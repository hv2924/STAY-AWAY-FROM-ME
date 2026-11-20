'use strict';
/* ============================================================================
   StayAwayFromMe — authoritative game server (single self-contained file)
   ----------------------------------------------------------------------------
   - 5 sector rooms (multi-room state loops) on ONE HTTP server
   - 30 Hz fixed-tick physics driven by process.hrtime.bigint() (monotonic)
   - 6000x6000 arena, 3-ring hazard map, spatial hash grid (500u cells)
   - exact circle / swept-segment / rounded-rect collision geometry
   - interest-managed snapshots (fog-of-war culling ~2800x2000 box)
   - hiding sockets, coin denomination merging, Watcher Gaze event
   - anti-cheat: server-authoritative movement, one session per IP via
     token-cookie handshake, input validation, 60 pps rate limit,
     45s unresponsive disconnect, nickname XSS stripping (15 chars)
   Run:  npm install ws && node server.js
   ============================================================================ */

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

/* ------------------------------- constants ------------------------------- */
const PORT = process.env.PORT || 3000;
const TICK_HZ = 30;
const TICK_MS = 1000 / TICK_HZ;
const WORLD = { cx: 3000, cy: 3000, arenaR: 2900 };       // 6000x6000 map
const ZONE_CORE_R = 950, ZONE_MID_R = 1950;               // ring boundaries
const R_MIN = 22, R_MAX = 115, SCORE_R_CAP = 2500;
const SPEED = 230;                                        // uniform for everyone
const LETHAL = 0.88, PICKUP = 1.08;                      // forgiving hitbox
const SPAWN_GHOST = 3.0, EXIT_GHOST = 1.0;
const HIDE_MAX = 4.0, HIDE_WARN = 3.5, HIDE_LEAK_EVERY = 0.25, HIDE_CD = 5.0;
const VIEW_HW = 1400, VIEW_HH = 1000;                     // interest box (half)
const CELL = 500, GRID_N = Math.ceil(6000 / CELL);        // 12 x 12 grid
const COIN_LIFE = 20, DEATH_DROP = 0.8, DROP_MAX = 45;
const DENOMS = [500, 100, 25, 5, 1];
const SHED_THRESHOLD = 1500, SHED_EVERY = 4;
const GAZE_EVERY = 180, GAZE_DUR = 15;
const GAZE_FIRST = Number.parseFloat(process.env.SAFM_TEST_GAZE_AT) > 0
  ? Number.parseFloat(process.env.SAFM_TEST_GAZE_AT) : GAZE_EVERY;
const RATE_LIMIT = 60;            // packets / second before disconnect
const UNRESPONSIVE_MS = 45000;    // zero input changes -> disconnect
const HELLO_TIMEOUT = 10000;
const CRUSH = { open: 2.2, warn: 1.0, slam: 0.8, retract: 0.8, period: 4.8,
                openGap: 190, closedGap: 15, snap: 0.12, hx: 125, hy: 105, cr: 26 };
const POP = { warn: 1.0, up: 1.2, ret: 0.3 };
const SECTORS = [
  { id: 1, name: 'SECTOR-01', label: 'Low Pop / Solo Practice', cap: 28 },
  { id: 2, name: 'SECTOR-02', label: 'Standard',               cap: 28 },
  { id: 3, name: 'SECTOR-03', label: 'Standard',               cap: 28 },
  { id: 4, name: 'SECTOR-04', label: 'High Activity',          cap: 40 },
  { id: 5, name: 'SECTOR-05', label: 'Overflow',               cap: 40 },
];
const COIN_TARGETS = { 1: 90, 2: 75, 3: 55 };
const COIN_INTERVAL = { 1: 9, 2: 6, 3: 2.5 };

/* ------------------------------ math helpers ----------------------------- */
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const clamp = (v, a, b) => v < a ? a : (v > b ? b : v);
const lerp = (a, b, k) => a + (b - a) * k;
function na(a) { while (a > Math.PI) a -= 2 * Math.PI; while (a < -Math.PI) a += 2 * Math.PI; return a; }
function turnRateFor(r) { return 3.9 * Math.sqrt(R_MIN / Math.max(r, R_MIN)); }
function radiusFor(score) {
  const s = clamp(score, 0, SCORE_R_CAP);
  return R_MIN + (R_MAX - R_MIN) * Math.sqrt(s / SCORE_R_CAP);   // diminishing returns
}
function coinR(v) {
  if (v >= 500) return 16;
  if (v >= 100) return 14;
  if (v >= 25) return 12;
  if (v >= 10) return 11;
  if (v >= 5) return 10;
  if (v >= 3) return 8.5;
  return 7;
}
/* exact circle vs rounded-rectangle (clamping method) */
function circleRectHit(px, py, r, rx, ry, hx, hy, cr) {
  const bx = Math.max(-(hx - cr), Math.min(hx - cr, px - rx));
  const by = Math.max(-(hy - cr), Math.min(hy - cr, py - ry));
  const dx = (px - rx) - bx, dy = (py - ry) - by;
  const rr = r + cr;
  return dx * dx + dy * dy < rr * rr;
}
/* exact circle vs line-segment squared distance */
function segDist2(px, py, x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const l2 = dx * dx + dy * dy;
  let t = l2 > 0 ? ((px - x1) * dx + (py - y1) * dy) / l2 : 0;
  t = clamp(t, 0, 1);
  const ex = px - (x1 + t * dx), ey = py - (y1 + t * dy);
  return ex * ex + ey * ey;
}
/* crusher cycle: 2.2 open / 1.0 warn / 0.8 slam / 0.8 retract */
function crushPhaseAt(time, ph0) {
  const c = (((time + ph0) % CRUSH.period) + CRUSH.period) % CRUSH.period;
  if (c < CRUSH.open) return { ph: 0, f: c / CRUSH.open };
  if (c < CRUSH.open + CRUSH.warn) return { ph: 1, f: (c - CRUSH.open) / CRUSH.warn };
  if (c < CRUSH.open + CRUSH.warn + CRUSH.slam) return { ph: 2, f: (c - CRUSH.open - CRUSH.warn) / CRUSH.slam };
  return { ph: 3, f: (c - CRUSH.open - CRUSH.warn - CRUSH.slam) / CRUSH.retract };
}
function crushGapHalf(ph, f) {
  if (ph === 0) return CRUSH.openGap;
  if (ph === 1) return CRUSH.openGap + Math.sin(f * 34) * 4;            // rattle
  if (ph === 2) {                                                        // snap shut
    const k = Math.min(1, f / CRUSH.snap);
    return lerp(CRUSH.openGap, CRUSH.closedGap, k * k);
  }
  const k = f * f * (3 - 2 * f);                                          // retract
  return lerp(CRUSH.closedGap, CRUSH.openGap, k);
}
/* pop-up spike cycle: hidden(h) / warn 1.0 / up 1.2 / retract 0.3 */
function popPhaseAt(time, u) {
  const P = u.period;
  const c = (((time + u.ph0) % P) + P) % P;
  if (c < u.hid) return { ph: 0, f: c / u.hid };
  if (c < u.hid + POP.warn) return { ph: 1, f: (c - u.hid) / POP.warn };
  if (c < u.hid + POP.warn + POP.up) return { ph: 2, f: (c - u.hid - POP.warn) / POP.up };
  return { ph: 3, f: (c - u.hid - POP.warn - POP.up) / POP.ret };
}
function pendTheta(time, u) { return u.rest + u.amp * Math.sin(u.om * time + u.ph); }
function sanitizeName(raw) {
  let s = String(raw == null ? '' : raw);
  s = s.replace(/[<>&"']/g, '').replace(/[\u0000-\u001f\u007f]/g, '');
  s = s.replace(/\s+/g, ' ').trim();
  if (s.length > 15) s = s.slice(0, 15);
  return s || ('SUBJECT-' + (1000 + ((Math.random() * 9000) | 0)));
}
function zoneOf(x, y) {
  const d = Math.hypot(x - WORLD.cx, y - WORLD.cy);
  return d < ZONE_CORE_R ? 3 : (d < ZONE_MID_R ? 2 : 1);
}

/* ============================== ROOM ==================================== */
class Room {
  constructor(sector) {
    this.sectorId = sector.id;
    this.name = sector.name;
    this.label = sector.label;
    this.cap = sector.cap;
    this.seed = (sector.id * 2654435761 ^ (Date.now() & 0xffff)) >>> 0;
    this.time = 0;
    this.tickCount = 0;
    this.nextPid = 1;
    this.nextCoinId = 1;
    this.players = new Map();
    this.coins = new Map();
    this.zoneCoins = { 1: 0, 2: 0, 3: 0 };
    this.spawnT = { 1: 0, 2: 0, 3: 0 };
    this.events = [];
    this.targeted = new Map();
    this.gazeActive = false;
    this.gazeNext = GAZE_FIRST;
    this.gazeEnd = 0;
    this.sparkT = new Map();
    this.lbRows = [];
    this.rank1Id = 0;
    this.rankById = new Map();
    this.genMap();
  }

  /* -------------------------- spatial hash grid -------------------------- */
  cellOf(x, y) {
    const i = clamp(Math.floor(x / CELL), 0, GRID_N - 1);
    const j = clamp(Math.floor(y / CELL), 0, GRID_N - 1);
    return i * GRID_N + j;
  }
  registerStatic(o, boundR) {
    const i0 = clamp(Math.floor((o.x - boundR) / CELL), 0, GRID_N - 1);
    const i1 = clamp(Math.floor((o.x + boundR) / CELL), 0, GRID_N - 1);
    const j0 = clamp(Math.floor((o.y - boundR) / CELL), 0, GRID_N - 1);
    const j1 = clamp(Math.floor((o.y + boundR) / CELL), 0, GRID_N - 1);
    for (let i = i0; i <= i1; i++)
      for (let j = j0; j <= j1; j++)
        this.staticCells[i * GRID_N + j].push(o);
  }
  coinCellAdd(c) {
    const idx = this.cellOf(c.x, c.y);
    let set = this.coinCells.get(idx);
    if (!set) { set = new Set(); this.coinCells.set(idx, set); }
    set.add(c.id);
    c.cellIdx = idx;
  }
  coinCellRemove(c) {
    const set = this.coinCells.get(c.cellIdx);
    if (set) set.delete(c.id);
  }
  coinCellMove(c) {
    const idx = this.cellOf(c.x, c.y);
    if (idx !== c.cellIdx) { this.coinCellRemove(c); this.coinCells.get(idx).add(c.id); c.cellIdx = idx; }
  }

  /* ----------------------------- map generation --------------------------- */
  genMap() {
    const rng = mulberry32(this.seed);
    const R = (a, b) => a + rng() * (b - a);
    const ringPos = (rMin, rMax) => {
      const ang = rng() * Math.PI * 2, rr = R(rMin, rMax);
      return [WORLD.cx + Math.cos(ang) * rr, WORLD.cy + Math.sin(ang) * rr];
    };
    const farFrom = (x, y, list, sep) => {
      for (const o of list) { if (Math.hypot(x - o.x, y - o.y) < sep) return false; }
      return true;
    };
    const placedPts = [];                     /* every placed anchor, for mutual separation */
    const placeSep = (rMin, rMax, sep, others, otherSep) => {
      for (let tries = 0; tries < 300; tries++) {
        const [x, y] = ringPos(rMin, rMax);
        if (!farFrom(x, y, placedPts, sep)) continue;
        if (others && otherSep && !farFrom(x, y, others, otherSep)) continue;
        placedPts.push({ x, y });
        return { x, y };
      }
      const [x, y] = ringPos(rMin, rMax);
      placedPts.push({ x, y });
      return { x, y };
    };

    this.pillars = [];   // Zone 1 — static spike pillars
    for (let i = 0; i < 26; i++) {
      const p = placeSep(2020, 2840, 420);
      this.pillars.push({ x: p.x, y: p.y, hx: R(42, 66), hy: R(42, 66), cr: 16, kind: 'pillar' });
    }
    this.lava = [];      // Zone 2 — lava holes
    for (let i = 0; i < 10; i++) {
      const p = placeSep(1030, 1870, 430);
      this.lava.push({ x: p.x, y: p.y, r: R(92, 128), kind: 'lava' });
    }
    this.pend = [];      // Zone 2 — swinging knives (pendulums)
    for (let i = 0; i < 8; i++) {
      const p = placeSep(1150, 1780, 520, this.lava, 300);
      const len = R(260, 380);
      this.pend.push({
        id: i + 1, px: p.x, py: p.y, len, rest: R(0, Math.PI * 2),
        amp: R(0.85, 1.3), om: Math.PI * 2 / R(3.6, 5.6), ph: R(0, Math.PI * 2),
        kind: 'pend', x: p.x, y: p.y
      });
    }
    this.crush = [];    // Zone 3 — hydraulic crushers (3 radial corridors)
    for (let i = 0; i < 3; i++) {
      const theta = i * 2.0944 + R(-0.18, 0.18);
      const rr = R(560, 760);
      const cx = WORLD.cx + Math.cos(theta) * rr, cy = WORLD.cy + Math.sin(theta) * rr;
      this.crush.push({ id: i + 1, cx, cy, hor: Math.abs(Math.sin(theta)) > 0.7, ph0: R(0, CRUSH.period), kind: 'crush', x: cx, y: cy });
      placedPts.push({ x: cx, y: cy });
    }
    this.pop = [];      // Zone 3 — pop-up floor spikes
    for (let i = 0; i < 10; i++) {
      const p = placeSep(160, 870, 270, this.crush, 340);
      const hid = R(2.4, 4.4);
      this.pop.push({ id: i + 1, x: p.x, y: p.y, r: R(52, 64), hid, ph0: R(0, hid), period: hid + POP.warn + POP.up + POP.ret, kind: 'pop' });
    }
    this.sockets = [];  // hiding sockets: 2 mega core / 12 medium mid / 9 medium + 20 small outer
    for (let i = 0; i < 2; i++) {
      const p = placeSep(640, 840, 900, this.crush, 360);
      this.sockets.push({ id: this.sockets.length + 1, x: p.x, y: p.y, tier: 2, innerR: 136, outerR: 178, occ: null });
    }
    const mkSockets = (n, rMin, rMax, tier, innerR, outerR, sep) => {
      const others = [].concat(this.pillars, this.lava, this.pend, this.crush);
      for (let i = 0; i < n; i++) {
        const p = placeSep(rMin, rMax, sep, others, 340);
        this.sockets.push({ id: this.sockets.length + 1, x: p.x, y: p.y, tier, innerR, outerR, occ: null });
      }
    };
    mkSockets(12, 1000, 1900, 1, 82, 120, 400);        // Zone 2 medium
    mkSockets(9, 2020, 2830, 1, 82, 120, 400);          // Zone 1 medium
    mkSockets(20, 2020, 2830, 0, 46, 72, 300);          // Zone 1 small

    /* static grid registration (hazards + sockets) */
    this.staticCells = Array.from({ length: GRID_N * GRID_N }, () => []);
    this.playerBuckets = Array.from({ length: GRID_N * GRID_N }, () => []);
    this.coinCells = new Map();
    for (const o of this.pillars) this.registerStatic(o, Math.max(o.hx, o.hy) + o.cr + 4);
    for (const o of this.lava) this.registerStatic(o, o.r + 4);
    for (const o of this.pend) this.registerStatic(o, o.len + 30);
    for (const o of this.crush) this.registerStatic(o, CRUSH.openGap + CRUSH.hx + CRUSH.hy + 20);
    for (const o of this.pop) this.registerStatic(o, o.r + 12);
    for (const o of this.sockets) this.registerStatic({ ...o, kind: 'socket' }, o.outerR + 6);

    /* initial coin fill */
    for (const z of [1, 2, 3]) {
      let guard = 0;
      while (this.zoneCoins[z] < COIN_TARGETS[z] && guard++ < 400) this.trySpawnZoneCoin(z, mulberry32(this.seed + z * 977 + guard));
    }

    /* immutable map payload for the client */
    this.mapP = {
      arenaR: WORLD.arenaR, cx: WORLD.cx, cy: WORLD.cy, zones: [ZONE_CORE_R, ZONE_MID_R],
      sockets: this.sockets.map(s => [s.id, Math.round(s.x), Math.round(s.y), s.innerR, s.outerR, s.tier]),
      pillars: this.pillars.map(p => [Math.round(p.x), Math.round(p.y), p.hx, p.hy, p.cr]),
      lava: this.lava.map(l => [Math.round(l.x), Math.round(l.y), Math.round(l.r)]),
      pend: this.pend.map(p => [p.id, Math.round(p.px), Math.round(p.py), Math.round(p.len), +p.amp.toFixed(3), +p.om.toFixed(4), +p.rest.toFixed(3), +p.ph.toFixed(3)]),
      crush: this.crush.map(c => [c.id, Math.round(c.cx), Math.round(c.cy), c.hor ? 1 : 0, +c.ph0.toFixed(3)]),
      pop: this.pop.map(p => [p.id, Math.round(p.x), Math.round(p.y), Math.round(p.r), +p.hid.toFixed(2), +p.ph0.toFixed(2), +p.period.toFixed(2)])
    };
  }

  /* ------------------------------ coins ---------------------------------- */
  coinSpotValid(x, y, z) {
    if (Math.hypot(x - WORLD.cx, y - WORLD.cy) > 2850) return false;
    if (zoneOf(x, y) !== z) return false;
    for (const p of this.pillars) if (Math.hypot(x - p.x, y - p.y) < Math.max(p.hx, p.hy) + 30) return false;
    for (const l of this.lava) if (Math.hypot(x - l.x, y - l.y) < l.r + 25) return false;
    for (const s of this.sockets) if (Math.hypot(x - s.x, y - s.y) < s.innerR + 12) return false;
    for (const c of this.crush) if (Math.hypot(x - c.cx, y - c.cy) < 430) return false;
    for (const p of this.pop) if (Math.hypot(x - p.x, y - p.y) < p.r + 18) return false;
    return true;
  }
  spawnCoin(x, y, v, zone, vx, vy, drop) {
    const c = { id: this.nextCoinId++, x, y, v, r: coinR(v), zone, born: drop ? this.time : -1, drop: !!drop, vx: vx || 0, vy: vy || 0, cellIdx: -1 };
    this.coins.set(c.id, c);
    this.zoneCoins[zone]++;
    this.coinCellAdd(c);
    if (this.coins.size > 800) this.trimCoins();
    return c;
  }
  removeCoin(id) {
    const c = this.coins.get(id);
    if (!c) return;
    this.zoneCoins[c.zone]--;
    this.coinCellRemove(c);
    this.coins.delete(id);
  }
  trimCoins() {           // safety valve: drops first, then newest coins (map anchors stay)
    if (this.coins.size <= 800) return;
    const arr = Array.from(this.coins.values());
    const drops = arr.filter(c => c.drop);
    const naturals = arr.filter(c => !c.drop).reverse();
    let excess = this.coins.size - 780;
    for (const c of [...drops, ...naturals]) {
      if (excess-- <= 0) break;
      this.removeCoin(c.id);
    }
  }
  trySpawnZoneCoin(z, rngIn) {
    const rnd = rngIn || Math.random;
    for (let tries = 0; tries < 24; tries++) {
      let x, y, v;
      if (z === 3) {
        if (rnd() < 0.18) { this.spawnCluster(rnd); return; }
        v = this.gazeActive ? 10 : 5;
        const ang = rnd() * Math.PI * 2, rr = Math.sqrt(rnd()) * 900;
        x = WORLD.cx + Math.cos(ang) * rr; y = WORLD.cy + Math.sin(ang) * rr;
      } else if (z === 2) {
        v = rnd() < 0.3 ? 3 : 1;
        if (rnd() < 0.6) {                       // weighted temptingly near hazards
          let hx, hy, hr;
          if (rnd() < 0.55 && this.lava.length) { const l = this.lava[(rnd() * this.lava.length) | 0]; hx = l.x; hy = l.y; hr = l.r; }
          else if (this.pend.length) { const p = this.pend[(rnd() * this.pend.length) | 0]; hx = p.px; hy = p.py; hr = p.len; }
          const ang = rnd() * Math.PI * 2, dd = hr + 60 + rnd() * 170;
          x = hx + Math.cos(ang) * dd; y = hy + Math.sin(ang) * dd;
        } else {
          const ang = rnd() * Math.PI * 2, rr = 990 + rnd() * 920;
          x = WORLD.cx + Math.cos(ang) * rr; y = WORLD.cy + Math.sin(ang) * rr;
        }
      } else {
        v = 1;
        const ang = rnd() * Math.PI * 2, rr = 1990 + rnd() * 870;
        x = WORLD.cx + Math.cos(ang) * rr; y = WORLD.cy + Math.sin(ang) * rr;
      }
      if (this.coinSpotValid(x, y, z)) { this.spawnCoin(x, y, v, z, 0, 0); return; }
    }
  }
  spawnCluster(rnd) {      // dense gold cluster in the Vault (never overshoots the target)
    const remaining = Math.max(1, Math.min(6, COIN_TARGETS[3] - this.zoneCoins[3]));
    for (let tries = 0; tries < 16; tries++) {
      const ang = rnd() * Math.PI * 2, rr = 60 + Math.sqrt(rnd()) * 800;
      const cx = WORLD.cx + Math.cos(ang) * rr, cy = WORLD.cy + Math.sin(ang) * rr;
      if (!this.coinSpotValid(cx, cy, 3)) continue;
      const v = this.gazeActive ? 10 : 5;
      for (let i = 0; i < remaining; i++) {
        const a = (i / remaining) * Math.PI * 2 + rnd() * 0.5, d = 34 + rnd() * 26;
        const x = cx + Math.cos(a) * d, y = cy + Math.sin(a) * d;
        if (this.coinSpotValid(x, y, 3)) this.spawnCoin(x, y, v, 3, 0, 0);
      }
      return;
    }
  }
  dropDeathCoins(x, y, score) {    // denomination merging, max 45 entities
    let gold = Math.floor(score * DEATH_DROP);
    if (gold < 1) return;
    const vals = [];
    for (const d of DENOMS)
      while (gold >= d && vals.length < DROP_MAX - 1) { vals.push(d); gold -= d; }
    if (gold > 0) {
      if (vals.length < DROP_MAX) vals.push(gold);
      else vals[vals.length - 1] += gold;
    }
    const base = Math.random() * Math.PI * 2, n = vals.length;
    const z = zoneOf(x, y);
    vals.forEach((v, i) => {
      const a = base + (i / n) * Math.PI * 2 + (Math.random() - 0.5) * 0.4;
      const sp = 150 + Math.random() * 110;
      this.spawnCoin(x + Math.cos(a) * (10 + Math.random() * 8), y + Math.sin(a) * (10 + Math.random() * 8),
        v, z, Math.cos(a) * sp, Math.sin(a) * sp, true);
    });
  }

  /* ------------------------------ sockets -------------------------------- */
  targetedEv(pid, ev) {
    const arr = this.targeted.get(pid) || [];
    arr.push(ev);
    this.targeted.set(pid, arr);
  }
  toggleHide(p) {
    if (p.dead) return;
    const t = this.time;
    if (p.hidden) { this.exitSocket(p, 'manual'); return; }
    if (t < p.ghostUntil) { this.targetedEv(p.id, { k: 'reject', why: 'ghost' }); return; }
    if (t < p.cooldownUntil) { this.targetedEv(p.id, { k: 'reject', why: 'cooldown' }); return; }
    let s = null, best = Infinity;
    for (const sock of this.sockets) {
      const d = Math.hypot(p.x - sock.x, p.y - sock.y);
      if (d < sock.innerR + p.r * 0.5 && d < best) { best = d; s = sock; }
    }
    if (!s) return;
    if (this.gazeActive || s.occ) { this.targetedEv(p.id, { k: 'reject', sid: s.id, why: 'occupied' }); return; }
    if (p.r >= s.innerR) { this.targetedEv(p.id, { k: 'reject', sid: s.id, why: 'size' }); return; }
    /* enter */
    p.hidden = true; p.hideSocketId = s.id; p.hideT = 0; p.leakAcc = 0;
    s.occ = p.id;
    p.x = s.x; p.y = s.y;
    this.targetedEv(p.id, { k: 'enter', sid: s.id });
  }
  exitSocket(p, reason) {
    const s = this.sockets.find(q => q.id === p.hideSocketId);
    if (s && s.occ === p.id) s.occ = null;
    p.hidden = false; p.hideSocketId = 0; p.hideT = 0; p.leakAcc = 0;
    p.ghostUntil = this.time + EXIT_GHOST;       // 1.0s intangible anti-camping buffer
    p.cooldownUntil = this.time + HIDE_CD;       // 5.0s global re-entry cooldown
    if (s) {
      const out = Math.max(10, s.innerR * 0.5);
      p.x = s.x + Math.cos(p.a) * out;
      p.y = s.y + Math.sin(p.a) * out;
    }
    this.targetedEv(p.id, { k: reason === 'manual' ? 'exit' : 'eject', why: reason });
  }

  /* ------------------------------ players -------------------------------- */
  safeSpawnPos() {
    let pos = null;
    for (let tries = 0; tries < 60; tries++) {
      const ang = Math.random() * Math.PI * 2, rr = 2000 + Math.random() * 700;
      const x = WORLD.cx + Math.cos(ang) * rr, y = WORLD.cy + Math.sin(ang) * rr;
      let ok = true;
      for (const q of this.players.values()) if (Math.hypot(x - q.x, y - q.y) < 350) { ok = false; break; }
      if (ok) for (const p of this.pillars) if (Math.hypot(x - p.x, y - p.y) < Math.max(p.hx, p.hy) + 350) { ok = false; break; }
      if (ok) for (const s of this.sockets) if (Math.hypot(x - s.x, y - s.y) < 240) { ok = false; break; }
      if (ok) for (const pd of this.pend) if (Math.hypot(x - pd.px, y - pd.py) < pd.len + 350) { ok = false; break; }
      if (ok) for (const c of this.crush) if (Math.hypot(x - c.cx, y - c.cy) < 600) { ok = false; break; }
      pos = { x, y };
      if (ok) break;
    }
    pos.a = Math.atan2(WORLD.cy - pos.y, WORLD.cx - pos.x) + (Math.random() - 0.5) * 1.2;
    return pos;
  }
  removePlayerById(pid) {
    const p = this.players.get(pid);
    if (p) { this.players.delete(pid); this.pushEvent({ k: 'gone', id: pid }); }
  }
  killPlayer(p, cause) {
    if (p.dead) return;
    p.dead = true;
    this.dropDeathCoins(p.x, p.y, p.score);
    this.players.delete(p.id);
    this.pushEvent({ k: 'poof', x: Math.round(p.x), y: Math.round(p.y), r: Math.round(p.r) });
    this.pushEvent({ k: 'gone', id: p.id });
    const stats = {
      t: 'died', cause,
      ms: Math.round((this.time - p.spawnT) * 1000),
      peak: p.peak, gold: p.gold,
      closest: p.closest === Infinity ? null : Math.round(p.closest * 10) / 10
    };
    try { p.ws.send(JSON.stringify(stats)); } catch (e) {}
    console.log(`[${this.name}] #${p.id} ${p.name} — ${cause} (peak ${p.peak})`);
    setTimeout(() => { try { p.ws.close(4001, 'TERMINATED'); } catch (e) {} }, 150);
  }
  pushEvent(ev) { this.events.push(ev); }
  buildLB() {
    const arr = [];
    for (const p of this.players.values()) arr.push([p.id, p.name, p.score]);
    arr.sort((a, b) => b[2] - a[2] || a[0] - b[0]);
    this.lbRows = arr.slice(0, 10);
    this.rank1Id = arr.length ? arr[0][0] : 0;
    this.rankById = new Map();
    arr.forEach((r, i) => this.rankById.set(r[0], i + 1));
  }

  /* ------------------------------- main tick ------------------------------ */
  tick(dt) {
    this.time += dt;
    this.tickCount++;
    const t = this.time;

    /* --- Watcher Gaze global event --- */
    if (!this.gazeActive && t >= this.gazeNext) {
      this.gazeActive = true;
      this.gazeEnd = t + GAZE_DUR;
      this.pushEvent({ k: 'gaze', on: 1 });
      for (const s of this.sockets)
        if (s.occ) { const p = this.players.get(s.occ); if (p && p.hidden) this.exitSocket(p, 'gaze'); }
    } else if (this.gazeActive && t >= this.gazeEnd) {
      this.gazeActive = false;
      this.gazeNext = t + GAZE_EVERY;
      this.pushEvent({ k: 'gaze', on: 0 });
    }

    /* --- rebuild player buckets --- */
    for (const b of this.playerBuckets) b.length = 0;
    for (const p of this.players.values()) {
      if (p.hidden) { p.cellIdx = -1; continue; }
      p.cellIdx = this.cellOf(p.x, p.y);
      this.playerBuckets[p.cellIdx].push(p);
    }

    /* --- steering (size-based inertia) + uniform forward motion + wall --- */
    const deaths = [];
    for (const p of this.players.values()) {
      if (p.hidden) continue;
      const want = na(p.inputA - p.a);
      const mx = turnRateFor(p.r) * dt;
      p.a = na(p.a + clamp(want, -mx, mx));
      p.x += Math.cos(p.a) * SPEED * dt;
      p.y += Math.sin(p.a) * SPEED * dt;
      if (Math.hypot(p.x - WORLD.cx, p.y - WORLD.cy) > WORLD.arenaR - LETHAL * p.r)
        deaths.push({ p, cause: 'Shredded by the Perimeter' });
      /* top-tier passive gold shedding */
      if (p.score >= SHED_THRESHOLD) {
        p.shedT += dt;
        if (p.shedT >= SHED_EVERY) {
          p.shedT = 0;
          if (this.coins.size < 780)
            this.spawnCoin(p.x - Math.cos(p.a) * (p.r + 12), p.y - Math.sin(p.a) * (p.r + 12), 1, 3, 0, 0, true);
        }
      } else p.shedT = 0;
    }

    /* --- eyeball vs eyeball: mutual termination + close-call grazes --- */
    const pairSeen = new Set();
    for (const p of this.players.values()) {
      if (p.hidden || p.cellIdx < 0) continue;
      const ci = (p.cellIdx / GRID_N) | 0, cj = p.cellIdx % GRID_N;
      for (let di = -1; di <= 1; di++) for (let dj = -1; dj <= 1; dj++) {
        const i = ci + di, j = cj + dj;
        if (i < 0 || j < 0 || i >= GRID_N || j >= GRID_N) continue;
        for (const q of this.playerBuckets[i * GRID_N + j]) {
          if (q.id === p.id) continue;
          const key = p.id < q.id ? p.id * 100000 + q.id : q.id * 100000 + p.id;
          if (pairSeen.has(key)) continue;
          pairSeen.add(key);
          if (t < p.ghostUntil || t < q.ghostUntil) continue;
          const dx = p.x - q.x, dy = p.y - q.y, d2 = dx * dx + dy * dy;
          const lethal = LETHAL * (p.r + q.r);
          if (d2 < lethal * lethal) {
            deaths.push({ p, cause: 'Terminated by ' + q.name });
            deaths.push({ p: q, cause: 'Terminated by ' + p.name });
            continue;
          }
          const outer = 1.05 * (p.r + q.r);
          if (d2 < outer * outer) {
            const gap = Math.sqrt(d2) - (p.r + q.r);
            if (gap < p.closest) p.closest = gap;
            if (gap < q.closest) q.closest = gap;
            const last = this.sparkT.get(key);
            if (t - (last === undefined ? -1 : last) > 0.4) {
              this.sparkT.set(key, t);
              this.pushEvent({ k: 'spark', x: Math.round((p.x + q.x) / 2), y: Math.round((p.y + q.y) / 2) });
            }
          }
        }
      }
    }

    /* --- eyeball vs static hazards (spatial grid, exact geometry) --- */
    for (const p of this.players.values()) {
      if (p.hidden || t < p.ghostUntil || p.dead) continue;
      const ci0 = (p.cellIdx / GRID_N) | 0, cj0 = p.cellIdx % GRID_N;
      for (let di = -1; di <= 1; di++) for (let dj = -1; dj <= 1; dj++) {
        const i = ci0 + di, j = cj0 + dj;
        if (i < 0 || j < 0 || i >= GRID_N || j >= GRID_N) continue;
        for (const o of this.staticCells[i * GRID_N + j]) {
          if (p.dead) break;
          switch (o.kind) {
            case 'pillar':
              if (circleRectHit(p.x, p.y, LETHAL * p.r, o.x, o.y, o.hx, o.hy, o.cr))
                deaths.push({ p, cause: 'Impaled by a Spike Pillar' });
              break;
            case 'lava': {
              const rr = o.r + 0.35 * p.r;                    // edge-teetering grace
              const dx = p.x - o.x, dy = p.y - o.y;
              if (dx * dx + dy * dy < rr * rr) deaths.push({ p, cause: 'Claimed by Lava' });
            } break;
            case 'pend': {                                     // swept 3-substep capsule
              for (let k = 0; k < 3; k++) {
                const tk = t - dt + dt * (k + 1) / 3;
                const th = pendTheta(tk, o);
                const x1 = o.px + Math.cos(th) * o.len * 0.12, y1 = o.py + Math.sin(th) * o.len * 0.12;
                const x2 = o.px + Math.cos(th) * o.len, y2 = o.py + Math.sin(th) * o.len;
                const lr = LETHAL * p.r;
                if (segDist2(p.x, p.y, x1, y1, x2, y2) < lr * lr) { deaths.push({ p, cause: 'Sliced by the Pendulum' }); break; }
              }
            } break;
            case 'crush': {                                    // lethal only while slammed
              const ph = crushPhaseAt(t, o.ph0);
              if (ph.ph === 2) {
                const g = crushGapHalf(2, ph.f);
                const lx = o.hor ? o.cx - g - CRUSH.hx : o.cx;
                const ly = o.hor ? o.cy : o.cy - g - CRUSH.hy;
                const rx = o.hor ? o.cx + g + CRUSH.hx : o.cx;
                const ry = o.hor ? o.cy : o.cy + g + CRUSH.hy;
                const hx = o.hor ? CRUSH.hx : CRUSH.hy, hy = o.hor ? CRUSH.hy : CRUSH.hx;
                if (circleRectHit(p.x, p.y, LETHAL * p.r, lx, ly, hx, hy, CRUSH.cr) ||
                    circleRectHit(p.x, p.y, LETHAL * p.r, rx, ry, hx, hy, CRUSH.cr))
                  deaths.push({ p, cause: 'Crushed in The Vault' });
              }
            } break;
            case 'pop': {                                      // lethal only while extended
              const ph = popPhaseAt(t, o);
              if (ph.ph === 2) {
                const rr = o.r * 0.9 + LETHAL * p.r;
                const dx = p.x - o.x, dy = p.y - o.y;
                if (dx * dx + dy * dy < rr * rr) deaths.push({ p, cause: 'Skewered by the Vault Floor' });
              }
            } break;
          }
        }
        if (p.dead) break;
      }
      if (p.dead) continue;
    }

    /* --- process deaths (instant mutual termination + gold drops) --- */
    for (const d of deaths) if (!d.p.dead) this.killPlayer(d.p, d.cause);

    /* --- coin pickups (ghosts & hidden players cannot collect) --- */
    for (const p of this.players.values()) {
      if (p.hidden || t < p.ghostUntil || p.dead) continue;
      const ci0 = (p.cellIdx / GRID_N) | 0, cj0 = p.cellIdx % GRID_N;
      const taken = [];
      for (let di = -1; di <= 1; di++) for (let dj = -1; dj <= 1; dj++) {
        const i = ci0 + di, j = cj0 + dj;
        if (i < 0 || j < 0 || i >= GRID_N || j >= GRID_N) continue;
        const set = this.coinCells.get(i * GRID_N + j);
        if (!set) continue;
        for (const id of set) {
          const c = this.coins.get(id);
          if (!c) continue;
          const rr = PICKUP * p.r + c.r;
          const dx = p.x - c.x, dy = p.y - c.y;
          if (dx * dx + dy * dy < rr * rr) taken.push(c);
        }
      }
      for (const c of taken) {
        this.removeCoin(c.id);
        p.score += c.v;
        if (p.score > p.peak) p.peak = p.score;
        p.gold += c.v;
        p.r = radiusFor(p.score);
      }
    }

    /* --- socket occupancy: safe window, warning, mass-leak, force eject --- */
    for (const s of this.sockets) {
      if (!s.occ) continue;
      const p = this.players.get(s.occ);
      if (!p || !p.hidden || p.hideSocketId !== s.id) { s.occ = null; continue; }
      p.hideT += dt;
      if (p.hideT >= HIDE_MAX) {
        p.leakAcc += dt;
        while (p.leakAcc >= HIDE_LEAK_EVERY) {
          p.leakAcc -= HIDE_LEAK_EVERY;
          const d = Math.min(p.score, Math.max(2, Math.floor(p.score * 0.02)));
          if (d > 0) {
            p.score -= d;
            p.r = radiusFor(p.score);
            const ang = Math.random() * Math.PI * 2;
            const sp = 140 + Math.random() * 80;
            this.spawnCoin(s.x + Math.cos(ang) * (s.innerR + 14), s.y + Math.sin(ang) * (s.innerR + 14),
              d, zoneOf(s.x, s.y), Math.cos(ang) * sp, Math.sin(ang) * sp, true);
          }
        }
        if (p.score <= 0) this.exitSocket(p, 'mass');     // minimum base mass -> eject
      }
    }

    /* --- dropped-coin motion with friction; only DROPPED coins despawn after 20s --- */
    for (const c of this.coins.values()) {
      const sp = Math.hypot(c.vx, c.vy);
      if (sp > 6) {
        c.x += c.vx * dt; c.y += c.vy * dt;
        const damp = Math.exp(-2.8 * dt);
        c.vx *= damp; c.vy *= damp;
        this.coinCellMove(c);
      } else if (c.vx !== 0 || c.vy !== 0) { c.vx = 0; c.vy = 0; }
      if (c.drop && t - c.born > COIN_LIFE) this.removeCoin(c.id);
    }

    /* --- zone coin maintenance (Vault values double during Gaze; burst catch-up) --- */
    for (const z of [1, 2, 3]) {
      const deficit = COIN_TARGETS[z] - this.zoneCoins[z];
      if (deficit > 0 && t - this.spawnT[z] >= COIN_INTERVAL[z] && this.coins.size < 750) {
        this.spawnT[z] = t;
        const burst = Math.min(deficit, Math.max(1, Math.ceil(deficit / 8)));
        for (let n = 0; n < burst; n++) this.trySpawnZoneCoin(z);
      }
    }

    /* --- disconnect fully unresponsive clients (45s) --- */
    const nowMs = Date.now();
    for (const p of Array.from(this.players.values())) {
      if (nowMs - p.lastInputAt > UNRESPONSIVE_MS) {
        try { p.ws.send(JSON.stringify({ t: 'sys', msg: 'DISCONNECTED: SUBJECT UNRESPONSIVE' })); } catch (e) {}
        try { p.ws.close(4003, 'UNRESPONSIVE'); } catch (e) { try { p.ws.terminate(); } catch (e2) {} }
      }
    }

    /* --- build & send interest-managed snapshots --- */
    this.buildPackets();
  }

  buildPackets() {
    this.buildLB();
    const t = this.time, tm = Math.round(t * 1000), gz = this.gazeActive ? 1 : 0;
    const withLB = this.tickCount % 3 === 0;
    for (const p of this.players.values()) {
      if (p.ws.readyState !== 1) continue;
      if (p.ws.bufferedAmount > 5e6) { try { p.ws.terminate(); } catch (e) {} continue; }
      if (p.ws.bufferedAmount > 1e6) continue;            // lagging client: skip frame

      /* events (global + positional-in-box + targeted) */
      const ev = [];
      for (const e of this.events) {
        if (e.x === undefined || (Math.abs(e.x - p.x) <= VIEW_HW && Math.abs(e.y - p.y) <= VIEW_HH)) ev.push(e);
      }
      const tArr = this.targeted.get(p.id);
      if (tArr && tArr.length) { ev.push(...tArr); this.targeted.delete(p.id); }

      /* players in view (fog-of-war) */
      const pl = [];
      for (const q of this.players.values()) {
        if (q === p || q.hidden) continue;
        if (Math.abs(q.x - p.x) > VIEW_HW || Math.abs(q.y - p.y) > VIEW_HH) continue;
        pl.push([q.id, Math.round(q.x), Math.round(q.y), +q.a.toFixed(3), +q.r.toFixed(1),
                 q.color, q.pupil, (t < q.ghostUntil ? 1 : 0) + (q.id === this.rank1Id ? 2 : 0)]);
      }

      /* coin diffing (add / remove / moving) */
      const cA = [], cD = [], cM = [], vis = new Set();
      const ci0 = clamp(Math.floor((p.x - VIEW_HW) / CELL), 0, GRID_N - 1);
      const ci1 = clamp(Math.floor((p.x + VIEW_HW) / CELL), 0, GRID_N - 1);
      const cj0 = clamp(Math.floor((p.y - VIEW_HH) / CELL), 0, GRID_N - 1);
      const cj1 = clamp(Math.floor((p.y + VIEW_HH) / CELL), 0, GRID_N - 1);
      for (let i = ci0; i <= ci1; i++) for (let j = cj0; j <= cj1; j++) {
        const set = this.coinCells.get(i * GRID_N + j);
        if (!set) continue;
        for (const id of set) {
          const c = this.coins.get(id);
          if (!c) continue;
          if (Math.abs(c.x - p.x) > VIEW_HW || Math.abs(c.y - p.y) > VIEW_HH) continue;
          vis.add(id);
          if (!p.knownCoins.has(id)) {
            p.knownCoins.add(id);
            cA.push([c.id, Math.round(c.x), Math.round(c.y), c.v, c.drop ? Math.round(c.born * 1000) : -1]);
          }
          if (c.vx !== 0 || c.vy !== 0) cM.push([c.id, Math.round(c.x), Math.round(c.y)]);
        }
      }
      for (const id of p.knownCoins) if (!vis.has(id)) { cD.push(id); p.knownCoins.delete(id); }

      /* socket states in view */
      const so = [];
      for (const s of this.sockets) {
        if (Math.abs(s.x - p.x) > VIEW_HW || Math.abs(s.y - p.y) > VIEW_HH) continue;
        const st = this.gazeActive ? 2 : (s.occ ? 1 : 0);
        let w = 0, l = 0;
        if (s.occ) {
          const occ = this.players.get(s.occ);
          if (occ) { w = occ.hideT >= HIDE_WARN ? 1 : 0; l = occ.hideT >= HIDE_MAX ? 1 : 0; }
        }
        so.push([s.id, st, w, l]);
      }

      /* dynamic hazard states in view */
      const pe = [], cr = [], po = [];
      for (const o of this.pend) {
        if (Math.abs(o.px - p.x) > VIEW_HW || Math.abs(o.py - p.y) > VIEW_HH) continue;
        pe.push([o.id, +pendTheta(t, o).toFixed(4)]);
      }
      for (const o of this.crush) {
        if (Math.abs(o.cx - p.x) > VIEW_HW || Math.abs(o.cy - p.y) > VIEW_HH) continue;
        const ph = crushPhaseAt(t, o.ph0);
        cr.push([o.id, ph.ph, +ph.f.toFixed(3)]);
      }
      for (const o of this.pop) {
        if (Math.abs(o.x - p.x) > VIEW_HW || Math.abs(o.y - p.y) > VIEW_HH) continue;
        const ph = popPhaseAt(t, o);
        po.push([o.id, ph.ph, +ph.f.toFixed(3)]);
      }

      const you = {
        x: Math.round(p.x), y: Math.round(p.y), a: +p.a.toFixed(3), r: +p.r.toFixed(1), s: p.score,
        g: Math.max(0, Math.round((p.ghostUntil - t) * 1000)),
        h: p.hidden ? 1 : 0,
        ht: p.hidden ? Math.max(0, Math.round((HIDE_MAX - p.hideT) * 1000)) : 0,
        hc: Math.max(0, Math.round((p.cooldownUntil - t) * 1000)),
        hw: (p.hidden && p.hideT >= HIDE_WARN) ? 1 : 0
      };
      const pkt = { t: 'st', tm, gz, you, pl, cA, cD, cM, so, pe, cr, po, ev };
      if (withLB) { pkt.lb = this.lbRows; pkt.yr = this.rankById.get(p.id) || 0; }
      try { p.ws.send(JSON.stringify(pkt)); } catch (e) {}
    }
    this.events.length = 0;
  }
}

const rooms = SECTORS.map(s => new Room(s));

/* ===================== HTTP server + static serving ====================== */
let INDEX = '';
try { INDEX = fs.readFileSync(path.join(__dirname, 'index.html')); }
catch (e) { console.error('[fatal] index.html must sit next to server.js'); process.exit(1); }

function cookieToken(headers) {
  const h = headers && headers.cookie;
  if (!h) return null;
  const m = /(?:^|;\s*)safm_tok=([A-Za-z0-9]+)/.exec(h);
  return m ? m[1] : null;
}
function ipOf(req) {
  let ip = (req.socket && req.socket.remoteAddress) || 'unknown';
  ip = String(ip).replace(/^::ffff:/, '');
  if (ip === '::1') ip = '127.0.0.1';
  if (process.env.SAFM_TRUST_PROXY === '1') {              // only for explicit proxy deployments / tests
    const xf = req.headers['x-forwarded-for'];
    if (xf) { const first = String(xf).split(',')[0].trim(); if (first) ip = first.replace(/^::ffff:/, ''); }
  }
  return ip;
}

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (req.method !== 'GET' && req.method !== 'HEAD') { res.writeHead(405); res.end(); return; }
  if (url === '/' || url === '/index.html') {
    if (!cookieToken(req.headers)) {
      res.setHeader('Set-Cookie',
        `safm_tok=${crypto.randomBytes(16).toString('hex')}; Path=/; Max-Age=43200; SameSite=Lax; HttpOnly`);
    }
    res.setHeader('Content-Type', 'text/html; charset=utf-8');
    res.setHeader('Cache-Control', 'no-store');
    res.end(INDEX);
  } else if (url === '/api/servers') {
    res.setHeader('Content-Type', 'application/json');
    res.setHeader('Cache-Control', 'no-store');
    res.end(JSON.stringify({
      servers: rooms.map(r => ({ id: r.sectorId, name: r.name, label: r.label, players: r.players.size, cap: r.cap }))
    }));
  } else if (url === '/api/ping') {
    res.setHeader('Content-Type', 'text/plain');
    res.end('pong');
  } else {
    res.writeHead(404); res.end('not found');
  }
});

/* ====================== WebSocket cluster manager ======================== */
const wss = new WebSocketServer({ noServer: true, maxPayload: 512, perMessageDeflate: false });
const conns = new Map();                    // ws -> {ip, token, pkt, p, roomIdx}
const sessionsByIp = new Map();             // ip -> {ws, token, pid, roomIdx}

server.on('upgrade', (req, socket, head) => {
  const u = req.url || '';
  if (!u.startsWith('/ws')) { socket.destroy(); return; }
  wss.handleUpgrade(req, socket, head, ws => onConnection(req, ws));
});

function onConnection(req, ws) {
  const meta = { ip: ipOf(req), token: cookieToken(req.headers) || 'NOTOK', pkt: 0, p: null, roomIdx: -1 };
  conns.set(ws, meta);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });
  const helloTimer = setTimeout(() => { if (!meta.p) { try { ws.terminate(); } catch (e) {} } }, HELLO_TIMEOUT);
  ws.on('message', raw => {
    meta.pkt++;
    let msg;
    try { msg = JSON.parse(raw.toString('utf8')); } catch (e) { return; }
    if (!msg || typeof msg !== 'object') return;
    try { handleMessage(ws, meta, msg, helloTimer); } catch (e) { console.error('[ws msg]', e); }
  });
  ws.on('close', () => {
    clearTimeout(helloTimer);
    conns.delete(ws);
    onWsClosed(ws, meta);
  });
}

function handleMessage(ws, meta, msg, helloTimer) {
  if (msg.t === 'hello') {
    if (meta.p) return;
    const ip = meta.ip, token = meta.token;
    /* ---- strict same-device / multi-tab restriction (one session per IP) ---- */
    const ex = sessionsByIp.get(ip);
    if (ex && ex.ws !== ws) {
      if (ex.token === token) {
        /* same browser profile: refresh / duplicate tab — retire old session */
        try { ex.ws.close(4002, 'REPLACED'); } catch (e) { try { ex.ws.terminate(); } catch (e2) {} }
        if (sessionsByIp.get(ip) === ex) sessionsByIp.delete(ip);
        const rm = rooms[ex.roomIdx];
        if (rm && ex.pid) rm.removePlayerById(ex.pid);
      } else {
        try {
          ws.send(JSON.stringify({ t: 'rejected', msg: 'CONNECTION REJECTED: SUBJECT ALREADY OBSERVED ON THIS NETWORK' }));
          setTimeout(() => { try { ws.terminate(); } catch (e) {} }, 300);
        } catch (e) {}
        return;
      }
    }
    const sector = Math.min(5, Math.max(1, Math.round(Number(msg.sector) || 2)));
    const room = rooms[sector - 1];
    if (room.players.size >= room.cap) {
      try {
        ws.send(JSON.stringify({ t: 'rejected', msg: 'CONNECTION REJECTED: SECTOR AT MAXIMUM DENSITY' }));
        setTimeout(() => { try { ws.terminate(); } catch (e) {} }, 300);
      } catch (e) {}
      return;
    }
    const name = sanitizeName(msg.name);
    const color = Math.min(5, Math.max(0, Math.round(Number(msg.color) || 0)));
    const pupil = Math.min(2, Math.max(0, Math.round(Number(msg.pupil) || 0)));
    const pos = room.safeSpawnPos();
    const p = {
      id: room.nextPid++, ws, name, color, pupil,
      x: pos.x, y: pos.y, a: pos.a, inputA: pos.a,
      score: 0, peak: 0, gold: 0, closest: Infinity, r: R_MIN,
      hidden: false, hideSocketId: 0, hideT: 0, leakAcc: 0, hideKeyPrev: false,
      ghostUntil: room.time + SPAWN_GHOST, cooldownUntil: 0, shedT: 0,
      spawnT: room.time, dead: false, knownCoins: new Set(), cellIdx: -1,
      lastInputAt: Date.now(), roomIdx: sector - 1
    };
    room.players.set(p.id, p);
    meta.p = p; meta.roomIdx = sector - 1;
    sessionsByIp.set(ip, { ws, token, pid: p.id, roomIdx: sector - 1 });
    clearTimeout(helloTimer);
    const roster = [];
    for (const q of room.players.values()) if (q !== p) roster.push([q.id, q.name]);
    try {
      ws.send(JSON.stringify({
        t: 'welcome', id: p.id, name, roomName: room.name,
        tm: Math.round(room.time * 1000), seed: room.seed, roster,
        consts: {
          rMin: R_MIN, rMax: R_MAX, speed: SPEED, scoreCap: SCORE_R_CAP,
          areaBase: 1150000, areaGrow: 1.0,
          hideMax: HIDE_MAX, hideWarn: HIDE_WARN, hideCd: HIDE_CD,
          ghostSpawn: SPAWN_GHOST, ghostExit: EXIT_GHOST,
          coinLife: COIN_LIFE, lethal: LETHAL, pickup: PICKUP,
          gazeEvery: GAZE_EVERY, gazeDur: GAZE_DUR, tickMs: TICK_MS
        },
        map: room.mapP
      }));
    } catch (e) {}
    room.pushEvent({ k: 'join', id: p.id, name });
    console.log(`[${room.name}] join #${p.id} ${name} (${room.players.size}/${room.cap})`);
    return;
  }
  if (msg.t === 'input') {
    const p = meta.p;
    if (!p || p.dead) return;
    p.lastInputAt = Date.now();
    if (typeof msg.a === 'number' && Number.isFinite(msg.a)) p.inputA = na(msg.a);   // last angle persists on packet loss
    const h = msg.h === true;
    if (h && !p.hideKeyPrev) rooms[p.roomIdx].toggleHide(p);
    p.hideKeyPrev = h;
    return;
  }
  /* unknown types silently discarded (malformed packets never mutate state) */
}

function onWsClosed(ws, meta) {
  const e = sessionsByIp.get(meta.ip);
  if (e && e.ws === ws) sessionsByIp.delete(meta.ip);      // instant rejoin after tab close
  if (meta.p) {
    const room = rooms[meta.roomIdx];
    if (room && room.players.has(meta.p.id)) {
      console.log(`[${room.name}] left #${meta.p.id} ${meta.p.name}`);
      room.removePlayerById(meta.p.id);
    }
    meta.p = null;
  }
}

/* heartbeat + rate limiting */
setInterval(() => {
  for (const ws of conns.keys()) {
    if (ws.readyState !== 1) continue;
    if (!ws.isAlive) { try { ws.terminate(); } catch (e) {} continue; }
    ws.isAlive = false;
    try { ws.ping(); } catch (e) {}
  }
}, 10000);
setInterval(() => {
  for (const [ws, meta] of conns) {
    if (meta.pkt > RATE_LIMIT) {                       // > 60 packets/second -> disconnect
      try { ws.terminate(); } catch (e) {}
      if (meta.p) {
        const room = rooms[meta.roomIdx];
        if (room) room.removePlayerById(meta.p.id);
      }
    }
    meta.pkt = 0;
  }
}, 1000);

/* ------------------- fixed-tick loop (monotonic clock) ------------------- */
let last = process.hrtime.bigint();
setInterval(() => {
  const now = process.hrtime.bigint();
  let dt = Number(now - last) / 1e9;
  last = now;
  dt = Math.min(dt, 0.05);                              // clamp: no tunneling through GC pauses
  for (const room of rooms) {
    try { room.tick(dt); } catch (e) { console.error('[tick ' + room.name + ']', e); }
  }
}, TICK_MS);

/* ------------------------------- boot ------------------------------------ */
process.on('uncaughtException', e => console.error('[uncaught]', e));
server.listen(PORT, () => {
  console.log('------------------------------------------------------------');
  console.log(' STAYAWAYFROMME — the walls have eyes');
  console.log(' listening on http://localhost:' + PORT);
  console.log(' sectors: ' + rooms.map(r => `${r.name} [${r.label}] 0/${r.cap}`).join('  |  '));
  console.log('------------------------------------------------------------');
});

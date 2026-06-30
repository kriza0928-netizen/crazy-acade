const express = require('express');
const http = require('http');
const WebSocket = require('ws');
const os = require('os');
const path = require('path');

const app = express();
const server = http.createServer(app);
const wss = new WebSocket.Server({ server });

app.use(express.static(path.join(__dirname, 'public')));
app.use('/sprites', express.static(path.join(__dirname, 'Minerman-Adventure 복사본')));

function getLanIP() {
  const ifaces = os.networkInterfaces();
  for (const name of Object.keys(ifaces)) {
    for (const iface of ifaces[name]) {
      if (iface.family === 'IPv4' && !iface.internal) return iface.address;
    }
  }
  return 'localhost';
}

// =============================================
// Constants
// =============================================
const COLS = 15, ROWS = 13, TILE = 44;
const T_EMPTY = 0, T_WALL = 1, T_BOX = 2;
const EXPLODE_DURATION = 500, BALLOON_DELAY = 3000;
const PLAYER_SPEED = 5;
const TRAP_DURATION = 7000;
const ESCAPE_NEEDED = 20;
const BALLOON_CD = 200;

// =============================================
// Session state
// =============================================
// clients: [{ws, playerIdx, isMobile}]  playerIdx=-1 until claimed
let clients = [];
// slots[0] and slots[1]: which client holds that player slot (or null)
let slots = [null, null];
let gs = null;
// inputs[playerIdx] = {up, down, left, right, bomb}
let inputs = [
  { up: false, down: false, left: false, right: false, bomb: false },
  { up: false, down: false, left: false, right: false, bomb: false },
];
// previous inputs for edge detection (escape counting)
let prevInputs = [
  { up: false, down: false, left: false, right: false, bomb: false },
  { up: false, down: false, left: false, right: false, bomb: false },
];
let lastBalloon = [0, 0];
let localMode = false; // true when single PC holds both slots

// =============================================
// Map generation
// =============================================
function buildRacingMap() {
  const map = Array.from({length: ROWS}, () => Array(COLS).fill(T_EMPTY));
  // 외곽 벽
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (r===0 || r===ROWS-1 || c===0 || c===COLS-1) map[r][c] = T_WALL;
  // 내부 섬 (트랙 안쪽)
  for (let r = 3; r <= 9; r++)
    for (let c = 4; c <= 10; c++)
      map[r][c] = T_WALL;
  // 트랙 위에 박스 (스폰/연료소 주변 제외)
  const safe = [[1,1],[1,2],[2,1],[11,13],[11,12],[10,13],[1,7],[11,7]];
  const isSafe = (r,c) => safe.some(([sr,sc])=>sr===r&&sc===c);
  for (let r = 1; r < ROWS-1; r++)
    for (let c = 1; c < COLS-1; c++)
      if (map[r][c]===T_EMPTY && !isSafe(r,c) && Math.random()<0.30)
        map[r][c] = T_BOX;
  return map;
}

function buildMap() {
  const map = [];
  for (let r = 0; r < ROWS; r++) {
    map.push([]);
    for (let c = 0; c < COLS; c++) {
      if (r === 0 || r === ROWS - 1 || c === 0 || c === COLS - 1) map[r].push(T_WALL);
      else if (r % 2 === 0 && c % 2 === 0) map[r].push(T_WALL);
      else map[r].push(T_EMPTY);
    }
  }
  const safe = [[1,1],[1,2],[2,1],[ROWS-2,COLS-2],[ROWS-2,COLS-3],[ROWS-3,COLS-2]];
  const isSafe = (r, c) => safe.some(([sr, sc]) => sr === r && sc === c);
  for (let r = 1; r < ROWS - 1; r++)
    for (let c = 1; c < COLS - 1; c++)
      if (map[r][c] === T_EMPTY && !isSafe(r, c) && Math.random() < 0.70)
        map[r][c] = T_BOX;
  return map;
}

// =============================================
// Tile helpers
// =============================================
const toTile = px => Math.floor(px / TILE);
const toCenter = t => t * TILE + TILE / 2;

// =============================================
// Collision
// =============================================
function isBlocked(x, y, ignoreIdx, extraWalls) {
  const mg = 3;
  const corners = [
    [x - TILE/2 + mg, y - TILE/2 + mg],
    [x + TILE/2 - mg, y - TILE/2 + mg],
    [x - TILE/2 + mg, y + TILE/2 - mg],
    [x + TILE/2 - mg, y + TILE/2 - mg],
  ];
  for (const [cx, cy] of corners) {
    const tc = toTile(cx), tr = toTile(cy);
    if (tr < 0 || tr >= ROWS || tc < 0 || tc >= COLS) return true;
    const tile = gs.map[tr][tc];
    if (tile === T_WALL || tile === T_BOX) return true;
    if (extraWalls && extraWalls.some(w => w.r === tr && w.c === tc)) return true;
    for (const b of gs.balloons) {
      if (b.playerIdx === ignoreIdx && b.passable) continue;
      if (b.r === tr && b.c === tc) return true;
    }
  }
  return false;
}

// =============================================
// Space map gimmick
// =============================================
function getSpaceWalls() {
  if (gs.mapId !== 'space' || gs.spaceWallLayer === 0) return [];
  const walls = [];
  const L = gs.spaceWallLayer;
  for (let r = 0; r < ROWS; r++) for (let c = 0; c < COLS; c++) {
    if (r < L || r >= ROWS - L || c < L || c >= COLS - L) {
      if (gs.map[r][c] !== T_WALL) walls.push({ r, c });
    }
  }
  return walls;
}

function isInDangerZone(r, c, layer) {
  return r < layer || r >= ROWS - layer || c < layer || c >= COLS - layer;
}

function updateDesertGimmick(now) {
  if (gs.mapId !== 'desert') return;
  const w = gs.desertWind;
  if (!w.active && now >= w.nextAt) {
    const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
    const [dx,dy] = dirs[Math.floor(Math.random()*4)];
    w.active = true; w.dx = dx; w.dy = dy;
    w.endAt = now + 3000;
  }
  if (w.active && now >= w.endAt) {
    w.active = false;
    w.nextAt = now + 8000;
  }
}

function updateMapGimmick(now) {
  updateDesertGimmick(now);
  if (gs.mapId !== 'space') return;
  if (gs.spacePhase >= 4) return;
  if (!gs.spaceDanger && now >= gs.spaceNextAt) {
    gs.spaceDanger = true;
    gs.spaceDangerAt = now + 3000;
  }
  if (gs.spaceDanger && now >= gs.spaceDangerAt) {
    gs.spaceDanger = false;
    gs.spacePhase++;
    gs.spaceWallLayer++;
    gs.spaceNextAt = now + 10000;
    for (const p of gs.players) {
      if (!p.alive) continue;
      if (isInDangerZone(toTile(p.y), toTile(p.x), gs.spaceWallLayer)) killPlayer(p);
    }
  }
}

// =============================================
// Movement
// =============================================
function movePlayerInput(p, ix, iy, idx, speed, isIce, dt) {
  if (!p.alive || p.trapped) return;
  const extraWalls = getSpaceWalls();

  if (isIce) {
    const accel = PLAYER_SPEED * TILE * 6;
    const friction = PLAYER_SPEED * TILE * 3.5;
    const maxV = PLAYER_SPEED * TILE * 1.5;
    if (ix !== 0) { p.vx += ix * accel * dt; p.vx = Math.max(-maxV, Math.min(maxV, p.vx)); }
    else { p.vx *= Math.max(0, 1 - friction * dt / Math.max(Math.abs(p.vx), 1) * 0.8); if (Math.abs(p.vx) < 2) p.vx = 0; }
    if (iy !== 0) { p.vy += iy * accel * dt; p.vy = Math.max(-maxV, Math.min(maxV, p.vy)); }
    else { p.vy *= Math.max(0, 1 - friction * dt / Math.max(Math.abs(p.vy), 1) * 0.8); if (Math.abs(p.vy) < 2) p.vy = 0; }
    const stepX = p.vx * dt, stepY = p.vy * dt;
    if (!isBlocked(p.x + stepX, p.y, idx, extraWalls)) p.x += stepX; else p.vx = 0;
    if (!isBlocked(p.x, p.y + stepY, idx, extraWalls)) p.y += stepY; else p.vy = 0;
  } else {
    // 하드 스냅: 이동 속도와 동일하게 중심으로 당김 (lerp보다 빠르고 정확)
    const SNAP_RANGE = TILE * 0.6;
    const snapAxis = (val, center) => {
      const d = center - val;
      return Math.abs(d) < SNAP_RANGE
        ? val + Math.sign(d) * Math.min(Math.abs(d), speed)
        : val;
    };

    if (ix !== 0 && iy !== 0) {
      if (!isBlocked(p.x + ix * speed, p.y, idx, extraWalls)) {
        p.x += ix * speed;
        p.y = snapAxis(p.y, toCenter(toTile(p.y)));
      } else if (!isBlocked(p.x, p.y + iy * speed, idx, extraWalls)) {
        p.y += iy * speed;
        p.x = snapAxis(p.x, toCenter(toTile(p.x)));
      }
    } else if (ix !== 0) {
      p.y = snapAxis(p.y, toCenter(toTile(p.y)));
      if (!isBlocked(p.x + ix * speed, p.y, idx, extraWalls)) p.x += ix * speed;
    } else if (iy !== 0) {
      p.x = snapAxis(p.x, toCenter(toTile(p.x)));
      if (!isBlocked(p.x, p.y + iy * speed, idx, extraWalls)) p.y += iy * speed;
    }
  }

  // 사막 바람
  if (gs.mapId === 'desert' && gs.desertWind && gs.desertWind.active) {
    const windSpeed = PLAYER_SPEED * TILE * dt * 0.7;
    const wx = gs.desertWind.dx * windSpeed;
    const wy = gs.desertWind.dy * windSpeed;
    if (!isBlocked(p.x + wx, p.y, idx, extraWalls)) p.x += wx;
    if (!isBlocked(p.x, p.y + wy, idx, extraWalls)) p.y += wy;
  }

  if (ix !== 0 || iy !== 0) {
    if (ix !== 0) p.facing = { x: ix, y: 0 };
    else p.facing = { x: 0, y: iy };
    p.walkCycle = (p.walkCycle || 0) + dt * 8;
    p.moving = true;
  } else {
    p.moving = false;
  }

  // Balloon passable: once player steps off their balloon tile, lock it
  const mg = 3;
  const corners = [
    [p.x - TILE/2 + mg, p.y - TILE/2 + mg],
    [p.x + TILE/2 - mg, p.y - TILE/2 + mg],
    [p.x - TILE/2 + mg, p.y + TILE/2 - mg],
    [p.x + TILE/2 - mg, p.y + TILE/2 - mg],
  ];
  for (const b of gs.balloons) {
    if (b.playerIdx === idx && b.passable) {
      const allOff = corners.every(([cx, cy]) => !(toTile(cx) === b.c && toTile(cy) === b.r));
      if (allOff) { b.passable = false; gs.mapDirty = true; }
    }
  }

  // Space danger zone
  if (gs.mapId === 'space' && gs.spaceWallLayer > 0) {
    if (isInDangerZone(toTile(p.y), toTile(p.x), gs.spaceWallLayer)) killPlayer(p);
  }

  // Item pickup
  const pr = toTile(p.y), pc = toTile(p.x);
  for (let i = gs.items.length - 1; i >= 0; i--) {
    const item = gs.items[i];
    if (item.r === pr && item.c === pc) {
      if (item.type === 'balloon_up') p.maxBalloons = Math.min(p.maxBalloons + 1, 5);
      else if (item.type === 'range_up') p.balloonRange = Math.min(p.balloonRange + 1, 7);
      gs.items.splice(i, 1);
    }
  }
}

// =============================================
// Input processing
// =============================================
function updateFuelStations(now) {
  if (!gs.fuelStations) return;
  for (const fs of gs.fuelStations) {
    if (!fs.active && now >= fs.rechargeAt) fs.active = true;
  }
}

function handleInputs(now, dt) {
  const isIce = gs.mapId === 'ice';

  for (let idx = 0; idx < 2; idx++) {
    const p = gs.players[idx];
    // 연료소 체크
    if (gs.mapId === 'racing' && gs.fuelStations) {
      const pr = Math.floor(p.y / TILE);
      const pc = Math.floor(p.x / TILE);
      for (const fs of gs.fuelStations) {
        if (fs.active && fs.r === pr && fs.c === pc) {
          p.boostEndAt = now + 4000;
          fs.active = false;
          fs.rechargeAt = now + 10000;
        }
      }
    }
  }

  const getSpeedMult = (p) => {
    if (gs.mapId === 'city') return 1.5;
    if (gs.mapId === 'racing' && p.boostEndAt && now < p.boostEndAt) return 2.0;
    return 1.0;
  };
  // speed는 루프 안에서 플레이어별로 계산
  const baseSpeed = PLAYER_SPEED * TILE * dt;

  for (let idx = 0; idx < 2; idx++) {
    const inp = inputs[idx];
    const prev = prevInputs[idx];
    const p = gs.players[idx];

    const ix = (inp.left ? -1 : 0) + (inp.right ? 1 : 0);
    const iy = (inp.up ? -1 : 0) + (inp.down ? 1 : 0);
    const speed = baseSpeed * getSpeedMult(p);
    movePlayerInput(p, ix, iy, idx, speed, isIce, dt);

    // Bomb placement on rising edge
    if (inp.bomb && !prev.bomb) {
      if (now - lastBalloon[idx] > BALLOON_CD) {
        placeBalloon(idx, now);
        lastBalloon[idx] = now;
      }
    }

    // Escape: count key-down edges (any direction or bomb)
    if (p.trapped) {
      const keys = ['up', 'down', 'left', 'right', 'bomb'];
      for (const k of keys) {
        if (inp[k] && !prev[k]) p.escapeCount++;
      }
    }

    // Save previous
    prevInputs[idx] = { ...inp };
  }
}

// =============================================
// Balloons
// =============================================
function placeBalloon(pidx, now) {
  const p = gs.players[pidx];
  if (!p.alive || p.trapped) return;
  if (p.activeBalloons >= p.maxBalloons) return;
  const bc = toTile(p.x), br = toTile(p.y);
  if (gs.balloons.some(b => b.r === br && b.c === bc)) return;
  p.activeBalloons++;
  gs.balloons.push({ r: br, c: bc, playerIdx: pidx, range: p.balloonRange, explodeAt: now + BALLOON_DELAY, passable: true });
  gs.mapDirty = true;
}

function updateBalloons(now) {
  const toExp = gs.balloons.filter(b => now >= b.explodeAt);
  gs.balloons = gs.balloons.filter(b => now < b.explodeAt);
  for (const b of toExp) {
    gs.players[b.playerIdx].activeBalloons = Math.max(0, gs.players[b.playerIdx].activeBalloons - 1);
    explodeBalloon(b, now);
  }
}

function explodeBalloon(balloon, now) {
  const { r, c } = balloon;
  const endTime = now + EXPLODE_DURATION;
  const blast = [{ r, c }];
  const dirs = [[0,1],[0,-1],[1,0],[-1,0]];
  for (const [dr, dc] of dirs) {
    for (let i = 1; i <= balloon.range; i++) {
      const nr = r + dr * i, nc = c + dc * i;
      if (nr < 0 || nr >= ROWS || nc < 0 || nc >= COLS) break;
      if (gs.map[nr][nc] === T_WALL) break;
      blast.push({ r: nr, c: nc });
      if (gs.map[nr][nc] === T_BOX) {
        gs.map[nr][nc] = T_EMPTY;
        gs.mapDirty = true;
        if (Math.random() < 0.4) {
          const type = Math.random() < 0.5 ? 'balloon_up' : 'range_up';
          gs.items.push({ r: nr, c: nc, type });
        }
        break;
      }
    }
  }
  for (const t of blast) gs.explosions.push({ ...t, endTime, playerIdx: balloon.playerIdx });

  for (const p of gs.players) {
    if (!p.alive) continue;
    if (blast.some(t => t.r === toTile(p.y) && t.c === toTile(p.x))) killPlayer(p);
  }

  const chain = gs.balloons.filter(b => b !== balloon && blast.some(t => t.r === b.r && t.c === b.c));
  gs.balloons = gs.balloons.filter(b => !chain.includes(b));
  for (const cb of chain) {
    gs.players[cb.playerIdx].activeBalloons = Math.max(0, gs.players[cb.playerIdx].activeBalloons - 1);
    explodeBalloon(cb, now);
  }
}

function updateExplosions(now) {
  gs.explosions = gs.explosions.filter(e => now < e.endTime);
}

// =============================================
// Kill / trap
// =============================================
function killPlayer(p) {
  if (!p.alive) return;
  if (p.trapped) { actuallyKillPlayer(p); return; }
  p.trapped = true;
  p.escapeCount = 0;
  p.trapStartAt = Date.now();
}

function actuallyKillPlayer(p) {
  if (!p.alive) return;
  p.alive = false;
  p.trapped = false;
  p.dyingAt = Date.now();
}

function updateTrapped(now) {
  for (const p of gs.players) {
    if (!p.alive || !p.trapped) continue;
    if (now - p.trapStartAt >= TRAP_DURATION) { actuallyKillPlayer(p); continue; }
    if (p.escapeCount >= ESCAPE_NEEDED) { p.trapped = false; p.escapeCount = 0; continue; }
    const pr = toTile(p.y), pc = toTile(p.x);
    for (const other of gs.players) {
      if (other === p || !other.alive || other.trapped) continue;
      if (toTile(other.y) === pr && toTile(other.x) === pc) { actuallyKillPlayer(p); break; }
    }
  }
}

// =============================================
// Win check
// =============================================
function checkWin() {
  if (gs.over) return;
  const alive = gs.players.filter(p => p.alive);
  if (alive.length <= 1) {
    gs.over = true;
    if (alive.length === 1) {
      alive[0].winning = true;
      gs.winner = alive[0].id - 1; // 0-indexed
    } else {
      gs.winner = -1; // draw
    }
  }
}

// =============================================
// Game init
// =============================================
function initGame(mapId) {
  const map = mapId === 'racing' ? buildRacingMap() : buildMap();
  gs = {
    map,
    explosions: [], balloons: [], items: [],
    over: false, winner: -1,
    mapId: mapId || 'village',
    mapDirty: true,
    spacePhase: 0, spaceNextAt: 0, spaceDangerAt: 0,
    spaceDanger: false, spaceWallLayer: 0,
    players: [
      {
        id: 1, x: 1*TILE + TILE/2, y: 1*TILE + TILE/2,
        alive: true, trapped: false, escapeCount: 0, trapStartAt: null,
        maxBalloons: 1, balloonRange: 3, activeBalloons: 0,
        color: '#4a9eff', borderColor: '#0055cc',
        balloonColor: '#00bfff', balloonBorder: '#0077cc',
        vx: 0, vy: 0, facing: { x: 0, y: 1 }, walkCycle: 0,
        dyingAt: null, winning: false, moving: false,
        boostEndAt: 0,
      },
      {
        id: 2, x: (COLS-2)*TILE + TILE/2, y: (ROWS-2)*TILE + TILE/2,
        alive: true, trapped: false, escapeCount: 0, trapStartAt: null,
        maxBalloons: 1, balloonRange: 3, activeBalloons: 0,
        color: '#ff6b6b', borderColor: '#cc2200',
        balloonColor: '#aaff00', balloonBorder: '#44aa00',
        vx: 0, vy: 0, facing: { x: 0, y: 1 }, walkCycle: 0,
        dyingAt: null, winning: false, moving: false,
        boostEndAt: 0,
      }
    ]
  };
  if (mapId === 'space') gs.spaceNextAt = Date.now() + 10000;
  if (mapId === 'desert') gs.desertWind = { active: false, dx: 0, dy: 0, nextAt: Date.now() + 8000, endAt: 0 };
  if (mapId === 'racing') gs.fuelStations = [
    { r: 1, c: 7, active: true, rechargeAt: 0 },
    { r: 11, c: 7, active: true, rechargeAt: 0 },
  ];
  inputs = [
    { up: false, down: false, left: false, right: false, bomb: false },
    { up: false, down: false, left: false, right: false, bomb: false },
  ];
  prevInputs = [
    { up: false, down: false, left: false, right: false, bomb: false },
    { up: false, down: false, left: false, right: false, bomb: false },
  ];
  lastBalloon = [0, 0];
}

// =============================================
// Broadcast helpers
// =============================================
function sendTo(ws, obj) {
  if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(obj));
}

function broadcast(obj) {
  const msg = JSON.stringify(obj);
  for (const c of clients) {
    if (c.ws.readyState === WebSocket.OPEN) c.ws.send(msg);
  }
}

function broadcastState() {
  if (!gs) return;
  const now = Date.now();
  const state = {
    type: 'state',
    serverTime: now,
    map: gs.map,   // 항상 포함 (맵이 작아서 부담 없음)
    players: gs.players,
    balloons: gs.balloons,
    explosions: gs.explosions,
    items: gs.items,
    over: gs.over,
    winner: gs.winner,
    mapId: gs.mapId,
    spacePhase: gs.spacePhase,
    spaceDanger: gs.spaceDanger,
    spaceDangerAt: gs.spaceDangerAt,
    spaceWallLayer: gs.spaceWallLayer,
    desertWind: gs.desertWind || null,
    fuelStations: gs.fuelStations || null,
  };
  broadcast(state);
}

// =============================================
// Game loop 60fps
// =============================================
let lastTick = Date.now();

setInterval(() => {
  if (!gs || gs.over) return;
  const now = Date.now();
  const dt = Math.min((now - lastTick) / 1000, 0.05);
  lastTick = now;

  handleInputs(now, dt);
  updateBalloons(now);
  updateExplosions(now);
  updateTrapped(now);
  updateMapGimmick(now);
  updateFuelStations(now);
  checkWin();
  broadcastState();
}, 1000 / 60);

// =============================================
// Connection management
// =============================================

// 현재 슬롯 상태 브로드캐스트 (어느 자리가 비어있는지)
function broadcastSlots() {
  broadcast({
    type: 'slots',
    taken: [slots[0] !== null, slots[1] !== null],
    lanIP: getLanIP(),
  });
}

wss.on('connection', (ws, req) => {
  const ua = req.headers['user-agent'] || '';
  const isMobile = /Mobile|Android|iPhone|iPad/i.test(ua);

  // 관전자 포함 최대 4명까지 접속 허용 (슬롯은 2개)
  if (clients.length >= 4) {
    ws.send(JSON.stringify({ type: 'full', message: '방이 가득 찼습니다.' }));
    ws.close();
    return;
  }

  const client = { ws, playerIdx: -1, isMobile };
  clients.push(client);

  // 접속하면 슬롯 선택 화면으로 → 현재 슬롯 상태 전송
  sendTo(ws, {
    type: 'pickPlayer',
    taken: [slots[0] !== null, slots[1] !== null],
    lanIP: getLanIP(),
    isMobile,
  });

  ws.on('message', raw => {
    let msg;
    try { msg = JSON.parse(raw); } catch { return; }

    // ── 슬롯 선택 ──────────────────────────────
    if (msg.type === 'claim') {
      const want = msg.playerIdx; // 0 or 1
      if (want !== 0 && want !== 1) return;

      // 이미 본인이 슬롯을 갖고 있으면 무시
      if (client.playerIdx !== -1) return;

      // 원하는 슬롯이 이미 차있으면 거절
      if (slots[want] !== null) {
        sendTo(ws, { type: 'claimFail', playerIdx: want, reason: '이미 선택된 자리입니다.' });
        return;
      }

      // 슬롯 배정
      slots[want] = client;
      client.playerIdx = want;

      sendTo(ws, {
        type: 'assign',
        playerIdx: want,
        isMobile,
        localMode: false,
        lanIP: getLanIP(),
      });

      // 모두에게 슬롯 상태 업데이트
      broadcastSlots();

      // 두 슬롯 모두 찼으면 ready
      if (slots[0] !== null && slots[1] !== null) {
        localMode = false;
        broadcast({ type: 'ready' });
        // 게임 중이었으면 현재 상태 전송
        if (gs) {
          const now = Date.now();
          sendTo(ws, {
            type: 'state', serverTime: now, map: gs.map,
            players: gs.players, balloons: gs.balloons,
            explosions: gs.explosions, items: gs.items,
            over: gs.over, winner: gs.winner, mapId: gs.mapId,
            spacePhase: gs.spacePhase, spaceDanger: gs.spaceDanger,
            spaceDangerAt: gs.spaceDangerAt, spaceWallLayer: gs.spaceWallLayer,
          });
        }
      }
      return;
    }

    // ── 로컬 2인용 (한 기기가 두 슬롯 모두 요청) ──
    if (msg.type === 'claimBoth') {
      if (slots[0] !== null || slots[1] !== null) {
        sendTo(ws, { type: 'claimFail', reason: '이미 선택된 자리가 있습니다.' });
        return;
      }
      slots[0] = client;
      slots[1] = client;
      client.playerIdx = 0;
      localMode = true;
      sendTo(ws, { type: 'assign', playerIdx: 0, isMobile, localMode: true, lanIP: getLanIP() });
      broadcastSlots();
      broadcast({ type: 'ready' });
      return;
    }

    const idx = client.playerIdx;

    // ── 맵 선택 ────────────────────────────────
    if (msg.type === 'selectMap') {
      if (idx !== 0) return;
      initGame(msg.map || 'village');
      lastTick = Date.now();
      gs.mapDirty = true;
      broadcastState();

    // ── 재시작 ─────────────────────────────────
    } else if (msg.type === 'restart') {
      if (idx !== 0 && !localMode) return;
      if (!gs) return;
      initGame(gs.mapId);
      lastTick = Date.now();
      gs.mapDirty = true;
      broadcastState();

    // ── 입력 ───────────────────────────────────
    } else if (msg.type === 'input') {
      if (!gs || gs.over) return;
      const targetIdx = (msg.playerIdx !== undefined) ? msg.playerIdx : idx;
      if (targetIdx < 0 || targetIdx > 1) return;
      if (!localMode && targetIdx !== idx) return;
      const k = msg.keys || {};
      inputs[targetIdx] = {
        up: !!k.up, down: !!k.down, left: !!k.left, right: !!k.right, bomb: !!k.bomb,
      };
    }
  });

  ws.on('close', () => {
    // 슬롯 해제
    if (client.playerIdx !== -1) {
      if (slots[0] === client) slots[0] = null;
      if (slots[1] === client) slots[1] = null;
      if (localMode) { slots[0] = null; slots[1] = null; localMode = false; }
    }
    clients = clients.filter(c => c !== client);

    // 한 명이 나가면 나머지에게 알림
    if (clients.length > 0) {
      broadcast({ type: 'disconnected' });
    }
    // 서버 게임 상태 초기화
    gs = null; slots = [null, null]; localMode = false;

    if (clients.length === 0) { gs = null; localMode = false; }
  });
});

// =============================================
// Start
// =============================================
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  const ip = getLanIP();
  console.log(`\n🎮 크레이지 워터 아케이드 서버 시작!`);
  console.log(`   로컬:  http://localhost:${PORT}`);
  console.log(`   WiFi:  http://${ip}:${PORT}  ← 이 주소를 핸드폰에서 접속`);
  console.log(`\nP1이 먼저 접속 → 맵 선택 → 게임 시작\n`);
});

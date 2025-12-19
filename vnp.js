// Von Neumann Probes (p5.js) — Radar + Warp Systems (OPTIMIZED for 10k+ probes)
// Mechanics kept the same. Replication cost = 100 for EVERYONE (player + AI), no DNA multiplier.
// Major optimizations:
// - Fixed-step simulation with accumulator (keeps real-time speed instead of slowing down when FPS drops)
// - Probe physics/AI rewritten to avoid p5.Vector allocations (numeric math only)
// - Fast wrapping (no % in hot path)
// - Precomputed neighbor cell lists for radar + harvest (no per-ping modulo loops)
// - Draw culling + LOD (visual-only): only draw probes/resources/stars in view; simplify probe rendering when crowded
// - Sacrifice removal is O(n) compaction (no repeated splice in a loop)

let WORLD = { w: 24000, h: 24000 };

let probes = [];
let resources = [];
let resourceActive = []; // indices of active resources (amt>0)
let stars = [];

let player = null;
let camFocus = null;

let zoom = 1.0;
let paused = false;

let systemIndex = 1;
let systemInitialTotal = 0;
let systemRemainingTotal = 0;

// Visual density
const NUM_STARS = 2600;
const NUM_RES_COMMON = 1200;
const NUM_RES_RICH = 140;

// Probe/resource tuning
const PROBE_RADIUS = 10;
const RESOURCE_BASE_R = 8;

const CHILD_START_RES = 12;
const HARD_PROBE_CAP = 1000000;

// Master AI / Warp
const MASTER_TRIGGER_DEPLETION = 0.90; // 90% depleted => remaining <= 10%
const RALLY_RADIUS = 260;
const RALLY_RADIUS2 = RALLY_RADIUS * RALLY_RADIUS;
const RALLY_FRACTION = 0.65;
const RALLY_TIMEOUT = 22;
const WARP_CHARGE_TIME = 5.5;

// AI Radar (realistic sensing)
const RADAR_RANGE = 1000;
const RADAR_RANGE2 = RADAR_RANGE * RADAR_RANGE;
const RADAR_COOLDOWN_MIN = 0.85;
const RADAR_COOLDOWN_MAX = 1.55;
const WANDER_MIN = 0.6;
const WANDER_MAX = 2.4;

// Harvest contact distance
const TOUCH_PAD = 6;

// Resource distribution tuning
const CLUSTER_COUNT_MIN = 24;
const CLUSTER_COUNT_MAX = 42;
const CLUSTER_SPREAD_MIN = 220;
const CLUSTER_SPREAD_MAX = 780;

const CLUSTER_PROB_COMMON = 0.35;
const CLUSTER_PROB_RICH = 0.80;

// Spatial grid (resources)
const RES_CELL = 700;
let resGridW = 0,
  resGridH = 0;
let resGrid = []; // array of arrays of resource indices

// Precomputed neighbor cells
let radarCellNeighbors = null; // [cellIndex] -> Int32Array or Array of neighbor cell indices
let harvestCellNeighbors = null; // 3x3 neighbors

// Simulation stepping
const FIXED_DT = 1 / 50; // 50 Hz
const MAX_STEPS_PER_FRAME = 5;
let simAcc = 0;

// LOD / drawing budgets (visual only)
const LOD_SIMPLIFY_AT = 2500; // simplify non-player probe drawing when total probes exceeds this
const LOD_DOWNSAMPLE_AT = 9000; // when a LOT are in view, downsample drawing
const DRAW_MARGIN = 120; // world-units margin outside view before culling

let master = {
  state: "NORMAL", // NORMAL -> RALLY -> BUILD -> CHARGE -> WARP
  waypoint: null, // {x,y}
  t: 0,
  sacrificed: 0,
  toSacrifice: 0,
  warpMachine: null,
};

function setup() {
  createCanvas(900, 650);
  pixelDensity(1);

  // Stars (fixed across systems)
  for (let i = 0; i < NUM_STARS; i++) {
    stars.push({
      x: rand(0, WORLD.w),
      y: rand(0, WORLD.h),
      tw: rand(0.3, 1.0),
      s: rand(0.6, 2.0),
    });
  }

  // System 1
  spawnSystem();

  // Player
  player = new Probe(WORLD.w * 0.5, WORLD.h * 0.5, true, makeDNA(true));
  probes.push(player);
  camFocus = player;
}

function draw() {
  if (paused) {
    renderScene(0);
    hud();
    pausedOverlay();
    return;
  }

  // Real-time accumulator (keeps sim from slowing down when FPS drops)
  let frameDt = deltaTime / 1000;
  if (!isFinite(frameDt) || frameDt < 0) frameDt = 0;
  frameDt = min(frameDt, 0.25); // prevent huge jumps
  simAcc += frameDt;

  let steps = 0;
  while (simAcc >= FIXED_DT && steps < MAX_STEPS_PER_FRAME) {
    simStep(FIXED_DT);
    simAcc -= FIXED_DT;
    steps++;
  }
  // If we're falling behind badly, drop extra accumulated time to stay responsive
  if (steps === MAX_STEPS_PER_FRAME) simAcc = 0;

  renderScene(FIXED_DT);
  hud();
}

// ---------------- Simulation ----------------

function simStep(dt) {
  // Update probe behaviors + motion
  for (let i = 0; i < probes.length; i++) probes[i].update(dt);

  // Harvest (even if stationary)
  for (let i = 0; i < probes.length; i++) probes[i].harvest(dt);

  // Replication (only when normal)
  if (master.state === "NORMAL") {
    for (let i = 0; i < probes.length; i++) probes[i].tryAutoReplicate(dt);
  }

  // Master AI orchestration
  masterUpdate(dt);

  // Sacrifice completion + compact probe list (O(n), no splice storms)
  purgeSacrificed();
}

// ---------------- Rendering ----------------

function renderScene(dt) {
  if (!camFocus || camFocus.dead) camFocus = player;
  const cam = camFocus;

  background(6);

  push();
  translate(width / 2, height / 2);
  scale(zoom);

  drawStarfield(cam.x, cam.y);
  drawResources(cam.x, cam.y);
  drawMasterMarkers(cam.x, cam.y, dt);
  drawProbes(cam.x, cam.y);

  pop();
}

function drawStarfield(camX, camY) {
  const halfW = width / (2 * zoom);
  const halfH = height / (2 * zoom);

  noStroke();
  for (let i = 0; i < stars.length; i++) {
    const st = stars[i];
    const dx = wrapDeltaFast(st.x - camX, WORLD.w);
    const dy = wrapDeltaFast(st.y - camY, WORLD.h);

    if (abs(dx) > halfW + 60 || abs(dy) > halfH + 60) continue;

    const tw = 0.55 + 0.45 * sin(frameCount * 0.02 + st.tw * 10);
    const b = 140 + 100 * tw;

    fill(b);
    circle(dx, dy, st.s);
  }
}

function drawResources(camX, camY) {
  const halfW = width / (2 * zoom);
  const halfH = height / (2 * zoom);

  for (let i = 0; i < resourceActive.length; i++) {
    const idx = resourceActive[i];
    const r = resources[idx];

    const dx = wrapDeltaFast(r.x - camX, WORLD.w);
    const dy = wrapDeltaFast(r.y - camY, WORLD.h);

    if (abs(dx) > halfW + DRAW_MARGIN || abs(dy) > halfH + DRAW_MARGIN) continue;

    push();
    translate(dx, dy);

    const rr = r.radius;
    noStroke();

    if (r.kind === 0) {
      fill(30, 120, 255, 26);
      circle(0, 0, rr * 3.2);

      const a = map(r.amt, 0, r.maxAmt, 70, 255);
      fill(70, 170, 255, a);
      circle(0, 0, rr * 2);

      fill(190, 230, 255, 210);
      circle(0, 0, rr * 0.75);
    } else {
      fill(190, 120, 255, 22);
      circle(0, 0, rr * 3.6);

      const a = map(r.amt, 0, r.maxAmt, 80, 255);
      fill(220, 170, 255, a);
      circle(0, 0, rr * 2.1);

      fill(255, 245, 255, 220);
      circle(0, 0, rr * 0.8);
    }

    pop();
  }
}

function drawMasterMarkers(camX, camY, dt) {
  if (master.waypoint) {
    const dx = wrapDeltaFast(master.waypoint.x - camX, WORLD.w);
    const dy = wrapDeltaFast(master.waypoint.y - camY, WORLD.h);

    const pulse = 0.5 + 0.5 * sin(frameCount * 0.05);
    const r1 = 90 + 25 * pulse;
    const r2 = 150 + 35 * pulse;

    noFill();
    stroke(255, 210, 120, 160);
    strokeWeight(3);
    circle(dx, dy, r1);

    stroke(255, 210, 120, 80);
    strokeWeight(2);
    circle(dx, dy, r2);

    stroke(255, 210, 120, 120);
    strokeWeight(2);
    line(dx - 26, dy, dx + 26, dy);
    line(dx, dy - 26, dx, dy + 26);
    noStroke();
  }

  if (master.warpMachine) {
    master.warpMachine.update(dt);
    master.warpMachine.draw(camX, camY);
  }
}

function drawProbes(camX, camY) {
  const halfW = width / (2 * zoom);
  const halfH = height / (2 * zoom);

  const total = probes.length;
  const simplify = total >= LOD_SIMPLIFY_AT;

  // If we are looking into a dense rally blob, downsample drawing (visual-only)
  // Keep player + focus always drawn.
  let drawEvery = 1;
  if (total >= LOD_DOWNSAMPLE_AT) drawEvery = 2;
  if (total >= 20000) drawEvery = 3;

  for (let i = 0; i < probes.length; i++) {
    const p = probes[i];
    if (p.dead) continue;

    // Always draw player + focus
    const mustDraw = p.isPlayer || p === camFocus;

    if (!mustDraw && drawEvery > 1 && (i % drawEvery) !== 0) continue;

    const dx = wrapDeltaFast(p.x - camX, WORLD.w);
    const dy = wrapDeltaFast(p.y - camY, WORLD.h);

    if (!mustDraw && (abs(dx) > halfW + DRAW_MARGIN || abs(dy) > halfH + DRAW_MARGIN)) continue;

    p.drawAt(dx, dy, simplify, camX, camY);
  }
}

// ---------------- HUD ----------------

function hud() {
  const cost = replicateCost();
  const total = probes.length;
  const aiCount = max(0, total - 1);

  const remainingPct = systemInitialTotal > 0 ? (systemRemainingTotal / systemInitialTotal) * 100 : 0;

  push();
  resetMatrix();
  noStroke();

  fill(0, 170);
  rect(10, 10, 490, 166, 12);

  fill(255);
  textSize(14);

  const focusName = camFocus === player ? "Player" : `AI #${camFocus.id}`;
  text(`System: ${systemIndex}   |   Focus: ${focusName}`, 22, 35);
  text(`Probes: ${total} (AI: ${aiCount})`, 22, 58);
  text(`Resources remaining: ${remainingPct.toFixed(1)}%`, 22, 81);

  const pr = player.resources;
  const replAllowed = master.state === "NORMAL";
  text(
    `Player resources: ${pr.toFixed(1)}   |   Replicate cost: ${cost.toFixed(1)}${replAllowed ? "" : " (locked)"}`,
    22,
    104
  );

  const barX = 22,
    barY = 118,
    barW = 450,
    barH = 14;
  fill(255, 35);
  rect(barX, barY, barW, barH, 6);

  const t = constrain(pr / cost, 0, 1);
  fill(120, 255, 140, 200);
  rect(barX, barY, barW * t, barH, 6);

  const status = masterStatusLine();
  if (status) {
    fill(255, 230, 150);
    text(status, 22, 154);
  }

  fill(220);
  textSize(12);
  text("WASD/Arrows: thrust   Shift: boost   Space: replicate   Wheel: zoom   C: focus   P: pause", 22, 192);

  drawMinimap();
  pop();
}

function masterStatusLine() {
  if (master.state === "NORMAL") return null;

  if (master.state === "RALLY") {
    const d = master.waypoint ? distWrapped(player.x, player.y, master.waypoint.x, master.waypoint.y) : 0;
    return `Master AI: RALLY at waypoint (distance: ${d.toFixed(0)})`;
  }
  if (master.state === "BUILD") {
    return `Master AI: BUILDING warp machine (sacrificed: ${master.sacrificed}/${master.toSacrifice})`;
  }
  if (master.state === "CHARGE") {
    return `Master AI: WARP CHARGING (${max(0, WARP_CHARGE_TIME - master.t).toFixed(1)}s)`;
  }
  if (master.state === "WARP") {
    return `Master AI: WARPING...`;
  }
  return null;
}

function drawMinimap() {
  const pad = 12;
  const mw = 180,
    mh = 180;
  const x = width - mw - pad;
  const y = pad;

  noStroke();
  fill(0, 160);
  rect(x, y, mw, mh, 12);

  stroke(255, 60);
  noFill();
  rect(x + 10, y + 10, mw - 20, mh - 20, 10);
  noStroke();

  const innerX = x + 10,
    innerY = y + 10;
  const innerW = mw - 20,
    innerH = mh - 20;

  if (master.waypoint) {
    const wx = innerX + (master.waypoint.x / WORLD.w) * innerW;
    const wy = innerY + (master.waypoint.y / WORLD.h) * innerH;
    fill(255, 210, 120, 220);
    circle(wx, wy, 6);
  }

  if (camFocus) {
    const fx = innerX + (camFocus.x / WORLD.w) * innerW;
    const fy = innerY + (camFocus.y / WORLD.h) * innerH;
    fill(255, 230, 120);
    circle(fx, fy, 6);
  }

  {
    const px = innerX + (player.x / WORLD.w) * innerW;
    const py = innerY + (player.y / WORLD.h) * innerH;
    fill(120, 255, 140);
    circle(px, py, 6);
  }

  // Keep minimap draw bounded (visual-only)
  const maxDots = 2200;
  const step = max(1, floor((probes.length - 1) / maxDots));

  fill(140, 200, 255, 170);
  for (let i = 1; i < probes.length; i += step) {
    const p = probes[i];
    const px = innerX + (p.x / WORLD.w) * innerW;
    const py = innerY + (p.y / WORLD.h) * innerH;
    circle(px, py, 3);
  }
}

function pausedOverlay() {
  push();
  resetMatrix();
  fill(0, 180);
  rect(0, 0, width, height);
  fill(255);
  textAlign(CENTER, CENTER);
  textSize(28);
  text("PAUSED", width / 2, height / 2 - 12);
  textSize(14);
  text("Press P to resume", width / 2, height / 2 + 18);
  pop();
}

// ---------------- System & Master AI ----------------

function spawnSystem() {
  resources = [];
  resourceActive = [];
  systemInitialTotal = 0;
  systemRemainingTotal = 0;

  initResGrid();

  // Mixed distribution (uniform + clusters)
  const clusters = [];
  const CL = floor(rand(CLUSTER_COUNT_MIN, CLUSTER_COUNT_MAX + 1));
  for (let i = 0; i < CL; i++) {
    clusters.push({
      x: rand(0, WORLD.w),
      y: rand(0, WORLD.h),
      spread: rand(CLUSTER_SPREAD_MIN, CLUSTER_SPREAD_MAX),
      w: rand(0.6, 1.6),
    });
  }

  let id = 0;

  for (let i = 0; i < NUM_RES_COMMON; i++) {
    const r = makeResource(id++, 0, clusters);
    const idx = resources.length;
    r._arrIndex = idx;
    resources.push(r);
    activateResource(idx);
    systemInitialTotal += r.maxAmt;
  }

  for (let i = 0; i < NUM_RES_RICH; i++) {
    const r = makeResource(id++, 1, clusters);
    const idx = resources.length;
    r._arrIndex = idx;
    resources.push(r);
    activateResource(idx);
    systemInitialTotal += r.maxAmt;
  }

  systemRemainingTotal = systemInitialTotal;

  // Precompute neighbor lists AFTER grid dims are known
  buildNeighborLists();
}

function masterUpdate(dt) {
  if (dt <= 0) return;

  if (master.state === "NORMAL") {
    if (systemInitialTotal > 0) {
      const remainingFrac = systemRemainingTotal / systemInitialTotal;
      if (remainingFrac <= 1 - MASTER_TRIGGER_DEPLETION && probes.length >= 1) {
        startRally();
      }
    }
    return;
  }

  master.t += dt;

  if (master.state === "RALLY") {
    const alive = probes.length;
    const arrived = countArrivedAtWaypointSq(RALLY_RADIUS2);

    const need = max(1, floor(alive * RALLY_FRACTION));
    const timeoutOk = master.t >= RALLY_TIMEOUT && arrived >= max(1, floor(alive * 0.45));

    if (arrived >= need || timeoutOk) startBuild();
  } else if (master.state === "BUILD") {
    if (master.sacrificed >= master.toSacrifice) startCharge();
  } else if (master.state === "CHARGE") {
    if (master.t >= WARP_CHARGE_TIME) performWarp();
  }
}

function startRally() {
  master.state = "RALLY";
  master.t = 0;
  master.sacrificed = 0;
  master.toSacrifice = 0;
  master.warpMachine = null;

  master.waypoint = { x: rand(0, WORLD.w), y: rand(0, WORLD.h) };

  // Set waypoint for all probes (O(n), but only once per system)
  for (let i = 0; i < probes.length; i++) probes[i].waypoint = master.waypoint;
}

function startBuild() {
  master.state = "BUILD";
  master.t = 0;
  master.sacrificed = 0;

  if (!master.waypoint) master.waypoint = { x: WORLD.w * 0.5, y: WORLD.h * 0.5 };
  master.warpMachine = new WarpMachine(master.waypoint.x, master.waypoint.y);

  // 50% of AI probes (never the player)
  const ai = [];
  for (let i = 0; i < probes.length; i++) {
    const p = probes[i];
    if (!p.isPlayer && !p.dead) ai.push(p);
  }

  const toSac = floor(ai.length * 0.10);
  master.toSacrifice = toSac;
  if (toSac <= 0) return;

  // Select K closest WITHOUT full sort (quickselect) for better scaling
  selectKClosestInPlace(ai, toSac, master.waypoint);

  for (let i = 0; i < toSac; i++) ai[i].beginSacrifice(master.waypoint);
}

function startCharge() {
  master.state = "CHARGE";
  master.t = 0;
  if (master.warpMachine) master.warpMachine.mode = "CHARGE";
}

function performWarp() {
  master.state = "WARP";
  master.t = 0;

  systemIndex += 1;
  spawnSystem();

  // Warp survivors to a fresh region
  const cx = WORLD.w * 0.5;
  const cy = WORLD.h * 0.5;

  for (let i = 0; i < probes.length; i++) {
    const p = probes[i];

    const a = rand(0, TWO_PI);
    const m = rand(40, 560);
    p.x = wrap01Fast(cx + cos(a) * m, WORLD.w);
    p.y = wrap01Fast(cy + sin(a) * m, WORLD.h);

    const av = rand(0, TWO_PI);
    const mv = rand(10, 70);
    p.vx = cos(av) * mv;
    p.vy = sin(av) * mv;

    // Reset behaviors
    p.target = -1;
    p.waypoint = null;

    if (!p.isPlayer) {
      p.radarCooldown = rand(0.2, 1.1);
      p.wanderT = rand(0.2, 0.9);
      p.heading = rand(0, TWO_PI);
    }

    p.replCooldown = max(p.replCooldown, 0.5);
  }

  master.waypoint = null;
  master.warpMachine = null;

  master.state = "NORMAL";
  master.t = 0;

  camFocus = player;
}

function countArrivedAtWaypointSq(radiusSq) {
  if (!master.waypoint) return 0;
  const wx = master.waypoint.x,
    wy = master.waypoint.y;

  let c = 0;
  for (let i = 0; i < probes.length; i++) {
    const p = probes[i];
    if (p.dead) continue;
    const dx = wrapDeltaFast(wx - p.x, WORLD.w);
    const dy = wrapDeltaFast(wy - p.y, WORLD.h);
    if (dx * dx + dy * dy <= radiusSq) c++;
  }
  return c;
}

// ---------------- Mechanics ----------------

function replicateCost() {
  return 100;
}

// Quickselect partition to get K closest probes (no full sort)
function selectKClosestInPlace(arr, k, wp) {
  const wx = wp.x,
    wy = wp.y;

  // cache distances on objects to avoid recomputing during partition swaps
  for (let i = 0; i < arr.length; i++) {
    const p = arr[i];
    const dx = wrapDeltaFast(p.x - wx, WORLD.w);
    const dy = wrapDeltaFast(p.y - wy, WORLD.h);
    p._d2tmp = dx * dx + dy * dy;
  }

  let left = 0,
    right = arr.length - 1;
  while (true) {
    if (left >= right) return;
    const pivotIndex = partitionByD2(arr, left, right, (left + right) >> 1);
    if (k - 1 === pivotIndex) return;
    if (k - 1 < pivotIndex) right = pivotIndex - 1;
    else left = pivotIndex + 1;
  }
}

function partitionByD2(arr, left, right, pivotIndex) {
  const pivotValue = arr[pivotIndex]._d2tmp;
  swap(arr, pivotIndex, right);
  let storeIndex = left;
  for (let i = left; i < right; i++) {
    if (arr[i]._d2tmp < pivotValue) {
      swap(arr, storeIndex, i);
      storeIndex++;
    }
  }
  swap(arr, right, storeIndex);
  return storeIndex;
}

function swap(arr, i, j) {
  const t = arr[i];
  arr[i] = arr[j];
  arr[j] = t;
}

function pickWeightedCluster(clusters) {
  let sum = 0;
  for (let i = 0; i < clusters.length; i++) sum += clusters[i].w;

  let r = rand(0, sum);
  for (let i = 0; i < clusters.length; i++) {
    r -= clusters[i].w;
    if (r <= 0) return clusters[i];
  }
  return clusters[clusters.length - 1];
}

function makeResource(id, kind, clusters) {
  const clusterProb = kind === 0 ? CLUSTER_PROB_COMMON : CLUSTER_PROB_RICH;
  const useCluster = clusters && clusters.length && Math.random() < clusterProb;

  let x, y;

  if (!useCluster) {
    x = rand(0, WORLD.w);
    y = rand(0, WORLD.h);
  } else {
    const cl = pickWeightedCluster(clusters);

    // randomGaussian() is only used at spawn-time (not hot path)
    const dx = randomGaussian() * cl.spread;
    const dy = randomGaussian() * cl.spread;

    x = wrap01Fast(cl.x + dx, WORLD.w);
    y = wrap01Fast(cl.y + dy, WORLD.h);
  }

  const maxAmt = kind === 0 ? rand(18, 110) : rand(140, 420);

  return {
    id,
    kind,
    x,
    y,
    amt: maxAmt,
    maxAmt,
    radius: RESOURCE_BASE_R + sqrt(maxAmt) * (kind === 0 ? 0.52 : 0.62),
    active: false,
    activeIndex: -1,
    _arrIndex: -1,
    _gridCell: -1,
    _gridIndex: -1,
  };
}

function activateResource(idx) {
  const r = resources[idx];
  r.active = true;
  r.activeIndex = resourceActive.length;
  resourceActive.push(idx);
  gridAddResource(idx);
}

function deactivateResource(idx) {
  const r = resources[idx];
  if (!r.active) return;

  gridRemoveResource(idx);

  const ai = r.activeIndex;
  const last = resourceActive.length - 1;
  const lastIdx = resourceActive[last];

  resourceActive[ai] = lastIdx;
  resources[lastIdx].activeIndex = ai;

  resourceActive.pop();
  r.active = false;
  r.activeIndex = -1;
}

function makeDNA(playerish) {
  return {
    maxSpeed: playerish ? 260 : rand(190, 260),
    accel: playerish ? 520 : rand(360, 520),
    harvest: playerish ? 22 : rand(16, 26),
  };
}

function mutateDNA(dna) {
  const m = {
    maxSpeed: dna.maxSpeed * rand(0.97, 1.03),
    accel: dna.accel * rand(0.96, 1.04),
    harvest: dna.harvest * rand(0.95, 1.06),
  };

  m.maxSpeed = constrain(m.maxSpeed, 140, 320);
  m.accel = constrain(m.accel, 260, 700);
  m.harvest = constrain(m.harvest, 8, 40);

  return m;
}

// ---------------- Warp Machine ----------------

class WarpMachine {
  constructor(x, y) {
    this.x = x;
    this.y = y;
    this.spin = rand(0, TWO_PI);
    this.mode = "BUILD";
    this.pulse = 0;
  }

  update(dt) {
    if (dt <= 0) return;
    this.spin += dt * (this.mode === "CHARGE" ? 1.6 : 0.8);
    this.pulse += dt * 2.2;
  }

  draw(camX, camY) {
    const dx = wrapDeltaFast(this.x - camX, WORLD.w);
    const dy = wrapDeltaFast(this.y - camY, WORLD.h);

    const pulse = 0.5 + 0.5 * sin(this.pulse);

    noFill();
    stroke(200, 220, 255, 90);
    strokeWeight(3);
    circle(dx, dy, 220 + 18 * pulse);

    stroke(255, 210, 120, 120);
    strokeWeight(2);
    circle(dx, dy, 170 + 14 * pulse);

    noStroke();
    if (this.mode === "BUILD") {
      fill(255, 210, 120, 18);
      circle(dx, dy, 140);
      fill(255, 235, 200, 42);
      circle(dx, dy, 80);
    } else {
      fill(120, 200, 255, 18);
      circle(dx, dy, 260 + 40 * pulse);

      fill(160, 230, 255, 55);
      circle(dx, dy, 160 + 22 * pulse);

      fill(255, 255, 255, 60);
      circle(dx, dy, 95 + 16 * pulse);
    }

    push();
    translate(dx, dy);
    rotate(this.spin);
    stroke(255, 240, 200, this.mode === "CHARGE" ? 150 : 100);
    strokeWeight(2);
    for (let i = 0; i < 8; i++) {
      const a = (TWO_PI / 8) * i;
      const r1 = 55;
      const r2 = 115 + 10 * pulse;
      line(cos(a) * r1, sin(a) * r1, cos(a) * r2, sin(a) * r2);
    }
    pop();
  }
}

// ---------------- Probe ----------------

let _probeId = 1;

class Probe {
  constructor(x, y, isPlayer, dna) {
    this.id = isPlayer ? 0 : _probeId++;
    this.isPlayer = isPlayer;

    this.x = x;
    this.y = y;

    const a = rand(0, TWO_PI);
    this.vx = cos(a) * 20;
    this.vy = sin(a) * 20;

    this.heading = rand(0, TWO_PI);
    this.resources = isPlayer ? 0 : rand(0, 8);

    this.dna = dna;

    // AI state
    this.target = -1; // resource index (NOT object reference) for faster access
    this.radarCooldown = rand(0.2, 1.2);
    this.wanderT = rand(0.2, 1.2);
    this.replCooldown = 0;

    // Master AI
    this.waypoint = null;

    // Sacrifice
    this.sacrificing = false;
    this.sacrificeT = 0;
    this.dead = false;
  }

  update(dt) {
    if (this.dead || dt <= 0) return;

    if (this.sacrificing) this.sacrificeBehavior(dt);
    else if (this.isPlayer) this.playerControl(dt);
    else this.aiControl(dt);

    // Integrate
    this.x += this.vx * dt;
    this.y += this.vy * dt;

    // Damping (dt is fixed, so use fast constant)
    // Equivalent to vel *= pow(0.35, dt), but precomputed for FIXED_DT
    const damp = DAMP_FACTOR;
    this.vx *= damp;
    this.vy *= damp;

    // Wrap (fast: positions never jump by more than world size)
    this.x = wrap01Fast(this.x, WORLD.w);
    this.y = wrap01Fast(this.y, WORLD.h);
  }

  playerControl(dt) {
    let ax = 0,
      ay = 0;
    if (keyIsDown(LEFT_ARROW) || keyIsDown(65)) ax -= 1;
    if (keyIsDown(RIGHT_ARROW) || keyIsDown(68)) ax += 1;
    if (keyIsDown(UP_ARROW) || keyIsDown(87)) ay -= 1;
    if (keyIsDown(DOWN_ARROW) || keyIsDown(83)) ay += 1;

    const boost = keyIsDown(SHIFT) ? 1.55 : 1.0;

    // Light autopilot during Master event when no input
    const masterActive = master.state !== "NORMAL" && master.waypoint;
    if (masterActive && ax === 0 && ay === 0) {
      const dx = wrapDeltaFast(master.waypoint.x - this.x, WORLD.w);
      const dy = wrapDeltaFast(master.waypoint.y - this.y, WORLD.h);
      const d2 = dx * dx + dy * dy;
      if (d2 > 1e-6) {
        const inv = 1 / sqrt(d2);
        const ux = dx * inv,
          uy = dy * inv;
        const accel = this.dna.accel * 0.85;
        this.vx += ux * accel * dt;
        this.vy += uy * accel * dt;
        this.heading = atan2(uy, ux);
      }
    }

    if (ax !== 0 || ay !== 0) {
      const mag = sqrt(ax * ax + ay * ay);
      const ux = ax / mag,
        uy = ay / mag;
      const accel = this.dna.accel * boost;
      this.vx += ux * accel * dt;
      this.vy += uy * accel * dt;
      this.heading = atan2(uy, ux);
    }

    const ms = this.dna.maxSpeed * boost;
    clampVel(this, ms);
  }

  aiControl(dt) {
    this.replCooldown = max(0, this.replCooldown - dt);

    // Master override
    const masterActive = master.state !== "NORMAL" && master.waypoint;
    if (masterActive) {
      this.waypoint = master.waypoint;
      this.steerToWaypoint(dt);
      return;
    }

    // If we have a target, chase it
    if (this.target >= 0) {
      const r = resources[this.target];
      if (r && r.amt > 0.001) {
        this.chaseTarget(dt, r);

        // Drop target if absurdly far
        const dx = wrapDeltaFast(r.x - this.x, WORLD.w);
        const dy = wrapDeltaFast(r.y - this.y, WORLD.h);
        const d2 = dx * dx + dy * dy;
        if (d2 > RADAR_RANGE2 * 3.2) this.target = -1;
        return;
      } else {
        this.target = -1;
      }
    }

    // No target: radar-wander loop
    this.radarCooldown -= dt;
    this.wanderT = max(0, this.wanderT - dt);

    if (this.radarCooldown <= 0) {
      const foundIdx = this.radarPing();
      if (foundIdx >= 0) {
        this.target = foundIdx;
        this.radarCooldown = rand(RADAR_COOLDOWN_MIN, RADAR_COOLDOWN_MAX);
        return;
      }

      // Miss: wander a bit, then ping again
      this.heading = rand(0, TWO_PI);
      this.wanderT = rand(WANDER_MIN, WANDER_MAX);
      this.radarCooldown = this.wanderT + rand(RADAR_COOLDOWN_MIN, RADAR_COOLDOWN_MAX);
    }

    if (this.wanderT <= 0 && Math.random() < 0.03) this.heading += rand(-0.7, 0.7);

    const ux = cos(this.heading),
      uy = sin(this.heading);
    const accel = this.dna.accel * 0.33;
    this.vx += ux * accel * dt;
    this.vy += uy * accel * dt;

    clampVel(this, this.dna.maxSpeed);
  }

  radarPing() {
    if (resourceActive.length <= 0) return -1;

    const ci = cellIndexForPos(this.x, this.y);
    const neigh = radarCellNeighbors[ci];

    let bestIdx = -1;
    let bestD2 = Infinity;

    for (let n = 0; n < neigh.length; n++) {
      const cell = resGrid[neigh[n]];
      for (let k = 0; k < cell.length; k++) {
        const ridx = cell[k];
        const r = resources[ridx];
        if (!r || r.amt <= 0.001) continue;

        const dx = wrapDeltaFast(r.x - this.x, WORLD.w);
        const dy = wrapDeltaFast(r.y - this.y, WORLD.h);
        const d2 = dx * dx + dy * dy;

        if (d2 <= RADAR_RANGE2 && d2 < bestD2) {
          bestD2 = d2;
          bestIdx = ridx;
        }
      }
    }

    return bestIdx;
  }

  chaseTarget(dt, r) {
    const dx = wrapDeltaFast(r.x - this.x, WORLD.w);
    const dy = wrapDeltaFast(r.y - this.y, WORLD.h);

    const d2 = dx * dx + dy * dy;
    if (d2 < 1e-6) return;

    const dist = sqrt(d2);
    const ux = dx / dist,
      uy = dy / dist;

    const slow = map(dist, 0, 240, 0.2, 1.0, true);
    const accel = this.dna.accel * 0.78 * slow;

    this.vx += ux * accel * dt;
    this.vy += uy * accel * dt;

    this.heading = atan2(uy, ux);
    clampVel(this, this.dna.maxSpeed);
  }

  steerToWaypoint(dt) {
    if (!this.waypoint) return;

    const dx = wrapDeltaFast(this.waypoint.x - this.x, WORLD.w);
    const dy = wrapDeltaFast(this.waypoint.y - this.y, WORLD.h);
    const d2 = dx * dx + dy * dy;
    if (d2 < 1) return;

    const dist = sqrt(d2);
    const ux = dx / dist,
      uy = dy / dist;

    const slow = map(dist, 0, 420, 0.25, 1.0, true);
    const accel = this.dna.accel * 0.75 * slow;

    this.vx += ux * accel * dt;
    this.vy += uy * accel * dt;
    this.heading = atan2(uy, ux);

    clampVel(this, this.dna.maxSpeed);
  }

  harvest(dt) {
    if (this.dead || dt <= 0) return;
    if (resourceActive.length <= 0) return;

    // 1) If touching current target, harvest it.
    if (this.target >= 0) {
      const r = resources[this.target];
      if (r && r.amt > 0.001) {
        const dx = wrapDeltaFast(r.x - this.x, WORLD.w);
        const dy = wrapDeltaFast(r.y - this.y, WORLD.h);
        const touch = PROBE_RADIUS + r.radius + TOUCH_PAD;
        if (dx * dx + dy * dy <= touch * touch) {
          this._harvestFrom(this.target, dt);
          return;
        }
      } else {
        this.target = -1;
      }
    }

    // 2) Otherwise, check nearby cells for any touching resource.
    const ci = cellIndexForPos(this.x, this.y);
    const neigh = harvestCellNeighbors[ci];

    let best = -1;
    let bestD2 = Infinity;

    for (let n = 0; n < neigh.length; n++) {
      const cell = resGrid[neigh[n]];
      for (let k = 0; k < cell.length; k++) {
        const ridx = cell[k];
        const r = resources[ridx];
        if (!r || r.amt <= 0.001) continue;

        const dx = wrapDeltaFast(r.x - this.x, WORLD.w);
        const dy = wrapDeltaFast(r.y - this.y, WORLD.h);
        const touch = PROBE_RADIUS + r.radius + TOUCH_PAD;
        const d2 = dx * dx + dy * dy;

        if (d2 <= touch * touch && d2 < bestD2) {
          bestD2 = d2;
          best = ridx;
        }
      }
    }

    if (best >= 0) this._harvestFrom(best, dt);
  }

  _harvestFrom(ridx, dt) {
    const r = resources[ridx];
    if (!r || r.amt <= 0.001) return;

    const take = min(r.amt, this.dna.harvest * dt);

    r.amt -= take;
    this.resources += take;
    systemRemainingTotal = max(0, systemRemainingTotal - take);

    if (r.amt <= 0.001) {
      r.amt = 0;
      deactivateResource(ridx);
      if (this.target === ridx) this.target = -1;
    }
  }

  tryAutoReplicate(dt) {
    if (this.dead || this.isPlayer) return;
    if (dt <= 0) return;
    if (probes.length >= HARD_PROBE_CAP) return;
    if (master.state !== "NORMAL") return;
    if (this.replCooldown > 0) return;

    const cost = replicateCost(); // fixed 100 for everyone
    if (this.resources >= cost * 1.08) {
      this.replicate(cost);
      this.replCooldown = rand(1.8, 3.4);
    }
  }

  replicate(cost) {
    if (probes.length >= HARD_PROBE_CAP) return;
    if (this.resources < cost) return;
    if (master.state !== "NORMAL") return;

    this.resources -= cost;

    const a = rand(0, TWO_PI);
    const m = rand(22, 45);
    const cx = wrap01Fast(this.x + cos(a) * m, WORLD.w);
    const cy = wrap01Fast(this.y + sin(a) * m, WORLD.h);

    const childDNA = mutateDNA(this.dna);
    const child = new Probe(cx, cy, false, childDNA);
    child.resources = CHILD_START_RES;

    const av = rand(0, TWO_PI);
    const mv = rand(30, 90);
    child.vx = cos(av) * mv;
    child.vy = sin(av) * mv;

    probes.push(child);
  }

  beginSacrifice(wp) {
    if (this.isPlayer) return;
    this.sacrificing = true;
    this.sacrificeT = rand(0.7, 1.25);
    this.waypoint = wp;
    this.target = -1;
  }

  sacrificeBehavior(dt) {
    if (this.waypoint) {
      const dx = wrapDeltaFast(this.waypoint.x - this.x, WORLD.w);
      const dy = wrapDeltaFast(this.waypoint.y - this.y, WORLD.h);
      const d2 = dx * dx + dy * dy;

      if (d2 > 1) {
        const inv = 1 / sqrt(d2);
        const ux = dx * inv,
          uy = dy * inv;
        const accel = this.dna.accel * 1.1;
        this.vx += ux * accel * dt;
        this.vy += uy * accel * dt;
        this.heading = atan2(uy, ux);
      }
    }

    clampVel(this, this.dna.maxSpeed * 1.15);

    this.sacrificeT -= dt;
    if (this.sacrificeT <= 0) this.dead = true;
  }

  drawAt(px, py, simplify, camX, camY) {
    const r = PROBE_RADIUS;

    // Sacrifice beam (keep, but only for visible probes)
    if (this.sacrificing && master.waypoint) {
      const wx = wrapDeltaFast(master.waypoint.x - camX, WORLD.w);
      const wy = wrapDeltaFast(master.waypoint.y - camY, WORLD.h);

      const a = map(this.sacrificeT, 0, 1.25, 0, 120, true);
      stroke(255, 210, 120, a);
      strokeWeight(2);
      line(px, py, wx, wy);
      noStroke();
    }

    // Visual LOD (mechanics unchanged)
    if (simplify && !this.isPlayer && this !== camFocus) {
      noStroke();
      fill(140, 200, 255, this.sacrificing ? 110 : 170);
      circle(px, py, 4);
      if (this === camFocus) {
        noFill();
        stroke(255, 230, 120, 160);
        strokeWeight(2);
        circle(px, py, r * 3.2);
      }
      return;
    }

    const fade = this.sacrificing ? map(this.sacrificeT, 0, 1.25, 0, 1, true) : 1;

    // Glow
    noStroke();
    if (this.isPlayer) fill(120, 255, 140, 38 * fade);
    else fill(140, 200, 255, 28 * fade);
    circle(px, py, r * 4.0);

    // Ship
    push();
    translate(px, py);
    rotate(this.heading);

    if (this.isPlayer) fill(120, 255, 140, 220 * fade);
    else fill(140, 200, 255, 200 * fade);

    stroke(255, 80 * fade);
    strokeWeight(1.2);

    beginShape();
    vertex(r * 1.35, 0);
    vertex(-r * 0.9, r * 0.9);
    vertex(-r * 0.55, 0);
    vertex(-r * 0.9, -r * 0.9);
    endShape(CLOSE);

    noStroke();
    fill(255, 220 * fade);
    circle(-r * 0.2, 0, r * 0.75);

    pop();

    // Optional target line (navigation after radar)
    if (!this.isPlayer && master.state === "NORMAL" && this.target >= 0) {
      const tr = resources[this.target];
      if (tr && tr.amt > 0.001) {
        const tx = wrapDeltaFast(tr.x - camX, WORLD.w);
        const ty = wrapDeltaFast(tr.y - camY, WORLD.h);
        stroke(160, 210, 255, 18);
        line(px, py, tx, ty);
        noStroke();
      }
    }

    // Focus ring
    if (this === camFocus) {
      noFill();
      stroke(255, 230, 120, 160);
      strokeWeight(2);
      circle(px, py, r * 3.2);
    }
  }
}

// Precompute damping for fixed dt (hot path)
const DAMP_FACTOR = Math.pow(0.35, FIXED_DT);

function clampVel(p, maxSpeed) {
  const v2 = p.vx * p.vx + p.vy * p.vy;
  const ms2 = maxSpeed * maxSpeed;
  if (v2 > ms2) {
    const inv = maxSpeed / sqrt(v2);
    p.vx *= inv;
    p.vy *= inv;
  }
}

// Remove dead sacrificed probes in one compaction pass
function purgeSacrificed() {
  let w = 0;
  let died = 0;

  for (let i = 0; i < probes.length; i++) {
    const p = probes[i];
    if (p.dead) {
      died++;
      continue;
    }
    probes[w++] = p;
  }

  if (died > 0) {
    probes.length = w;
    master.sacrificed += died;
    if (camFocus && camFocus.dead) camFocus = player;
  }
}

// ---------------- Input ----------------

function keyPressed() {
  if (key === "p" || key === "P") paused = !paused;

  if ((key === " " || key === "r" || key === "R") && !paused) {
    if (master.state !== "NORMAL") return;

    const cost = replicateCost();
    if (player.resources >= cost && probes.length < HARD_PROBE_CAP) player.replicate(cost);
  }

  if (key === "c" || key === "C") cycleFocus();
}

function cycleFocus() {
  if (probes.length <= 1) {
    camFocus = player;
    return;
  }

  // Find current focus index (O(n), but user-triggered, not hot path)
  let idx = -1;
  for (let i = 0; i < probes.length; i++) {
    if (probes[i] === camFocus) {
      idx = i;
      break;
    }
  }
  if (idx < 0) {
    camFocus = player;
    return;
  }

  // Next probe (skip dead)
  for (let step = 1; step <= probes.length; step++) {
    const p = probes[(idx + step) % probes.length];
    if (!p.dead) {
      camFocus = p;
      return;
    }
  }

  camFocus = player;
}

function mouseWheel(e) {
  const factor = 1 - e.delta * 0.0012;
  zoom *= factor;
  zoom = constrain(zoom, 0.35, 2.2);
  return false;
}

// ---------------- Wrapping helpers (FAST) ----------------

// Fast wrap for values that won't jump more than a world-size in one step.
// With FIXED_DT and speed caps, this is safe and avoids % in hot path.
function wrap01Fast(v, size) {
  if (v < 0) v += size;
  else if (v >= size) v -= size;
  // In the extremely rare case of huge jumps (e.g., external edits), fix with modulo
  if (v < 0 || v >= size) {
    v = v % size;
    if (v < 0) v += size;
  }
  return v;
}

// Inputs are always in [-size, size] because x,y are in [0,size)
function wrapDeltaFast(d, size) {
  const half = size * 0.5;
  if (d > half) d -= size;
  else if (d < -half) d += size;
  return d;
}

function distWrapped(ax, ay, bx, by) {
  const dx = wrapDeltaFast(bx - ax, WORLD.w);
  const dy = wrapDeltaFast(by - ay, WORLD.h);
  return sqrt(dx * dx + dy * dy);
}

// ---------------- Spatial grid ----------------

function initResGrid() {
  resGridW = ceil(WORLD.w / RES_CELL);
  resGridH = ceil(WORLD.h / RES_CELL);
  resGrid = Array.from({ length: resGridW * resGridH }, () => []);
}

function cellIndexForPos(x, y) {
  // x,y already wrapped to [0,size)
  let cx = (x / RES_CELL) | 0;
  let cy = (y / RES_CELL) | 0;
  if (cx >= resGridW) cx = resGridW - 1;
  if (cy >= resGridH) cy = resGridH - 1;
  return cx + cy * resGridW;
}

function gridAddResource(idx) {
  const r = resources[idx];
  const ci = cellIndexForPos(r.x, r.y);
  const cell = resGrid[ci];
  r._gridCell = ci;
  r._gridIndex = cell.length;
  cell.push(idx);
}

function gridRemoveResource(idx) {
  const r = resources[idx];
  const ci = r._gridCell;
  const gi = r._gridIndex;
  if (ci == null || gi == null || ci < 0 || gi < 0) return;

  const cell = resGrid[ci];
  const last = cell.length - 1;
  const lastIdx = cell[last];

  cell[gi] = lastIdx;
  resources[lastIdx]._gridIndex = gi;

  cell.pop();
  r._gridCell = -1;
  r._gridIndex = -1;
}

function buildNeighborLists() {
  const totalCells = resGridW * resGridH;

  // Radar neighbors: within R cells (based on RADAR_RANGE and RES_CELL)
  const R = ceil(RADAR_RANGE / RES_CELL) + 1;

  radarCellNeighbors = Array.from({ length: totalCells }, () => []);
  harvestCellNeighbors = Array.from({ length: totalCells }, () => []);

  for (let cy = 0; cy < resGridH; cy++) {
    for (let cx = 0; cx < resGridW; cx++) {
      const ci = cx + cy * resGridW;

      // Radar neighbors
      const rn = radarCellNeighbors[ci];
      for (let oy = -R; oy <= R; oy++) {
        const ncy = mod(cy + oy, resGridH);
        for (let ox = -R; ox <= R; ox++) {
          const ncx = mod(cx + ox, resGridW);
          rn.push(ncx + ncy * resGridW);
        }
      }

      // Harvest neighbors: 3x3
      const hn = harvestCellNeighbors[ci];
      for (let oy = -1; oy <= 1; oy++) {
        const ncy = mod(cy + oy, resGridH);
        for (let ox = -1; ox <= 1; ox++) {
          const ncx = mod(cx + ox, resGridW);
          hn.push(ncx + ncy * resGridW);
        }
      }
    }
  }
}

function mod(n, m) {
  n = n % m;
  if (n < 0) n += m;
  return n;
}

// ---------------- RNG helpers ----------------

function rand(a, b) {
  return a + (b - a) * Math.random();
}

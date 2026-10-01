'use strict';
/* Autonomous Driving City Sim v2 - plain JS. Sections: utils, road network, lights, sensor, NN, car, evolution, camera, renderer, UI/main loop */

/* ---------- utils ---------- */
const lerp = (a, b, t) => a + (b - a) * t;
const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const angleOf = (a, b) => Math.atan2(b.y - a.y, b.x - a.x);
const randRange = (min, max) => min + Math.random() * (max - min);
const pickRandom = arr => arr[Math.floor(Math.random() * arr.length)];
function gauss() { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); }
function getIntersection(A, B, C, D) {
    const tTop = (D.x - C.x) * (A.y - C.y) - (D.y - C.y) * (A.x - C.x);
    const uTop = (C.y - A.y) * (A.x - B.x) - (C.x - A.x) * (A.y - B.y);
    const bottom = (D.y - C.y) * (B.x - A.x) - (D.x - C.x) * (B.y - A.y);
    if (bottom === 0) return null;
    const t = tTop / bottom, u = uTop / bottom;
    if (t >= 0 && t <= 1 && u >= 0 && u <= 1) return { x: lerp(A.x, B.x, t), y: lerp(A.y, B.y, t), offset: t };
    return null;
}
function polysIntersect(p1, p2) {
    for (let i = 0; i < p1.length; i++) for (let j = 0; j < p2.length; j++)
        if (getIntersection(p1[i], p1[(i + 1) % p1.length], p2[j], p2[(j + 1) % p2.length])) return true;
    return false;
}
function segDist(p, a, b) {
    const l2 = (a.x - b.x) ** 2 + (a.y - b.y) ** 2;
    if (l2 === 0) return dist(p, a);
    const t = Math.max(0, Math.min(1, ((p.x - a.x) * (b.x - a.x) + (p.y - a.y) * (b.y - a.y)) / l2));
    return Math.hypot(p.x - (a.x + t * (b.x - a.x)), p.y - (a.y + t * (b.y - a.y)));
}
function getRGBA(v) { const a = Math.abs(v); return v < 0 ? `rgba(0,0,255,${a})` : `rgba(255,255,0,${a})`; }

/* ---------- road network ---------- */
class RoadNetwork {
    constructor() {
        this.nodes = []; this.edges = []; this.checkpoints = []; this.buildings = []; this.trees = []; this.streetLights = [];
        this._build(); this._geometry(); this._checkpoints(); this._scenery(); this._grid();
    }
    _build() {
        const COLS = 7, ROWS = 6, SP = 480, J = 45, grid = [];
        for (let r = 0; r < ROWS; r++) {
            const row = [];
            for (let c = 0; c < COLS; c++) {
                const n = { id: r * COLS + c, x: c * SP + randRange(-J, J), y: r * SP + randRange(-J, J) };
                this.nodes.push(n); row.push(n);
            }
            grid.push(row);
        }
        const cands = [], seen = new Set();
        const add = (a, b, kind) => { const k = Math.min(a.id, b.id) + '_' + Math.max(a.id, b.id); if (!seen.has(k)) { seen.add(k); cands.push({ a, b, kind }); } };
        for (let r = 0; r < ROWS; r++) for (let c = 0; c < COLS; c++) {
            if (c < COLS - 1) add(grid[r][c], grid[r][c + 1], 'grid');
            if (r < ROWS - 1) add(grid[r][c], grid[r + 1][c], 'grid');
        }
        for (let i = 0; i < Math.min(ROWS, COLS) - 1; i++) add(grid[i][i], grid[i + 1][i + 1], 'highway');
        for (let i = 0; i < ROWS - 2; i++) add(grid[i][COLS - 1 - i], grid[i + 1][COLS - 2 - i], 'highway');
        const parent = {}; this.nodes.forEach(n => parent[n.id] = n.id);
        const find = i => parent[i] === i ? i : (parent[i] = find(parent[i]));
        const shuffled = cands.slice().sort(() => Math.random() - 0.5), chosen = [];
        for (const c of shuffled) if (find(c.a.id) !== find(c.b.id)) { parent[find(c.a.id)] = find(c.b.id); chosen.push(c); }
        for (const c of shuffled) if (!chosen.includes(c) && Math.random() < 0.45) chosen.push(c);
        this.degree = {};
        for (const c of chosen) {
            this.degree[c.a.id] = (this.degree[c.a.id] || 0) + 1; this.degree[c.b.id] = (this.degree[c.b.id] || 0) + 1;
            const hw = c.kind === 'highway', w = hw ? 130 : (Math.random() < 0.3 ? 70 : 95);
            this.edges.push(new Road(c.a, c.b, w, w > 110 ? 2 : 1));
        }
    }
    _geometry() {
        this.nodeRadius = {};
        for (const n of this.nodes) {
            let m = 0; for (const e of this.edges) if (e.a === n || e.b === n) m = Math.max(m, e.width);
            this.nodeRadius[n.id] = m / 2 + 6;
        }
        for (const r of this.edges) r.build(this.nodeRadius[r.a.id], this.nodeRadius[r.b.id]);
        this.trafficLights = [];
        for (const n of this.nodes) {
            const con = this.edges.filter(e => e.a === n || e.b === n);
            if (con.length >= 3) this.trafficLights.push(new TrafficLight(n, con));
        }
    }
    _checkpoints() {
        for (const r of this.edges) {
            r.cps = [];
            for (const wp of r.waypoints) { r.cps.push(this.checkpoints.length); this.checkpoints.push({ x: wp.x, y: wp.y, radius: 46 }); }
        }
    }
    _scenery() {
        const b = this.bounds();
        for (let i = 0; i < 260; i++) {
            const x = randRange(b.minX - 150, b.maxX + 150), y = randRange(b.minY - 150, b.maxY + 150);
            let min = Infinity; for (const r of this.edges) min = Math.min(min, segDist({ x, y }, r.a, r.b) - r.width / 2);
            if (min < 80) continue;
            if (Math.random() < 0.55) {
                const w = randRange(40, 110), h = randRange(40, 110), rot = Math.random() < 0.5 ? 0 : Math.PI / 2;
                this.buildings.push([[-1, -1], [1, -1], [1, 1], [-1, 1]].map(([sx, sy]) => {
                    const px = sx * w / 2, py = sy * h / 2;
                    return { x: x + px * Math.cos(rot) - py * Math.sin(rot), y: y + px * Math.sin(rot) + py * Math.cos(rot) };
                }));
            } else this.trees.push({ x, y, radius: randRange(10, 20) });
        }
        for (const r of this.edges) for (const wp of r.waypoints)
            if (Math.random() < 0.3) this.streetLights.push({ x: wp.x + r.normal.x * (r.width / 2 + 14), y: wp.y + r.normal.y * (r.width / 2 + 14) });
    }
    // Spatial grid: each cell lists roads within ~190 units, so per-car checks touch a handful of roads instead of all of them.
    _grid() {
        this.cell = 200; this.cells = new Map();
        for (const e of this.edges) {
            const m = 190, S = this.cell;
            const x0 = Math.floor((Math.min(e.a.x, e.b.x) - m) / S), x1 = Math.floor((Math.max(e.a.x, e.b.x) + m) / S);
            const y0 = Math.floor((Math.min(e.a.y, e.b.y) - m) / S), y1 = Math.floor((Math.max(e.a.y, e.b.y) + m) / S);
            for (let x = x0; x <= x1; x++) for (let y = y0; y <= y1; y++) {
                const k = x + ',' + y; if (!this.cells.has(k)) this.cells.set(k, []); this.cells.get(k).push(e);
            }
        }
    }
    nearEdges(p) { return this.cells.get(Math.floor(p.x / this.cell) + ',' + Math.floor(p.y / this.cell)) || []; }
    onRoad(p) {
        for (const e of this.nearEdges(p)) {
            if (segDist(p, e.a, e.b) <= e.width / 2 + 2) return true;
            if (dist(p, e.a) < this.nodeRadius[e.a.id] || dist(p, e.b) < this.nodeRadius[e.b.id]) return true;
        }
        return false;
    }
    // Lane-keeping info for the AI: heading error (-1..1, 0 = parallel to the road, direction-agnostic)
    // and lateral offset from the right-hand lane centre (-1..1). Replaces absolute-heading inputs, which made cars memorise "turn right here".
    laneInfo(c) {
        const h = c.heading; let best = null;
        for (const e of this.nearEdges(c)) {
            const d = segDist(c, e.a, e.b);
            if (d > e.width / 2 + 25) continue;
            let diff = h - Math.atan2(e.dir.y, e.dir.x);
            diff = Math.atan2(Math.sin(diff), Math.cos(diff));
            let sg = 1;
            if (Math.abs(diff) > Math.PI / 2) { diff += diff > 0 ? -Math.PI : Math.PI; sg = -1; }
            const score = Math.abs(diff) + d / 400;
            if (!best || score < best.score) best = { score, diff, sg, e };
        }
        if (!best) return { err: 0, off: 0 };
        const e = best.e, side = ((c.x - e.a.x) * e.normal.x + (c.y - e.a.y) * e.normal.y) * best.sg;
        const off = (side - e.width / 4) / (e.width / 2);
        return { err: Math.max(-1, Math.min(1, best.diff / (Math.PI / 2))), off: Math.max(-1, Math.min(1, off)) };
    }
    bounds() {
        let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
        for (const n of this.nodes) { minX = Math.min(minX, n.x); maxX = Math.max(maxX, n.x); minY = Math.min(minY, n.y); maxY = Math.max(maxY, n.y); }
        return { minX, maxX, minY, maxY };
    }
    randomPath(steps) {
        let edge = pickRandom(this.edges), forward = Math.random() < 0.5;
        const path = [{ edge, forward }];
        let node = forward ? edge.b : edge.a;
        for (let i = 0; i < steps; i++) {
            const opts = this.edges.filter(e => (e.a === node || e.b === node) && e !== edge).map(e => ({ edge: e, forward: e.a === node }));
            if (!opts.length) break;
            const nx = pickRandom(opts); path.push(nx); edge = nx.edge; forward = nx.forward; node = forward ? edge.b : edge.a;
        }
        return path;
    }
}

class Road {
    constructor(a, b, width, lanes) {
        this.a = a; this.b = b; this.width = width; this.lanesEachWay = lanes;
        const dx = b.x - a.x, dy = b.y - a.y, len = Math.hypot(dx, dy);
        this.dir = { x: dx / len, y: dy / len }; this.normal = { x: -this.dir.y, y: this.dir.x }; this.length = len;
    }
    build(rA, rB) {
        const sA = { x: this.a.x + this.dir.x * rA, y: this.a.y + this.dir.y * rA };
        const eB = { x: this.b.x - this.dir.x * rB, y: this.b.y - this.dir.y * rB }, hw = this.width / 2, n = this.normal;
        this.leftBorder = { a: { x: sA.x + n.x * hw, y: sA.y + n.y * hw }, b: { x: eB.x + n.x * hw, y: eB.y + n.y * hw } };
        this.rightBorder = { a: { x: sA.x - n.x * hw, y: sA.y - n.y * hw }, b: { x: eB.x - n.x * hw, y: eB.y - n.y * hw } };
        this.waypoints = [];
        const count = Math.max(1, Math.floor(this.length / 220));
        for (let i = 1; i <= count; i++) this.waypoints.push({ x: lerp(this.a.x, this.b.x, i / (count + 1)), y: lerp(this.a.y, this.b.y, i / (count + 1)) });
        this.stopLineA = this._stop(this.a, rA, 1); this.stopLineB = this._stop(this.b, rB, -1);
    }
    _stop(node, r, s) {
        const o = this.width / 4;
        return { x: node.x - this.dir.x * r * s + this.normal.x * o * s, y: node.y - this.dir.y * r * s + this.normal.y * o * s };
    }
    // Right-hand lane centre + heading in the car's angle convention.
    // FIX: car convention is x -= sin(angle), y -= cos(angle), so heading = -travelAngle - PI/2.
    // (v1 used travelAngle - PI/2, which mirrored the heading on any non-horizontal road - cars spawned facing the wrong way.)
    laneCenter(fromNode, t) {
        const fwd = fromNode === this.a, s = fwd ? this.a : this.b, e = fwd ? this.b : this.a, o = this.width / 4, sg = fwd ? 1 : -1;
        return {
            x: lerp(s.x, e.x, t) + this.normal.x * o * sg, y: lerp(s.y, e.y, t) + this.normal.y * o * sg,
            angle: -Math.atan2(e.y - s.y, e.x - s.x) - Math.PI / 2
        };
    }
}

/* ---------- traffic lights ---------- */
class TrafficLight {
    constructor(node, roads) {
        this.node = node; this.roads = roads; this.phaseOf = new Map();
        for (const r of roads) {
            const n = ((Math.atan2(r.dir.y, r.dir.x) % Math.PI) + Math.PI) % Math.PI;
            this.phaseOf.set(r, n > Math.PI / 4 && n < 3 * Math.PI / 4 ? 1 : 0);
        }
        this.timer = randRange(0, 6); this.idx = 0;
        this.cycle = [['A', 7], ['AY', 1.6], ['R', 0.6], ['B', 7], ['BY', 1.6], ['R', 0.6]];
    }
    update(dt) { this.timer += dt; if (this.timer >= this.cycle[this.idx][1]) { this.timer = 0; this.idx = (this.idx + 1) % 6; } }
    stateFor(road) {
        const s = this.cycle[this.idx][0];
        if (s === 'R' || this.phaseOf.get(road) !== (s[0] === 'A' ? 0 : 1)) return 'RED';
        return s.length > 1 ? 'YELLOW' : 'GREEN';
    }
    stopPointFor(r) { return r.a === this.node ? r.stopLineA : r.stopLineB; }
}

/* ---------- sensor ---------- */
class Sensor {
    constructor(car, n = 7, len = 180, spread = Math.PI * 0.8) { this.car = car; this.rayCount = n; this.rayLength = len; this.raySpread = spread; this.rays = []; this.readings = []; }
    update(network, traffic) {
        const c = this.car, borders = [];
        for (const e of network.nearEdges(c)) borders.push(e.leftBorder, e.rightBorder);
        const polys = [];
        for (const t of traffic) if (Math.abs(t.x - c.x) < 260 && Math.abs(t.y - c.y) < 260) polys.push(t.polygon);
        this.rays = []; this.readings = [];
        for (let i = 0; i < this.rayCount; i++) {
            const a = lerp(this.raySpread / 2, -this.raySpread / 2, this.rayCount === 1 ? 0.5 : i / (this.rayCount - 1)) + c.angle;
            const ray = [{ x: c.x, y: c.y }, { x: c.x - Math.sin(a) * this.rayLength, y: c.y - Math.cos(a) * this.rayLength }];
            this.rays.push(ray);
            let best = null;
            const test = (p, q) => { const t = getIntersection(ray[0], ray[1], p, q); if (t && (!best || t.offset < best.offset)) best = t; };
            for (const b of borders) test(b.a, b.b);
            for (const p of polys) for (let k = 0; k < 4; k++) test(p[k], p[(k + 1) % 4]);
            this.readings.push(best);
        }
    }
    inputs() { return this.readings.map(r => r === null ? 0 : 1 - r.offset); }
}

/* ---------- neural network ---------- */
class NeuralNetwork {
    constructor(sizes) {
        this.sizes = sizes; this.layers = [];
        for (let i = 0; i < sizes.length - 1; i++) this.layers.push({
            weights: Array.from({ length: sizes[i] }, () => Array.from({ length: sizes[i + 1] }, () => randRange(-1, 1))),
            biases: Array.from({ length: sizes[i + 1] }, () => randRange(-1, 1))
        });
    }
    clone() { const n = new NeuralNetwork(this.sizes); n.layers = this.layers.map(l => ({ weights: l.weights.map(r => r.slice()), biases: l.biases.slice() })); return n; }
    toJSON() { return { sizes: this.sizes, layers: this.layers }; }
    static fromJSON(j) { const n = new NeuralNetwork(j.sizes); n.layers = j.layers.map(l => ({ weights: l.weights, biases: l.biases })); return n; }
    static feedForward(inputs, net) {
        let out = inputs; const acts = [inputs];
        net.layers.forEach((l, li) => {
            const raw = l.biases.map((b, o) => { let s = b; for (let i = 0; i < out.length; i++) s += out[i] * l.weights[i][o]; return s; });
            out = li === net.layers.length - 1 ? [Math.tanh(raw[0]), 1 / (1 + Math.exp(-raw[1])), 1 / (1 + Math.exp(-raw[2]))] : raw.map(Math.tanh);
            acts.push(out);
        });
        return { outputs: out, activations: acts };
    }
    // Gaussian mutation: nudge a random subset of weights (much better at refining a good brain than lerping toward random values).
    static mutate(net, rate, strength) {
        for (const l of net.layers) {
            for (let o = 0; o < l.biases.length; o++) if (Math.random() < rate) l.biases[o] += gauss() * strength;
            for (const row of l.weights) for (let o = 0; o < row.length; o++) if (Math.random() < rate) row[o] += gauss() * strength;
        }
    }
    static crossover(a, b) {
        const c = a.clone();
        c.layers.forEach((l, li) => {
            const lb = b.layers[li];
            l.biases = l.biases.map((v, i) => Math.random() < 0.5 ? v : lb.biases[i]);
            l.weights = l.weights.map((row, i) => row.map((v, j) => Math.random() < 0.5 ? v : lb.weights[i][j]));
        });
        return c;
    }
}

/* ---------- car ---------- */
let nextCarId = 1;
class Car {
    constructor(x, y, angle, type, brain = null) {
        this.id = nextCarId++; this.x = x; this.y = y; this.angle = angle; this.type = type;
        this.width = 26; this.height = 46; this.speed = 0; this.acceleration = 0.24; this.friction = 0.045; this.steerSpeed = 0.045;
        this.maxSpeed = type === 'AI' ? 3.6 : randRange(1.6, 2.4);
        this.damaged = false; this.crashed = false; this.generation = 0;
        this.color = type === 'AI' ? `hsl(${randRange(180, 260)},70%,${randRange(45, 65)}%)` : `hsl(${randRange(0, 360)},55%,50%)`;
        this.distanceTraveled = 0; this.checkpointScore = 0; this.visited = new Set(); this.timeAlive = 0; this.stuckTimer = 0; this.lastProgress = 0;
        this.sx = x; this.sy = y; this.turnAccum = 0; this.maxDisp = 0; this.laneBonus = 0; this.circled = false; this.laneErr = 0; this.laneOff = 0; this.trail = []; this.trailTick = 0;
        if (type === 'AI') { this.sensor = new Sensor(this); this.brain = brain || new NeuralNetwork([this.sensor.rayCount + 3, 12, 8, 3]); }
        else { this.path = null; this.pathIndex = 0; this.progress = 0; }
    }
    get heading() { return -this.angle - Math.PI / 2; } // standard math heading (for comparing with atan2)
    get polygon() {
        const rad = Math.hypot(this.width, this.height) / 2, al = Math.atan2(this.width, this.height), a = this.angle, p = [];
        for (const t of [a - al, a + al, Math.PI + a - al, Math.PI + a + al]) p.push({ x: this.x - Math.sin(t) * rad, y: this.y - Math.cos(t) * rad });
        return p;
    }
    update(dt, network, traffic) {
        if (this.damaged) return;
        this.timeAlive += dt;
        if (this.type === 'AI') {
            this.sensor.update(network, traffic);
            const lane = network.laneInfo(this); this.laneErr = lane.err; this.laneOff = lane.off;
            const { outputs, activations } = NeuralNetwork.feedForward([...this.sensor.inputs(), this.speed / this.maxSpeed, lane.err, lane.off], this.brain);
            this.lastActivations = activations;
            const a0 = this.angle;
            this._drive(outputs[0], outputs[1], outputs[2]);
            this.turnAccum += this.angle - a0;
        } else this._driveTraffic(network);
        const f = dt * 60;
        this.x -= Math.sin(this.angle) * this.speed * f; this.y -= Math.cos(this.angle) * this.speed * f;
        this.distanceTraveled += Math.abs(this.speed) * f;
        if (this.type !== 'AI') return;
        this.stuckTimer = Math.abs(this.speed) < 0.05 ? this.stuckTimer + dt : 0;
        this.maxDisp = Math.max(this.maxDisp, Math.hypot(this.x - this.sx, this.y - this.sy));
        if (this.speed > 0.8) this.laneBonus += (1 - Math.abs(this.laneOff)) * (1 - Math.abs(this.laneErr)) * (this.speed / this.maxSpeed) * 0.004 * f;
        if (++this.trailTick % 10 === 0) { this.trail.push({ x: this.x, y: this.y, angle: this.angle, speed: this.speed }); if (this.trail.length > 12) this.trail.shift(); }
        this._checkDamage(network, traffic); this._trackFitness(network);
        // Retire cars that stop making progress - this is what makes generations short (and learning fast).
        if (!this.damaged && (this.stuckTimer > 2.5 || this.timeAlive - this.lastProgress > 7)) this.damaged = true;
        // Going in circles: accumulated steering of ~320 degrees (same direction) without reaching a new checkpoint.
        if (!this.damaged && Math.abs(this.turnAccum) > Math.PI * 1.8) { this.damaged = true; this.circled = true; }
    }
    _drive(steer, throttle, brake) {
        if (throttle > 0.15) this.speed += this.acceleration * throttle;
        if (brake > 0.15) this.speed -= this.acceleration * 1.6 * brake;
        this.speed *= 1 - this.friction;
        this.speed = Math.max(-this.maxSpeed / 2, Math.min(this.maxSpeed, this.speed));
        const sf = Math.min(1, Math.abs(this.speed) / (this.maxSpeed * 0.4) + 0.15);
        this.angle -= steer * this.steerSpeed * sf * (this.speed >= 0 ? 1 : -1);
    }
    _driveTraffic(network) {
        if (!this.path || !this.path[this.pathIndex]) this._newPath(network);
        const step = this.path[this.pathIndex], road = step.edge, from = step.forward ? road.a : road.b;
        this.progress += this.speed / Math.max(road.length, 1);
        const target = road.laneCenter(from, Math.min(1, this.progress));
        let diff = target.angle - this.angle;
        while (diff > Math.PI) diff -= 2 * Math.PI; while (diff < -Math.PI) diff += 2 * Math.PI;
        this.angle += Math.max(-this.steerSpeed * 1.2, Math.min(this.steerSpeed * 1.2, diff));
        this.x = lerp(this.x, target.x, 0.12); this.y = lerp(this.y, target.y, 0.12);
        let want = this.maxSpeed;
        const h = this.heading;
        for (const o of network.traffic) {
            if (o === this) continue;
            const d = dist(this, o);
            if (d < 70) { const ahead = Math.cos(h - angleOf(this, o)); if (d < 55 && ahead > 0.5) want = 0; else if (ahead > 0.3) want = Math.min(want, o.speed * 0.9); }
        }
        for (const o of network.ai) if (!o.damaged) { const d = dist(this, o); if (d < 60 && Math.cos(h - angleOf(this, o)) > 0.5) { want = 0; break; } }
        if (this.progress > 0.75 && this.progress < 0.98) {
            const end = step.forward ? road.b : road.a, light = network.trafficLights.find(l => l.node === end);
            if (light && light.stateFor(road) !== 'GREEN') want = 0;
        }
        this.speed += this.speed < want ? this.acceleration * 0.6 : -this.acceleration * 0.9;
        this.speed = Math.max(0, Math.min(this.maxSpeed, this.speed));
        if (this.progress >= 1) { this.pathIndex++; this.progress = 0; if (this.pathIndex >= this.path.length - 1) this._newPath(network); }
    }
    _newPath(network) {
        this.path = network.randomPath(12); this.pathIndex = 0; this.progress = 0;
        const s = this.path[0], c = s.edge.laneCenter(s.forward ? s.edge.a : s.edge.b, 0.02);
        this.x = c.x; this.y = c.y; this.angle = c.angle;
    }
    _checkDamage(network, traffic) {
        const kill = () => { this.damaged = true; this.crashed = true; };
        if (!network.onRoad(this)) return kill();
        const poly = this.polygon;
        for (const e of network.nearEdges(this)) for (const b of [e.leftBorder, e.rightBorder])
            for (let i = 0; i < 4; i++) if (getIntersection(poly[i], poly[(i + 1) % 4], b.a, b.b)) return kill();
        for (const o of traffic) if (Math.abs(o.x - this.x) < 60 && Math.abs(o.y - this.y) < 60 && polysIntersect(poly, o.polygon)) return kill();
    }
    _trackFitness(network) {
        for (const e of network.nearEdges(this)) for (const i of e.cps) {
            if (this.visited.has(i)) continue;
            const cp = network.checkpoints[i];
            if (dist(this, cp) < cp.radius) { this.visited.add(i); this.checkpointScore += 20; this.lastProgress = this.timeAlive; this.turnAccum = 0; }
        }
    }
    // New checkpoints dominate; raw distance driven is no longer rewarded (that is what made circling pay off).
    get fitness() { return this.type !== 'AI' ? 0 : this.checkpointScore + this.maxDisp * 0.03 + this.laneBonus - (this.crashed ? 30 : 0) - (this.circled ? 15 : 0); }
    draw(ctx, showSensor, selected, night, alpha = 1) {
        const p = this.polygon;
        ctx.save(); ctx.globalAlpha = alpha;
        ctx.beginPath(); ctx.moveTo(p[0].x, p[0].y); for (let i = 1; i < 4; i++) ctx.lineTo(p[i].x, p[i].y); ctx.closePath();
        ctx.fillStyle = this.color; ctx.shadowColor = 'rgba(0,0,0,0.35)'; ctx.shadowBlur = selected ? 6 : 0; ctx.fill(); ctx.shadowBlur = 0;
        ctx.strokeStyle = selected ? '#ffdd33' : 'rgba(0,0,0,0.35)'; ctx.lineWidth = selected ? 3 : 1; ctx.stroke();
        const mf = { x: (p[0].x + p[1].x) / 2, y: (p[0].y + p[1].y) / 2 }, mm = { x: (p[0].x + p[2].x) / 2, y: (p[0].y + p[2].y) / 2 };
        ctx.fillStyle = 'rgba(20,30,45,0.7)'; ctx.beginPath(); ctx.arc((mf.x + mm.x) / 2, (mf.y + mm.y) / 2, this.width * 0.32, 0, 6.283); ctx.fill();
        if (night) { ctx.fillStyle = 'rgba(255,240,160,0.9)'; for (const q of [p[0], p[1]]) { ctx.beginPath(); ctx.arc(q.x, q.y, 3, 0, 6.283); ctx.fill(); } }
        ctx.restore();
        if (showSensor && this.sensor) this.sensor.rays.forEach((ray, i) => {
            const end = this.sensor.readings[i] || ray[1];
            ctx.lineWidth = 2; ctx.strokeStyle = 'rgba(255,220,0,0.75)'; ctx.beginPath(); ctx.moveTo(ray[0].x, ray[0].y); ctx.lineTo(end.x, end.y); ctx.stroke();
            ctx.strokeStyle = 'rgba(0,0,0,0.55)'; ctx.beginPath(); ctx.moveTo(ray[1].x, ray[1].y); ctx.lineTo(end.x, end.y); ctx.stroke();
        });
    }
}

/* ---------- evolution ---------- */
// Adaptive evolution:
//  - top-3 elites survive, children = crossover + gaussian mutation, mutation + random immigrants grow while progress is stale
//  - a hall of fame of past generation winners is mixed back in when stale (escapes "everyone turns right" local optima)
//  - when stale, every other generation is a PRACTICE generation: all cars spawn ~2s before where the leader got stuck
//    (alternating with a random spot on the map), so the population is trained on exactly the thing it fails at
//  - practice generations feed their winners into the parent pool but never touch best-ever / the chart
class EvolutionManager {
    constructor(network, size) {
        this.network = network; this.populationSize = size; this.generation = 1; this.bestEverBrain = null; this.bestEverFitness = 0;
        this.stale = 0; this.history = []; this.genTimer = 0; this.maxGenTime = 60; this.onImprove = null; this.cars = [];
        this.hall = []; this.practice = null; this.practiceCount = 0;
        const wc = network.edges.filter(e => (network.degree[e.a.id] || 0) >= 3 || (network.degree[e.b.id] || 0) >= 3);
        const road = pickRandom(wc.length ? wc : network.edges);
        this.mainSpawn = road.laneCenter(Math.random() < 0.5 ? road.a : road.b, 0.15); this.spawn = this.mainSpawn;
        this.spawnPopulation(null);
    }
    _pick(P) { return P[Math.floor(Math.random() ** 2 * P.length)]; }
    spawnPopulation(P) {
        const n = this.populationSize, st = this.stale, s = Math.min(0.6, 0.12 + st * 0.04), fresh = 0.1 + Math.min(0.2, st * 0.02);
        this.cars = [];
        for (let i = 0; i < n; i++) {
            let brain = null;
            if (P && P.length) {
                if (i < Math.min(3, P.length)) brain = P[i].clone();
                else if (i < n * 0.55) { brain = NeuralNetwork.crossover(this._pick(P), this._pick(P)); NeuralNetwork.mutate(brain, 0.15, s); }
                else if (i < n * (1 - fresh)) {
                    const pool = st >= 3 && this.hall.length && Math.random() < 0.4 ? this.hall : P.slice(0, Math.min(3, P.length));
                    brain = pickRandom(pool).clone(); NeuralNetwork.mutate(brain, 0.4, s * 1.5);
                }
            }
            const car = new Car(this.spawn.x, this.spawn.y, this.spawn.angle, 'AI', brain);
            if (this.spawn.speed) car.speed = this.spawn.speed;
            car.generation = this.generation; this.cars.push(car);
        }
        this.genTimer = 0; this.network.ai = this.cars;
    }
    update(dt, traffic) {
        this.genTimer += dt;
        let alive = 0;
        for (const c of this.cars) { c.update(dt, this.network, traffic); if (!c.damaged) alive++; }
        if (!alive || this.genTimer > (this.practice ? 30 : this.maxGenTime)) this.nextGeneration();
    }
    // Where did the leader get stuck? Back up ~2s along its trail so the drill starts just before the failure.
    _stuckSpawn(car) {
        const t = car && car.trail.length ? car.trail[0] : null;
        return t ? { x: t.x, y: t.y, angle: t.angle, speed: Math.max(0.5, t.speed) } : null;
    }
    _randomSpawn() {
        const road = pickRandom(this.network.edges);
        return road.laneCenter(Math.random() < 0.5 ? road.a : road.b, randRange(0.15, 0.85));
    }
    nextGeneration() {
        const ranked = this.cars.slice().sort((a, b) => b.fitness - a.fitness), best = ranked[0], wasPractice = !!this.practice;
        if (!wasPractice) {
            this.history.push({ best: best.fitness, avg: this.cars.reduce((s, c) => s + c.fitness, 0) / this.cars.length });
            if (this.history.length > 200) this.history.shift();
            this.hall.push(best.brain.clone()); if (this.hall.length > 8) this.hall.shift();
            if (best.fitness > this.bestEverFitness) { this.bestEverFitness = best.fitness; this.bestEverBrain = best.brain.clone(); this.stale = 0; if (this.onImprove) this.onImprove(this); }
            else this.stale++;
        }
        const P = ranked.slice(0, 9).map(c => c.brain); if (this.bestEverBrain) P.unshift(this.bestEverBrain);
        this.generation++;
        this.practice = null; this.spawn = this.mainSpawn;
        // Stuck? Drill the failure spot (2 of every 3 drills), or a random spot on the map (1 of 3) for variety.
        if (!wasPractice && this.stale >= 2) {
            const kind = this.practiceCount++ % 3 === 2 ? 'random' : 'drill';
            const sp = kind === 'drill' ? this._stuckSpawn(best) : this._randomSpawn();
            if (sp) { this.spawn = sp; this.practice = { label: kind }; }
        }
        this.spawnPopulation(P);
    }
    get bestAlive() { let b = null; for (const c of this.cars) if (!c.damaged && (!b || c.fitness > b.fitness)) b = c; return b; }
    get bestCar() { return this.cars.reduce((b, c) => !b || c.fitness > b.fitness ? c : b, null); }
}

/* ---------- camera ---------- */
class Camera {
    constructor(canvas) {
        this.canvas = canvas; this.x = 0; this.y = 0; this.zoom = 1; this.dragging = false; this.dragStart = null; this.followCar = null;
        canvas.addEventListener('mousedown', e => { this.dragging = true; this.followCar = null; this.dragStart = { x: e.clientX, y: e.clientY, cx: this.x, cy: this.y }; window.dispatchEvent(new Event('camdrag')); });
        window.addEventListener('mouseup', () => this.dragging = false);
        window.addEventListener('mousemove', e => { if (this.dragging) { this.x = this.dragStart.cx - (e.clientX - this.dragStart.x) / this.zoom; this.y = this.dragStart.cy - (e.clientY - this.dragStart.y) / this.zoom; } });
        canvas.addEventListener('wheel', e => { e.preventDefault(); this.zoom = Math.max(0.2, Math.min(2.5, this.zoom * (e.deltaY < 0 ? 1.1 : 0.9))); }, { passive: false });
    }
    reset(c) { this.x = c.x; this.y = c.y; this.zoom = 0.85; this.followCar = null; }
    update() { if (this.followCar && !this.followCar.damaged) { this.x = lerp(this.x, this.followCar.x, 0.1); this.y = lerp(this.y, this.followCar.y, 0.1); } }
    apply(ctx) { ctx.translate(this.canvas.width / 2, this.canvas.height / 2); ctx.scale(this.zoom, this.zoom); ctx.translate(-this.x, -this.y); }
    screenToWorld(sx, sy) { return { x: (sx - this.canvas.width / 2) / this.zoom + this.x, y: (sy - this.canvas.height / 2) / this.zoom + this.y }; }
}

/* ---------- renderer ---------- */
const Renderer = {
    line(ctx, r) { ctx.beginPath(); ctx.moveTo(r.a.x, r.a.y); ctx.lineTo(r.b.x, r.b.y); ctx.stroke(); },
    drawWorld(ctx, net, night) {
        const b = net.bounds(); ctx.fillStyle = night ? '#16241a' : '#7fb86b'; ctx.fillRect(b.minX - 600, b.minY - 600, b.maxX - b.minX + 1200, b.maxY - b.minY + 1200);
        ctx.lineCap = 'round'; ctx.strokeStyle = '#c9c4b8';
        for (const r of net.edges) { ctx.lineWidth = r.width + 16; this.line(ctx, r); }
        const asphalt = night ? '#26282e' : '#3a3b40'; ctx.strokeStyle = asphalt; ctx.fillStyle = asphalt;
        for (const r of net.edges) { ctx.lineWidth = r.width; this.line(ctx, r); }
        for (const n of net.nodes) { ctx.beginPath(); ctx.arc(n.x, n.y, net.nodeRadius[n.id], 0, 6.283); ctx.fill(); }
        for (const r of net.edges) {
            if (r.lanesEachWay > 1) { ctx.setLineDash([16, 14]); ctx.strokeStyle = 'rgba(255,255,255,0.85)'; ctx.lineWidth = 2.5; this.line(ctx, r); ctx.setLineDash([]); }
            ctx.strokeStyle = 'rgba(255,220,60,0.9)'; ctx.lineWidth = 2.5; this.line(ctx, r);
        }
        for (const l of net.trafficLights) for (const r of l.roads) {
            const s = l.stopPointFor(r), st = l.stateFor(r);
            ctx.save(); ctx.translate(s.x, s.y); ctx.rotate(Math.atan2(r.dir.y, r.dir.x) + Math.PI / 2); ctx.fillStyle = 'rgba(255,255,255,0.9)'; ctx.fillRect(-r.width / 4 - 3, -3, r.width / 2 + 6, 6); ctx.restore();
            ctx.beginPath(); ctx.fillStyle = st === 'GREEN' ? '#33e07a' : st === 'YELLOW' ? '#ffd23f' : '#ff4d4d';
            ctx.arc(s.x - r.normal.x * (r.width / 2 + 20), s.y - r.normal.y * (r.width / 2 + 20), 6, 0, 6.283); ctx.fill();
        }
        for (const p of net.buildings) {
            ctx.beginPath(); ctx.moveTo(p[0].x, p[0].y); for (let i = 1; i < 4; i++) ctx.lineTo(p[i].x, p[i].y); ctx.closePath();
            ctx.fillStyle = night ? '#22262f' : '#9aa0ad'; ctx.fill(); ctx.strokeStyle = 'rgba(0,0,0,0.25)'; ctx.lineWidth = 1.5; ctx.stroke();
        }
        for (const t of net.trees) { ctx.beginPath(); ctx.fillStyle = '#3f7a3a'; ctx.arc(t.x, t.y, t.radius, 0, 6.283); ctx.fill(); }
        if (night) for (const s of net.streetLights) {
            const g = ctx.createRadialGradient(s.x, s.y, 2, s.x, s.y, 45); g.addColorStop(0, 'rgba(255,235,160,0.35)'); g.addColorStop(1, 'rgba(255,235,160,0)');
            ctx.fillStyle = g; ctx.beginPath(); ctx.arc(s.x, s.y, 45, 0, 6.283); ctx.fill();
        }
    },
    drawCheckpoints(ctx, net, visited) {
        net.checkpoints.forEach((cp, i) => { ctx.beginPath(); ctx.strokeStyle = visited && visited.has(i) ? 'rgba(60,220,120,0.85)' : 'rgba(255,255,255,0.35)'; ctx.lineWidth = 2; ctx.arc(cp.x, cp.y, cp.radius, 0, 6.283); ctx.stroke(); });
    },
    drawBorders(ctx, net) { ctx.strokeStyle = 'rgba(255,60,60,0.9)'; ctx.lineWidth = 3; for (const r of net.edges) { this.line(ctx, r.leftBorder); this.line(ctx, r.rightBorder); } },
    drawMinimap(ctx, canvas, net, ai, traffic, sel, cam) {
        const w = canvas.width, h = canvas.height, b = net.bounds(), pad = 200;
        const sc = Math.min(w / (b.maxX - b.minX + pad * 2), h / (b.maxY - b.minY + pad * 2)), ox = -(b.minX - pad) * sc, oy = -(b.minY - pad) * sc;
        ctx.clearRect(0, 0, w, h); ctx.fillStyle = 'rgba(15,18,24,0.85)'; ctx.fillRect(0, 0, w, h);
        ctx.strokeStyle = 'rgba(255,255,255,0.35)'; ctx.lineWidth = 1;
        for (const r of net.edges) { ctx.beginPath(); ctx.moveTo(r.a.x * sc + ox, r.a.y * sc + oy); ctx.lineTo(r.b.x * sc + ox, r.b.y * sc + oy); ctx.stroke(); }
        ctx.fillStyle = '#7dd3fc'; for (const c of traffic) ctx.fillRect(c.x * sc + ox - 1, c.y * sc + oy - 1, 2, 2);
        ctx.fillStyle = '#4ade80'; for (const c of ai) if (!c.damaged) ctx.fillRect(c.x * sc + ox - 1.5, c.y * sc + oy - 1.5, 3, 3);
        if (sel) { ctx.fillStyle = '#facc15'; ctx.beginPath(); ctx.arc(sel.x * sc + ox, sel.y * sc + oy, 4, 0, 6.283); ctx.fill(); }
        const vw = cam.canvas.width / cam.zoom * sc, vh = cam.canvas.height / cam.zoom * sc;
        ctx.strokeStyle = 'rgba(255,255,255,0.8)'; ctx.lineWidth = 1.5; ctx.strokeRect(cam.x * sc + ox - vw / 2, cam.y * sc + oy - vh / 2, vw, vh);
    }
};

/* ---------- UI + main loop ---------- */
function main() {
    const $ = id => document.getElementById(id);
    const canvas = $('worldCanvas'), ctx = canvas.getContext('2d'), mmCanvas = $('minimapCanvas'), mmCtx = mmCanvas.getContext('2d');
    const nnCanvas = $('nnCanvas'), nnCtx = nnCanvas.getContext('2d'), chCanvas = $('chartCanvas'), chCtx = chCanvas.getContext('2d');
    const resize = () => { canvas.width = canvas.clientWidth; canvas.height = canvas.clientHeight; };
    window.addEventListener('resize', resize);

    const network = new RoadNetwork(), camera = new Camera(canvas);
    resize();
    const bnd = network.bounds(), center = { x: (bnd.minX + bnd.maxX) / 2, y: (bnd.minY + bnd.maxY) / 2 };
    camera.reset(center);

    const state = { running: true, speed: 1, selected: null, follow: true };
    let traffic = [];
    function makeTraffic(n) {
        traffic = []; network.traffic = traffic;
        for (let i = 0; i < n; i++) { const c = new Car(0, 0, 0, 'TRAFFIC'); c._newPath(network); traffic.push(c); }
    }
    function newEvo(size, brain) {
        evo = new EvolutionManager(network, size);
        evo.onImprove = e => { try { localStorage.setItem('drivingSim.save2', JSON.stringify({ brain: e.bestEverBrain.toJSON(), generation: e.generation, bestFitness: e.bestEverFitness, populationSize: e.populationSize })); } catch (_) {} };
        if (brain) { evo.bestEverBrain = brain; evo.spawnPopulation([brain]); }
        state.selected = null;
    }
    let evo;
    makeTraffic(parseInt($('trafficInput').value) || 12);
    newEvo(parseInt($('carsInput').value) || 80);

    // resume from the autosave if there is one
    try {
        const s = JSON.parse(localStorage.getItem('drivingSim.save2'));
        if (s) { newEvo(evo.populationSize, NeuralNetwork.fromJSON(s.brain)); evo.generation = s.generation || 1; evo.bestEverFitness = s.bestFitness || 0; }
    } catch (_) {}

    const flash = (btn, text) => { const old = btn.textContent; btn.textContent = text; setTimeout(() => btn.textContent = old, 900); };
    const togglePlay = () => { state.running = !state.running; $('btnPause').textContent = state.running ? 'Pause' : 'Resume'; };
    $('btnPause').addEventListener('click', togglePlay);
    $('btnNextGen').addEventListener('click', () => evo.nextGeneration());
    $('btnReset').addEventListener('click', () => newEvo(evo.populationSize));
    $('carsInput').addEventListener('change', e => { const n = Math.max(10, Math.min(300, parseInt(e.target.value) || 80)); e.target.value = n; newEvo(n, evo.bestEverBrain); });
    $('trafficInput').addEventListener('change', e => { const n = Math.max(0, Math.min(60, parseInt(e.target.value) || 0)); e.target.value = n; makeTraffic(n); });
    document.querySelectorAll('.speed-btn').forEach(btn => btn.addEventListener('click', () => {
        document.querySelectorAll('.speed-btn').forEach(b => b.classList.remove('active')); btn.classList.add('active'); state.speed = parseFloat(btn.dataset.speed);
    }));
    $('cbFollow').addEventListener('change', e => { state.follow = e.target.checked; if (!state.follow) camera.followCar = null; });
    window.addEventListener('camdrag', () => { state.follow = false; $('cbFollow').checked = false; });
    $('btnResetCam').addEventListener('click', () => camera.reset(center));
    $('btnSave').addEventListener('click', () => { if (evo.bestEverBrain) { evo.onImprove(evo); flash($('btnSave'), 'Saved!'); } });
    $('btnLoad').addEventListener('click', () => {
        try { const s = JSON.parse(localStorage.getItem('drivingSim.save2')); newEvo(evo.populationSize, NeuralNetwork.fromJSON(s.brain)); evo.generation = s.generation || 1; evo.bestEverFitness = s.bestFitness || 0; flash($('btnLoad'), 'Loaded!'); }
        catch (_) { flash($('btnLoad'), 'No save'); }
    });
    $('btnResetTraining').addEventListener('click', () => { localStorage.removeItem('drivingSim.save2'); newEvo(evo.populationSize); flash($('btnResetTraining'), 'Cleared'); });
    window.addEventListener('keydown', e => {
        if (e.target.tagName === 'INPUT') return;
        if (e.code === 'Space') { e.preventDefault(); togglePlay(); }
        if (e.key === 'n') evo.nextGeneration();
        const btns = document.querySelectorAll('.speed-btn'), i = parseInt(e.key) - 1; if (btns[i]) btns[i].click();
    });
    canvas.addEventListener('click', e => {
        if (camera.dragStart && Math.hypot(e.clientX - camera.dragStart.x, e.clientY - camera.dragStart.y) > 6) return;
        const r = canvas.getBoundingClientRect(), w = camera.screenToWorld(e.clientX - r.left, e.clientY - r.top);
        let best = null, bd = 26; for (const c of evo.cars) if (!c.damaged) { const d = dist(w, c); if (d < bd) { best = c; bd = d; } }
        if (best) { state.selected = best; camera.followCar = best; state.follow = false; $('cbFollow').checked = false; }
    });

    function drawNetwork(car) {
        nnCtx.clearRect(0, 0, nnCanvas.width, nnCanvas.height);
        if (!car || !car.lastActivations) return;
        const A = car.lastActivations, m = 24, lw = (nnCanvas.width - m * 2) / (A.length - 1);
        const nx = l => m + l * lw, ny = (n, i) => lerp(nnCanvas.height - m, m, n === 1 ? 0.5 : i / (n - 1));
        for (let l = 0; l < A.length - 1; l++) for (let i = 0; i < A[l].length; i++) for (let o = 0; o < A[l + 1].length; o++) {
            nnCtx.beginPath(); nnCtx.strokeStyle = getRGBA(Math.max(-1, Math.min(1, car.brain.layers[l].weights[i][o]))); nnCtx.lineWidth = 1.2;
            nnCtx.moveTo(nx(l), ny(A[l].length, i)); nnCtx.lineTo(nx(l + 1), ny(A[l + 1].length, o)); nnCtx.stroke();
        }
        A.forEach((lvl, l) => lvl.forEach((v, i) => {
            nnCtx.beginPath(); nnCtx.fillStyle = getRGBA(Math.max(-1, Math.min(1, v))); nnCtx.strokeStyle = '#1a1f2b'; nnCtx.arc(nx(l), ny(lvl.length, i), 7, 0, 6.283); nnCtx.fill(); nnCtx.stroke();
            if (l === A.length - 1) { nnCtx.fillStyle = '#e5e9f0'; nnCtx.font = '10px sans-serif'; nnCtx.fillText(['STEER', 'GAS', 'BRAKE'][i], nx(l) - 36, ny(lvl.length, i) + 3); }
        }));
    }
    function drawChart() {
        const w = chCanvas.width, h = chCanvas.height, H = evo.history;
        chCtx.clearRect(0, 0, w, h);
        if (H.length < 2) { chCtx.fillStyle = '#6b7288'; chCtx.font = '12px sans-serif'; chCtx.fillText('Fitness history appears after 2 generations', 12, h / 2); return; }
        const max = Math.max(...H.map(p => p.best), 1);
        for (const [key, col] of [['avg', '#7dd3fc'], ['best', '#4ade80']]) {
            chCtx.beginPath(); chCtx.strokeStyle = col; chCtx.lineWidth = 2;
            H.forEach((p, i) => { const x = 6 + i / (H.length - 1) * (w - 12), y = h - 6 - Math.max(0, p[key]) / max * (h - 14); i ? chCtx.lineTo(x, y) : chCtx.moveTo(x, y); });
            chCtx.stroke();
        }
    }
    function infoPanel() {
        const c = state.selected;
        $('carInfoPanel').innerHTML = !c ? '<p class="muted">Click a car to inspect it, or let it follow the leader.</p>' : `
            <h3>CAR #${c.id}</h3>
            <div class="stat-row"><span>Fitness</span><b>${c.fitness.toFixed(0)}</b></div>
            <div class="stat-row"><span>Distance</span><b>${c.distanceTraveled.toFixed(0)}</b></div>
            <div class="stat-row"><span>Speed</span><b>${(Math.abs(c.speed) * 22).toFixed(0)} km/h</b></div>
            <div class="stat-row"><span>Checkpoints</span><b>${c.visited.size} / ${network.checkpoints.length}</b></div>
            <div class="stat-row"><span>Status</span><b>${c.damaged ? 'Out' : 'Driving'}</b></div>`;
    }

    function step() {
        const dt = 1 / 60;
        for (const l of network.trafficLights) l.update(dt);
        for (const t of traffic) t.update(dt, network, traffic);
        evo.update(dt, traffic);
    }

    let last = performance.now(), fps = 60, simSpeed = 1, frameNo = 0;
    function frame(now) {
        requestAnimationFrame(frame); frameNo++;
        fps = lerp(fps, 1000 / Math.max(now - last, 0.1), 0.08); last = now;
        if (state.running) {
            // Time-budgeted: run up to `speed` sim steps this frame, but never block the tab for more than ~35ms.
            // That's how 500x works - the simulation advances 500 ticks per rendered frame if your CPU can keep up.
            const t0 = performance.now(); let done = 0;
            while (done < state.speed) { step(); done++; if ((done & 7) === 0 && performance.now() - t0 > 35) break; }
            simSpeed = lerp(simSpeed, done, 0.15);
        }
        if (state.follow) { const b = evo.bestAlive; if (b) { state.selected = b; camera.followCar = b; } }
        else if (state.selected && state.selected.damaged) camera.followCar = null;
        camera.update();

        ctx.save(); ctx.clearRect(0, 0, canvas.width, canvas.height);
        ctx.fillStyle = $('cbNight').checked ? '#0b1220' : '#bfe3ff'; ctx.fillRect(0, 0, canvas.width, canvas.height);
        camera.apply(ctx);
        const night = $('cbNight').checked;
        Renderer.drawWorld(ctx, network, night);
        if ($('cbCheckpoints').checked) Renderer.drawCheckpoints(ctx, network, state.selected ? state.selected.visited : null);
        if ($('cbBorders').checked) Renderer.drawBorders(ctx, network);
        for (const t of traffic) t.draw(ctx, false, false, night);
        for (const c of evo.cars) if (!c.damaged && c !== state.selected) c.draw(ctx, false, false, night, 0.55);
        if (state.selected && !state.selected.damaged) state.selected.draw(ctx, $('cbSensors').checked, true, night);
        if (night) { ctx.fillStyle = 'rgba(5,10,25,0.35)'; ctx.fillRect(-20000, -20000, 40000, 40000); }
        ctx.restore();

        Renderer.drawMinimap(mmCtx, mmCanvas, network, evo.cars, traffic, state.selected, camera);
        if ($('cbNN').checked) drawNetwork(state.selected); else nnCtx.clearRect(0, 0, nnCanvas.width, nnCanvas.height);
        if (frameNo % 6 === 0) {
            const alive = evo.cars.filter(c => !c.damaged).length, best = evo.bestCar;
            $('statGen').textContent = evo.generation + (evo.practice ? ' (' + evo.practice.label + ')' : ''); $('statAlive').textContent = `${alive} / ${evo.cars.length}`;
            $('statBestFit').textContent = best ? best.fitness.toFixed(0) : 0; $('statBestEver').textContent = evo.bestEverFitness.toFixed(0);
            $('statSpeed').textContent = state.running ? simSpeed.toFixed(0) + 'x' : 'paused'; $('statFps').textContent = fps.toFixed(0);
            infoPanel(); drawChart();
        }
    }
    requestAnimationFrame(frame);
}
if (typeof document !== 'undefined') main();

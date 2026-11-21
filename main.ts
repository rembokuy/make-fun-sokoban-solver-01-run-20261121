// Sokoban solver for make.fun "Build the best Sokoban solver, 21 November 2026".
//
// Idea: a level is a one-cell-wide hallway with one to four small rooms off it
// (each inside a 6x6 slot, one door, 3 or 4 boxes). A box pushed out of a room
// through its door can never be pushed back, so every box stays in its room
// and a level's push-optimal count is the sum of its rooms' optima. The solver
// therefore splits the level into its rooms, solves each room push-optimally
// with A* over pushes, and stitches the room solutions together with plain
// walking through the hallway (walking never adds pushes).
//
// Inside one room a state is the sorted box cells plus the player region
// reachable without pushing. One search step is one push. The heuristic is
// the cheapest assignment of boxes to goals by shortest floor distance
// (ignoring other boxes), which never overestimates: one push moves one box
// by one cell, so it can lower the assignment cost by at most one. Deadlocks
// are pruned early: boxes on statically dead cells (corners, goal-less wall
// runs), 2x2 blocks of walls/boxes with no goal, and boxes frozen between
// walls and frozen boxes.
//
// Work is bounded by a fixed number of expanded states, never by the wall
// clock, so two runs on the same set write the same bytes. Every stitched
// answer is replayed on the level before it is written; a failed replay
// writes an empty answer rather than an illegal one.

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Fixed budget, counted in expanded states, shared by every run.
const ROOM_EXPANSION_CAP = 250000;
const WHOLE_EXPANSION_CAP = 500000;
// Global work budget across the whole run (all instances, all rooms and the
// fallback): once spent, searches give up instead of risking the 60 s wall.
const WORK_BUDGET = 1500000;
let budgetUsed = 0;

interface Dir {
  dx: number;
  dy: number;
  ch: string;
}

const DIRS: readonly Dir[] = [
  { dx: 0, dy: -1, ch: 'u' },
  { dx: 0, dy: 1, ch: 'd' },
  { dx: -1, dy: 0, ch: 'l' },
  { dx: 1, dy: 0, ch: 'r' },
];

interface Level {
  w: number;
  h: number;
  floor: Set<number>;
  goals: Set<number>;
  boxes: number[];
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max.apply(null, rows.map((r) => r.length));
  const floor = new Set<number>();
  const goals = new Set<number>();
  const boxes: number[] = [];
  let player = -1;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const c = rows[y][x] ?? '#';
      if (c === '#') continue;
      const cell = y * w + x;
      floor.add(cell);
      if (c === '.' || c === '*' || c === '+') goals.add(cell);
      if (c === '$' || c === '*') boxes.push(cell);
      if (c === '@' || c === '+') player = cell;
    }
  }
  boxes.sort((a, b) => a - b);
  return { w, h, floor, goals, boxes, player };
}

function cellX(cell: number, w: number): number {
  return cell % w;
}

function cellY(cell: number, w: number): number {
  return Math.floor(cell / w);
}

function step(cell: number, dir: Dir, w: number): number {
  return cell + dir.dy * w + dir.dx;
}

/** Shortest walk (u/d/l/r) from `from` to `to` over cells `pass` accepts. */
function walkPath(
  from: number,
  to: number,
  pass: (cell: number) => boolean,
  w: number,
): string | null {
  if (from === to) return '';
  if (!pass(to)) return null;
  const prev = new Map<number, { at: number; ch: string }>();
  const queue: number[] = [from];
  prev.set(from, { at: -1, ch: '' });
  for (let head = 0; head < queue.length; head++) {
    const cur = queue[head];
    for (const dir of DIRS) {
      const nx = cellX(cur, w) + dir.dx;
      const ny = cellY(cur, w) + dir.dy;
      if (nx < 0 || nx >= w || ny < 0) continue;
      const next = step(cur, dir, w);
      if (prev.has(next) || !pass(next)) continue;
      prev.set(next, { at: cur, ch: dir.ch });
      if (next === to) {
        let out = '';
        let c = next;
        while (c !== from) {
          const p = prev.get(c) as { at: number; ch: string };
          out = p.ch + out;
          c = p.at;
        }
        return out;
      }
      queue.push(next);
    }
  }
  return null;
}

/** BFS distances from one goal over the region's cells, ignoring boxes. */
function distancesFrom(goal: number, cells: Set<number>, w: number): Map<number, number> {
  const dist = new Map<number, number>();
  const queue: number[] = [goal];
  dist.set(goal, 0);
  for (let head = 0; head < queue.length; head++) {
    const cur = queue[head];
    const d = dist.get(cur) as number;
    for (const dir of DIRS) {
      const nx = cellX(cur, w) + dir.dx;
      if (nx < 0 || nx >= w) continue;
      const next = step(cur, dir, w);
      if (!cells.has(next) || dist.has(next)) continue;
      dist.set(next, d + 1);
      queue.push(next);
    }
  }
  return dist;
}

function permutations(n: number): number[][] {
  const out: number[][] = [];
  const cur: number[] = [];
  const used = new Array<boolean>(n).fill(false);
  const build = (): void => {
    if (cur.length === n) {
      out.push(cur.slice());
      return;
    }
    for (let i = 0; i < n; i++) {
      if (used[i]) continue;
      used[i] = true;
      cur.push(i);
      build();
      cur.pop();
      used[i] = false;
    }
  };
  build();
  return out;
}

interface Region {
  w: number;
  cells: Set<number>;
  goals: number[];
  boxes: number[];
  startPlayer: number;
  extraWalk: Set<number>;
  door: number;
  cap: number;
  requireExit: boolean;
}

interface RegionResult {
  moves: string;
  pushes: number;
  finalPlayer: number;
  finalBoxes: number[];
  trapped: boolean;
}

/** A push-optimal A* over one region (a room, or the whole level as fallback). */
function solveRegion(region: Region): RegionResult | null {
  const { w, cells, goals, boxes, startPlayer, extraWalk, door, cap } = region;
  const n = boxes.length;
  if (n === 0) return { moves: '', pushes: 0, finalPlayer: startPlayer, finalBoxes: [], trapped: false };
  const goalSet = new Set<number>(goals);
  const goalList = goals.slice().sort((a, b) => a - b);
  const distByGoal = goalList.map((g) => distancesFrom(g, cells, w));
  // The player may also stand on the extra walk cells (the hallway cell at
  // a room's door). For deadlock purposes those count as open floor: a box
  // on the door can be pushed inward by a player standing in the hallway,
  // so the hallway side of the door is not a wall.
  const open = new Set<number>(cells);
  for (const c of extraWalk) open.add(c);
  const perms = n <= 8 ? permutations(n) : null;

  // Static dead cells: corners and goal-less runs along a wall.
  const dead = new Set<number>();
  const isWall = (cell: number): boolean => !open.has(cell);
  for (const cell of cells) {
    if (goalSet.has(cell)) continue;
    const x = cellX(cell, w);
    const y = cellY(cell, w);
    const up = isWall(cell - w);
    const down = isWall(cell + w);
    const left = isWall(cell - 1);
    const right = isWall(cell + 1);
    if ((up && left) || (up && right) || (down && left) || (down && right)) {
      dead.add(cell);
      continue;
    }
    // Runs along a wall: a box on such a run can only slide along it.
    const runs: { wall: boolean; step: number; across: number }[] = [
      { wall: up, step: 1, across: -w },
      { wall: down, step: 1, across: w },
      { wall: left, step: w, across: -1 },
      { wall: right, step: w, across: 1 },
    ];
    for (const run of runs) {
      if (!run.wall) continue;
      let lo = cell;
      while (cells.has(lo - run.step) && isWall(lo - run.step + run.across)) lo -= run.step;
      let hi = cell;
      while (cells.has(hi + run.step) && isWall(hi + run.step + run.across)) hi += run.step;
      let hasGoal = false;
      for (let c = lo; c <= hi; c += run.step) {
        if (goalSet.has(c)) {
          hasGoal = true;
          break;
        }
      }
      // Dead only when the run holds no goal and the box cannot slide out
      // of it at either end: the cells just past both ends must be walls.
      const endBlocked = (from: number, delta: number): boolean => {
        if (run.step === 1) {
          if (cellX(from, w) + delta < 0 || cellX(from, w) + delta >= w) return true;
        }
        return isWall(from + delta * run.step);
      };
      if (!hasGoal && endBlocked(lo, -1) && endBlocked(hi, 1)) {
        dead.add(cell);
        break;
      }
    }
  }

  const heuristic = (bs: number[]): number => {
    if (perms !== null) {
      let best = Infinity;
      for (const perm of perms) {
        let sum = 0;
        for (let i = 0; i < n; i++) {
          const d = distByGoal[perm[i]].get(bs[i]);
          if (d === undefined) {
            sum = Infinity;
            break;
          }
          sum += d;
        }
        if (sum < best) best = sum;
      }
      return best;
    }
    // Too many boxes to enumerate assignments: sum each box's distance to
    // its nearest goal. Still admissible (goals may be shared), just weaker.
    let sum = 0;
    for (let i = 0; i < n; i++) {
      let d = Infinity;
      for (let j = 0; j < n; j++) {
        const dj = distByGoal[j].get(bs[i]);
        if (dj !== undefined && dj < d) d = dj;
      }
      if (d === Infinity) return Infinity;
      sum += d;
    }
    return sum;
  };

  const reachable = (player: number, boxSet: Set<number>): Set<number> => {
    const seen = new Set<number>();
    if (boxSet.has(player)) return seen;
    const queue: number[] = [player];
    seen.add(player);
    for (let head = 0; head < queue.length; head++) {
      const cur = queue[head];
      for (const dir of DIRS) {
        const nx = cellX(cur, w) + dir.dx;
        if (nx < 0 || nx >= w) continue;
        const next = step(cur, dir, w);
        if (seen.has(next) || boxSet.has(next)) continue;
        if (!cells.has(next) && !extraWalk.has(next)) continue;
        seen.add(next);
        queue.push(next);
      }
    }
    return seen;
  };

  const isDeadState = (bs: number[], boxSet: Set<number>): boolean => {
    for (const b of bs) {
      if (goalSet.has(b)) continue;
      if (dead.has(b)) return true;
      // 2x2 block of walls/boxes with no goal.
      const blocks: number[][] = [
        [b, b + 1, b + w, b + w + 1],
        [b - 1, b, b + w - 1, b + w],
        [b - w, b - w + 1, b, b + 1],
        [b - w - 1, b - w, b - 1, b],
      ];
      for (const block of blocks) {
        let full = true;
        let hasGoal = false;
        for (const c of block) {
          if (goalSet.has(c)) hasGoal = true;
          if (open.has(c) && !boxSet.has(c)) {
            full = false;
            break;
          }
        }
        if (full && !hasGoal) return true;
      }
    }
    // Frozen boxes: cannot move on either axis, blocked only by walls or
    // boxes that are themselves frozen. Least fixpoint, sound by induction.
    const frozen = new Set<number>();
    let changed = true;
    while (changed) {
      changed = false;
      for (const b of bs) {
        if (goalSet.has(b) || frozen.has(b)) continue;
        const blocked = (c: number): boolean => !open.has(c) || frozen.has(c);
        const horiz = blocked(b - 1) && blocked(b + 1);
        const vert = blocked(b - w) && blocked(b + w);
        if (horiz && vert) {
          frozen.add(b);
          changed = true;
        }
      }
    }
    return frozen.size > 0;
  };

  interface State {
    boxes: number[];
    player: number;
    parent: number;
    pushBox: number;
    pushDir: number;
  }

  const keyOf = (bs: number[], canon: number): string => bs.join(',') + '|' + canon;
  const states: State[] = [];
  const startBoxes = boxes.slice().sort((a, b) => a - b);
  const startBoxSet = new Set<number>(startBoxes);
  const startRegion = reachable(startPlayer, startBoxSet);
  if (startRegion.size === 0) return null;
  let startCanon = Infinity;
  for (const c of startRegion) if (c < startCanon) startCanon = c;
  const h0 = heuristic(startBoxes);
  if (h0 === Infinity || isDeadState(startBoxes, startBoxSet)) return null;
  states.push({ boxes: startBoxes, player: startPlayer, parent: -1, pushBox: -1, pushDir: -1 });
  const best = new Map<string, number>();
  best.set(keyOf(startBoxes, startCanon), 0);

  // Binary heap ordered by (f, h, insertion order) for full determinism.
  interface HeapItem {
    f: number;
    h: number;
    seq: number;
    idx: number;
    g: number;
  }
  const heap: HeapItem[] = [];
  let seq = 0;
  const heapLess = (a: HeapItem, b: HeapItem): boolean =>
    a.f !== b.f ? a.f < b.f : a.h !== b.h ? a.h < b.h : a.seq < b.seq;
  const heapPush = (item: HeapItem): void => {
    heap.push(item);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!heapLess(heap[i], heap[p])) break;
      const t = heap[i];
      heap[i] = heap[p];
      heap[p] = t;
      i = p;
    }
  };
  const heapPop = (): HeapItem => {
    const top = heap[0];
    const last = heap.pop() as HeapItem;
    if (heap.length > 0) {
      heap[0] = last;
      let i = 0;
      for (;;) {
        const l = i * 2 + 1;
        const r = l + 1;
        let m = i;
        if (l < heap.length && heapLess(heap[l], heap[m])) m = l;
        if (r < heap.length && heapLess(heap[r], heap[m])) m = r;
        if (m === i) break;
        const t = heap[i];
        heap[i] = heap[m];
        heap[m] = t;
        i = m;
      }
    }
    return top;
  };
  heapPush({ f: h0, h: h0, seq: seq++, idx: 0, g: 0 });

  let expanded = 0;
  let goalIdx = -1;
  let goalTrapped = false;
  while (heap.length > 0) {
    const item = heapPop();
    const state = states[item.idx];
    const boxSet = new Set<number>(state.boxes);
    const regionSet = reachable(state.player, boxSet);
    let canon = Infinity;
    for (const c of regionSet) if (c < canon) canon = c;
    // Stale heap entry: a better path to this same state was found since.
    if ((best.get(keyOf(state.boxes, canon)) as number) < item.g) continue;
    // Goal: every box on a goal, and (when required) the player can leave.
    let solved = true;
    for (const b of state.boxes) {
      if (!goalSet.has(b)) {
        solved = false;
        break;
      }
    }
    if (solved) {
      let canExit = door < 0;
      if (!canExit) {
        if (regionSet.has(door)) canExit = true;
        for (const c of extraWalk) {
          if (regionSet.has(c)) {
            canExit = true;
            break;
          }
        }
      }
      if (canExit || !region.requireExit) {
        goalIdx = item.idx;
        goalTrapped = !canExit;
        break;
      }
      // Solved but trapped and exit required: do not expand, keep searching.
      continue;
    }
    if (expanded >= cap || budgetUsed >= WORK_BUDGET) return null;
    expanded++;
    budgetUsed++;
    for (let bi = 0; bi < n; bi++) {
      const b = state.boxes[bi];
      for (let d = 0; d < 4; d++) {
        const dir = DIRS[d];
        const behind = step(b, DIRS[d ^ 1], w);
        const target = step(b, dir, w);
        if (!regionSet.has(behind)) continue;
        if (!cells.has(target) || boxSet.has(target)) continue;
        const nextBoxes = state.boxes.slice();
        nextBoxes[bi] = target;
        nextBoxes.sort((a, b2) => a - b2);
        const nextBoxSet = new Set<number>(nextBoxes);
        if (isDeadState(nextBoxes, nextBoxSet)) continue;
        const h = heuristic(nextBoxes);
        if (h === Infinity) continue;
        const g = item.g + 1;
        const nextRegion = reachable(b, nextBoxSet);
        let canon = Infinity;
        for (const c of nextRegion) if (c < canon) canon = c;
        const key = keyOf(nextBoxes, canon);
        const prevG = best.get(key);
        if (prevG !== undefined && prevG <= g) continue;
        best.set(key, g);
        if (states.length >= 600000) return null;
        states.push({ boxes: nextBoxes, player: b, parent: item.idx, pushBox: b, pushDir: d });
        heapPush({ f: g + h, h, seq: seq++, idx: states.length - 1, g });
      }
    }
  }
  if (goalIdx < 0) return null;

  // Reconstruct the pushes, then expand each into walk + push.
  const pushes: { box: number; dir: number }[] = [];
  let cur = goalIdx;
  while (states[cur].parent >= 0) {
    pushes.push({ box: states[cur].pushBox, dir: states[cur].pushDir });
    cur = states[cur].parent;
  }
  pushes.reverse();
  let moves = '';
  let curPlayer = startPlayer;
  let curBoxes = startBoxes.slice();
  for (const push of pushes) {
    const dir = DIRS[push.dir];
    const behind = step(push.box, DIRS[push.dir ^ 1], w);
    const boxSetNow = new Set<number>(curBoxes);
    const walk = walkPath(
      curPlayer,
      behind,
      (c) => (cells.has(c) || extraWalk.has(c)) && !boxSetNow.has(c),
      w,
    );
    if (walk === null) return null;
    moves += walk + dir.ch;
    const bi = curBoxes.indexOf(push.box);
    curBoxes[bi] = step(push.box, dir, w);
    curBoxes.sort((a, b) => a - b);
    curPlayer = push.box;
  }
  return {
    moves,
    pushes: pushes.length,
    finalPlayer: curPlayer,
    finalBoxes: curBoxes,
    trapped: goalTrapped,
  };
}

interface Room {
  cells: Set<number>;
  goals: number[];
  boxes: number[];
  door: number;
  hall: number;
}

function solveRoom(room: Room, w: number, requireExit: boolean): RegionResult | null {
  const doorFree = !room.boxes.includes(room.door);
  return solveRegion({
    w,
    cells: room.cells,
    goals: room.goals,
    boxes: room.boxes,
    startPlayer: doorFree ? room.door : room.hall,
    extraWalk: new Set<number>([room.hall]),
    door: room.door,
    cap: ROOM_EXPANSION_CAP,
    requireExit,
  });
}

/** Split a level into hallway row + rooms. Null when the shape is unexpected. */
function findRooms(level: Level): Room[] | null {
  const py = cellY(level.player, level.w);
  const rest = new Set<number>();
  for (const c of level.floor) {
    if (cellY(c, level.w) !== py) rest.add(c);
  }
  const seen = new Set<number>();
  const rooms: Room[] = [];
  const coveredBoxes = new Set<number>();
  const coveredGoals = new Set<number>();
  for (const start of rest) {
    if (seen.has(start)) continue;
    const comp = new Set<number>();
    const queue: number[] = [start];
    seen.add(start);
    comp.add(start);
    for (let head = 0; head < queue.length; head++) {
      const cur = queue[head];
      for (const dir of DIRS) {
        const next = step(cur, dir, level.w);
        if (!rest.has(next) || seen.has(next)) continue;
        seen.add(next);
        comp.add(next);
        queue.push(next);
      }
    }
    const boxes = level.boxes.filter((b) => comp.has(b));
    const goals = [...level.goals].filter((g) => comp.has(g));
    if (boxes.length === 0) {
      if (goals.length > 0) return null;
      continue;
    }
    if (boxes.length !== goals.length) return null;
    const doors: number[] = [];
    for (const c of comp) {
      for (const dir of DIRS) {
        const nb = step(c, dir, level.w);
        if (cellY(nb, level.w) === py && level.floor.has(nb)) {
          doors.push(c);
          break;
        }
      }
    }
    if (doors.length === 0) return null;
    doors.sort((a, b) => a - b);
    const door = doors[0];
    let hall = -1;
    for (const dir of DIRS) {
      const nb = step(door, dir, level.w);
      if (cellY(nb, level.w) === py && level.floor.has(nb)) {
        hall = nb;
        break;
      }
    }
    if (hall < 0) return null;
    for (const b of boxes) coveredBoxes.add(b);
    for (const g of goals) coveredGoals.add(g);
    rooms.push({ cells: comp, goals: goals.sort((a, b) => a - b), boxes, door, hall });
  }
  if (coveredBoxes.size !== level.boxes.length) return null;
  if (coveredGoals.size !== level.goals.size) return null;
  return rooms;
}

/** Replay moves on the level; true only when every box ends on a goal. */
function verify(level: Level, moves: string): boolean {
  const boxes = new Set<number>(level.boxes);
  let player = level.player;
  for (const ch of moves) {
    const dir = DIRS.find((d) => d.ch === ch);
    if (!dir) return false;
    const next = step(player, dir, level.w);
    if (!level.floor.has(next)) return false;
    if (boxes.has(next)) {
      const beyond = step(next, dir, level.w);
      if (!level.floor.has(beyond) || boxes.has(beyond)) return false;
      boxes.delete(next);
      boxes.add(beyond);
    }
    player = next;
  }
  for (const b of boxes) {
    if (!level.goals.has(b)) return false;
  }
  return true;
}

function solveLevel(level: Level): string {
  const rooms = findRooms(level);
  if (rooms !== null) {
    const results: (RegionResult | null)[] = rooms.map((r) => solveRoom(r, level.w, false));
    if (results.every((r) => r !== null)) {
      const trappedCount = results.filter((r) => (r as RegionResult).trapped).length;
      if (trappedCount > 1) {
        // At most one room may end with the player trapped inside; re-solve
        // the others demanding an exit. If that fails, fall through.
        let ok = true;
        for (let i = 0; i < rooms.length; i++) {
          const r = results[i] as RegionResult;
          if (!r.trapped) continue;
          const retry = solveRoom(rooms[i], level.w, true);
          if (retry === null || retry.trapped) {
            // Keep the first trapped room as-is, re-solve the rest.
            const firstTrapped = results.findIndex((x) => (x as RegionResult).trapped);
            if (i !== firstTrapped) {
              ok = false;
              break;
            }
          } else {
            results[i] = retry;
          }
        }
        if (!ok) {
          const fb = solveRegion({
            w: level.w,
            cells: level.floor,
            goals: [...level.goals].sort((a, b) => a - b),
            boxes: level.boxes,
            startPlayer: level.player,
            extraWalk: new Set<number>(),
            door: -1,
            cap: WHOLE_EXPANSION_CAP,
            requireExit: false,
          });
          if (fb !== null && verify(level, fb.moves)) return fb.moves;
          return '';
        }
      }
      // Stitch: non-trapped rooms first (nearest door first), trapped last.
      const order = rooms.map((_, i) => i);
      const globalBoxes = new Set<number>(level.boxes);
      let globalPlayer = level.player;
      const done = new Set<number>();
      let moves = '';
      const walkPass = (c: number): boolean => level.floor.has(c) && !globalBoxes.has(c);
      while (done.size < rooms.length) {
        let bestIdx = -1;
        let bestDist = Infinity;
        for (const i of order) {
          if (done.has(i)) continue;
          const res = results[i] as RegionResult;
          if (res.trapped && done.size < rooms.length - 1) continue;
          const walk = walkPath(globalPlayer, rooms[i].hall, walkPass, level.w);
          const dist = walk === null ? Infinity : walk.length;
          const key = dist * 100000 + rooms[i].door;
          if (bestIdx < 0 || key < bestDist) {
            bestIdx = i;
            bestDist = key;
          }
        }
        if (bestIdx < 0) break;
        const room = rooms[bestIdx];
        const res = results[bestIdx] as RegionResult;
        const walk = walkPath(globalPlayer, room.hall, walkPass, level.w);
        if (walk === null) break;
        moves += walk;
        globalPlayer = room.hall;
        if (!globalBoxes.has(room.door)) {
          const dir = DIRS.find((d) => step(room.hall, d, level.w) === room.door);
          if (!dir) break;
          moves += dir.ch;
          globalPlayer = room.door;
        }
        moves += res.moves;
        for (const b of room.boxes) globalBoxes.delete(b);
        for (const b of res.finalBoxes) globalBoxes.add(b);
        globalPlayer = res.finalPlayer;
        done.add(bestIdx);
      }
      if (done.size === rooms.length && verify(level, moves)) return moves;
    }
  }
  const fb = solveRegion({
    w: level.w,
    cells: level.floor,
    goals: [...level.goals].sort((a, b) => a - b),
    boxes: level.boxes,
    startPlayer: level.player,
    extraWalk: new Set<number>(),
    door: -1,
    cap: WHOLE_EXPANSION_CAP,
    requireExit: false,
  });
  if (fb !== null && verify(level, fb.moves)) return fb.moves;
  return '';
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  const level = parseLevel(readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8'));
  const moves = solveLevel(level);
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'solution.txt'), moves + '\n');
}

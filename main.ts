// Push-optimal Sokoban solver — room decomposition + BFS over pushes.
//
// Idea: the generator builds each level as a 1-wide hallway (the player's row)
// plus 1-4 small rooms off it. A box pushed through a door into the hallway can
// never come back, so every box stays in its own room and the level optimum is
// the sum of the room optima. Each room (3-4 boxes, ~6x6) is solved exactly with
// a breadth-first search over pushes, then the rooms are stitched together by
// walking the player between them. Deterministic: no clock, no randomness, no
// environment-dependent choices; search budgets are counted in states.
//
// Fallbacks, in order: whole-level push BFS, then a move-based A* search, then
// an empty (but always written) solution so no instance is ever unanswered.

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// ---------------------------------------------------------------------------
// Small utilities
// ---------------------------------------------------------------------------

const DIRS = [
  { dx: 0, dy: -1, ch: 'u' },
  { dx: 0, dy: 1, ch: 'd' },
  { dx: -1, dy: 0, ch: 'l' },
  { dx: 1, dy: 0, ch: 'r' },
];

function sortedCopy(arr) {
  const out = arr.slice();
  out.sort((a, b) => a - b);
  return out;
}

// ---------------------------------------------------------------------------
// Level parsing
// ---------------------------------------------------------------------------

// A board: width/height, wall flags (1 = wall), goal flags, box squares and
// the player's square. Short rows are padded with walls; the outer frame is
// forced to wall so nothing can leave the board.
function parseBoard(text) {
  const lines = text.split('\n').filter((row) => row.length > 0);
  const h = lines.length;
  const w = Math.max.apply(null, lines.map((row) => row.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goal = new Uint8Array(w * h);
  const boxes = [];
  let player = -1;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < lines[y].length; x++) {
      const i = y * w + x;
      const c = lines[y][x];
      if (c === '#') continue;
      wall[i] = 0;
      if (c === '.' || c === '*' || c === '+') goal[i] = 1;
      if (c === '$' || c === '*') boxes.push(i);
      if (c === '@' || c === '+') player = i;
    }
  }
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  return { w, h, wall, goal, boxes: sortedCopy(boxes), player };
}

// ---------------------------------------------------------------------------
// Reachability helpers (all iterative, all deterministic)
// ---------------------------------------------------------------------------

// Lowest square of the player's reachable region from `from`, treating
// `blocked` squares as walls. `seen`/`stamp`/`stack` are scratch buffers owned
// by the caller so repeated calls allocate nothing.
function regionLow(board, blocked, from, seen, stamp, stack) {
  const { w, wall } = board;
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    const x = p % w;
    if (p - w >= 0 && !wall[p - w] && !blocked[p - w] && seen[p - w] !== stamp) {
      seen[p - w] = stamp; stack[n++] = p - w;
    }
    if (p + w < wall.length && !wall[p + w] && !blocked[p + w] && seen[p + w] !== stamp) {
      seen[p + w] = stamp; stack[n++] = p + w;
    }
    if (x > 0 && !wall[p - 1] && !blocked[p - 1] && seen[p - 1] !== stamp) {
      seen[p - 1] = stamp; stack[n++] = p - 1;
    }
    if (x + 1 < w && !wall[p + 1] && !blocked[p + 1] && seen[p + 1] !== stamp) {
      seen[p + 1] = stamp; stack[n++] = p + 1;
    }
  }
  return low;
}

// Mark `seen` with `stamp` for every square reachable from `from`.
function floodMark(board, blocked, from, seen, stamp, stack) {
  regionLow(board, blocked, from, seen, stamp, stack);
}

// Squares a lone box can ever be pushed onto some goal: start from the goals
// and walk boxes backwards (a box at square s could have been pushed from the
// square behind it, provided the player could stand there).
function liveSquares(board) {
  const { w, wall, goal } = board;
  const live = new Uint8Array(wall.length);
  const queue = [];
  for (let i = 0; i < wall.length; i++) {
    if (goal[i]) { live[i] = 1; queue.push(i); }
  }
  for (let qi = 0; qi < queue.length; qi++) {
    const s = queue[qi];
    const sx = s % w;
    const sy = Math.floor(s / w);
    for (const d of DIRS) {
      const bx = sx - d.dx;
      const by = sy - d.dy;
      const px = bx - d.dx;
      const py = by - d.dy;
      if (bx < 0 || bx >= w || by < 0 || by >= board.h) continue;
      if (px < 0 || px >= w || py < 0 || py >= board.h) continue;
      const behind = by * w + bx;
      const beyond = py * w + px;
      if (wall[behind] || wall[beyond] || live[behind]) continue;
      // The pull step needs the player to stand beyond the box: `beyond`
      // is that square, and it must be open floor.
      live[behind] = 1;
      queue.push(behind);
    }
  }
  return live;
}

// True when the box just pushed onto `t` is stuck inside a frozen 2x2 block:
// four squares, each wall or box, with at least one box off its goal.
function isFrozen(board, blocked, goal, t) {
  const { w, wall } = board;
  const corners = [t, t - 1, t - w, t - w - 1];
  for (const a of corners) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (a < 0 || d >= wall.length) continue;
    const cells = [a, b, c, d];
    let solid = true;
    for (const s of cells) {
      if (!wall[s] && !blocked[s]) { solid = false; break; }
    }
    if (!solid) continue;
    for (const s of cells) {
      if (blocked[s] && !goal[s]) return true;
    }
  }
  return false;
}

// ---------------------------------------------------------------------------
// Push-optimal BFS over one board
// ---------------------------------------------------------------------------
//
// State = sorted box squares + the player's reachable region (named by its
// lowest square). States are expanded in push order, so the first solved state
// found is push-optimal. Returns { pushes, moves } (lowercase u/d/l/r, pushes
// included as ordinary steps) or null when the state budget runs out or the
// board is unsolvable.

const MAX_PUSH_STATES = 400000;

function solvePushes(board, maxStates) {
  const { w, wall, goal } = board;
  const size = wall.length;
  const live = liveSquares(board);
  for (const b of board.boxes) if (!live[b]) return null;

  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  const blocked = new Uint8Array(size);
  let stamp = 0;

  // State storage: parallel arrays, queue order = push order (plain BFS).
  const stateBoxes = [board.boxes.slice()];
  const statePlayer = [board.player];
  const stateParent = [-1];
  const statePush = [-1]; // direction index of the push that created the state
  const visited = new Set();
  for (const b of board.boxes) blocked[b] = 1;
  const startLow = regionLow(board, blocked, board.player, seen, ++stamp, stack);
  for (const b of board.boxes) blocked[b] = 0;
  visited.add(stateBoxes[0].join(',') + '|' + startLow);

  const allOnGoal = (boxes) => {
    for (const b of boxes) if (!goal[b]) return false;
    return true;
  };

  let found = allOnGoal(board.boxes) ? 0 : -1;
  for (let head = 0; found < 0 && head < stateBoxes.length; head++) {
    const boxes = stateBoxes[head];
    for (const b of boxes) blocked[b] = 1;
    floodMark(board, blocked, statePlayer[head], seen, ++stamp, stack);
    const reachStamp = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (let di = 0; di < 4; di++) {
        const d = DIRS[di];
        const step = d.dy * w + d.dx;
        const from = b - step; // square the player must stand on to push
        const to = b + step; // square the box moves to
        if (to < 0 || to >= size || from < 0 || from >= size) continue;
        if (seen[from] !== reachStamp) continue;
        if (wall[to] || blocked[to] || !live[to]) continue;
        blocked[b] = 0;
        blocked[to] = 1;
        const frozen = isFrozen(board, blocked, goal, to);
        let key = '';
        let nextBoxes = null;
        if (!frozen) {
          nextBoxes = boxes.slice();
          nextBoxes[bi] = to;
          nextBoxes.sort((a, c) => a - c);
          const low = regionLow(board, blocked, b, mark, ++stamp, stack);
          key = nextBoxes.join(',') + '|' + low;
        }
        blocked[to] = 0;
        blocked[b] = 1;
        if (frozen || visited.has(key)) continue;
        if (stateBoxes.length >= maxStates) {
          for (const x of boxes) blocked[x] = 0;
          return null;
        }
        visited.add(key);
        stateBoxes.push(nextBoxes);
        statePlayer.push(b);
        stateParent.push(head);
        statePush.push(di);
        if (allOnGoal(nextBoxes)) { found = stateBoxes.length - 1; break; }
      }
    }
    for (const x of boxes) blocked[x] = 0;
  }
  if (found < 0) return null;

  // Rebuild the push chain, then turn each push into concrete moves: walk the
  // player to the pushing square (shortest path around walls and boxes), then
  // step into the box.
  const chain = [];
  for (let s = found; s > 0; s = stateParent[s]) chain.push(s);
  chain.reverse();
  let moves = '';
  let player = board.player;
  let boxes = board.boxes.slice();
  for (const s of chain) {
    const nextBoxes = stateBoxes[s];
    let movedFrom = -1;
    let movedTo = -1;
    const oldSet = new Set(boxes);
    const newSet = new Set(nextBoxes);
    for (const b of boxes) if (!newSet.has(b)) movedFrom = b;
    for (const b of nextBoxes) if (!oldSet.has(b)) movedTo = b;
    const di = statePush[s];
    const step = DIRS[di].dy * w + DIRS[di].dx;
    const standOn = movedFrom - step;
    for (const b of boxes) blocked[b] = 1;
    moves += shortestWalk(board, blocked, player, standOn);
    for (const b of boxes) blocked[b] = 0;
    moves += DIRS[di].ch;
    player = movedFrom;
    boxes = nextBoxes;
  }
  return { pushes: chain.length, moves };
}

// Shortest walk (lowercase letters) from `from` to `to` around walls and the
// squares flagged in `blocked`. Ties break by direction order, so the walk is
// deterministic.
function shortestWalk(board, blocked, from, to) {
  const { w, wall } = board;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    const x = p % w;
    for (const d of DIRS) {
      const q = p + d.dy * w + d.dx;
      if (q < 0 || q >= wall.length) continue;
      if ((d.dx === -1 && x === 0) || (d.dx === 1 && x === w - 1)) continue;
      if (wall[q] || blocked[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = d.ch;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('push square out of reach');
  let out = '';
  for (let p = to; p !== from; p = prev[p]) out = how[p] + out;
  return out;
}

// Square the player ends on after walking `moves` from `from`.
function endSquare(w, from, moves) {
  let p = from;
  for (const ch of moves) {
    if (ch === 'u') p -= w;
    else if (ch === 'd') p += w;
    else if (ch === 'l') p -= 1;
    else if (ch === 'r') p += 1;
  }
  return p;
}

// ---------------------------------------------------------------------------
// Room decomposition
// ---------------------------------------------------------------------------
//
// Cut the hallway row's dead squares (floor the player walks on, but from
// which no box can ever reach a goal) out of the floor. Each remaining
// connected component holding boxes is one room. Returns the rooms (each with
// its boxes and goals) or null when the level is not a clean set of rooms.

function splitRooms(board) {
  const { w, wall, goal } = board;
  const live = liveSquares(board);
  const hallRow = Math.floor(board.player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = hallRow * w; i < (hallRow + 1) * w; i++) {
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  for (const b of board.boxes) if (cut[b]) return null;

  const comp = new Int32Array(wall.length).fill(-1);
  const rooms = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || comp[s] >= 0) continue;
    const id = rooms.length;
    const members = [s];
    comp[s] = id;
    for (let i = 0; i < members.length; i++) {
      const p = members[i];
      const x = p % w;
      const neighbours = [];
      if (p - w >= 0) neighbours.push(p - w);
      if (p + w < wall.length) neighbours.push(p + w);
      if (x > 0) neighbours.push(p - 1);
      if (x + 1 < w) neighbours.push(p + 1);
      for (const q of neighbours) {
        if (!wall[q] && !cut[q] && comp[q] < 0) { comp[q] = id; members.push(q); }
      }
    }
    rooms.push({ boxes: [], goals: [] });
  }
  for (const b of board.boxes) {
    if (comp[b] < 0) return null;
    rooms[comp[b]].boxes.push(b);
  }
  for (let g = 0; g < wall.length; g++) {
    if (goal[g]) {
      if (comp[g] < 0) return null;
      rooms[comp[g]].goals.push(g);
    }
  }
  for (const r of rooms) {
    if (r.boxes.length !== r.goals.length) return null;
  }
  return rooms.filter((r) => r.boxes.length > 0);
}

// Solve room by room: other rooms' boxes act as walls (a finished room's boxes
// sit on its goals, so its goals act as walls instead). The player walks on
// from wherever the previous room left it.
function solveByRooms(board) {
  const rooms = splitRooms(board);
  if (rooms === null) return solvePushes(board, MAX_PUSH_STATES);
  let player = board.player;
  let pushes = 0;
  let moves = '';
  for (const room of rooms) {
    const wall = board.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      const blockers = other.done ? other.goals : other.boxes;
      for (const b of blockers) wall[b] = 1;
    }
    const sub = {
      w: board.w,
      h: board.h,
      wall,
      goal: null,
      boxes: sortedCopy(room.boxes),
      player,
    };
    // Only this room's goals count: mask the goal flags to the room's own.
    const roomGoal = new Uint8Array(board.goal.length);
    for (const g of room.goals) roomGoal[g] = 1;
    sub.goal = roomGoal;
    const solved = solvePushes(sub, MAX_PUSH_STATES);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    player = endSquare(board.w, player, solved.moves);
    room.done = true;
  }
  return { pushes, moves };
}

// ---------------------------------------------------------------------------
// Fallback: move-based A* (plain, own implementation)
// ---------------------------------------------------------------------------
//
// State = sorted boxes + player square. Heuristic: sum over boxes of the
// Manhattan distance to the nearest goal — admissible, since one step moves at
// most one box by one square. Used only if the push searches fail.

function solveAStar(board, maxExpand) {
  const { w, wall, goal } = board;
  const size = wall.length;
  const goalList = [];
  for (let i = 0; i < size; i++) if (goal[i]) goalList.push(i);
  const gx = goalList.map((g) => g % w);
  const gy = goalList.map((g) => Math.floor(g / w));

  const heuristic = (boxes) => {
    let sum = 0;
    for (const b of boxes) {
      const bx = b % w;
      const by = Math.floor(b / w);
      let best = Infinity;
      for (let gi = 0; gi < goalList.length; gi++) {
        const d = Math.abs(bx - gx[gi]) + Math.abs(by - gy[gi]);
        if (d < best) best = d;
      }
      sum += best;
    }
    return sum;
  };

  // Tiny binary heap of [f, order, stateIndex], ordered by f then insertion.
  const heap = [];
  const heapPush = (item) => {
    heap.push(item);
    let i = heap.length - 1;
    while (i > 0) {
      const parent = (i - 1) >> 1;
      if (heap[parent][0] < heap[i][0] || (heap[parent][0] === heap[i][0] && heap[parent][1] <= heap[i][1])) break;
      const tmp = heap[parent]; heap[parent] = heap[i]; heap[i] = tmp;
      i = parent;
    }
  };
  const heapPop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      let i = 0;
      for (;;) {
        const left = i * 2 + 1;
        const right = left + 1;
        let smallest = i;
        if (left < heap.length && (heap[left][0] < heap[smallest][0] || (heap[left][0] === heap[smallest][0] && heap[left][1] < heap[smallest][1]))) smallest = left;
        if (right < heap.length && (heap[right][0] < heap[smallest][0] || (heap[right][0] === heap[smallest][0] && heap[right][1] < heap[smallest][1]))) smallest = right;
        if (smallest === i) break;
        const tmp = heap[smallest]; heap[smallest] = heap[i]; heap[i] = tmp;
        i = smallest;
      }
    }
    return top;
  };

  const startBoxes = board.boxes.slice();
  const startKey = startBoxes.join(',') + '|' + board.player;
  const nodes = [{ boxes: startBoxes, player: board.player, parent: -1, move: '' }];
  const cost = new Map();
  cost.set(startKey, 0);
  let order = 0;
  heapPush([heuristic(startBoxes), order++, 0]);
  const solvedIdx = (boxes) => {
    for (const b of boxes) if (!goal[b]) return false;
    return true;
  };
  let found = solvedIdx(startBoxes) ? 0 : -1;
  let expanded = 0;
  while (heap.length > 0 && found < 0) {
    const [, , idx] = heapPop();
    const node = nodes[idx];
    const g = cost.get(node.boxes.join(',') + '|' + node.player);
    if (expanded++ >= maxExpand) return null;
    const boxSet = new Set(node.boxes);
    for (const d of DIRS) {
      const step = d.dy * w + d.dx;
      const np = node.player + step;
      if (np < 0 || np >= size) continue;
      const px = node.player % w;
      if ((d.dx === -1 && px === 0) || (d.dx === 1 && px === w - 1)) continue;
      if (wall[np]) continue;
      let nextBoxes = node.boxes;
      let nextPlayer = np;
      if (boxSet.has(np)) {
        const beyond = np + step;
        if (beyond < 0 || beyond >= size || wall[beyond] || boxSet.has(beyond)) continue;
        nextBoxes = node.boxes.slice();
        nextBoxes[nextBoxes.indexOf(np)] = beyond;
        nextBoxes.sort((a, b) => a - b);
      }
      const key = nextBoxes.join(',') + '|' + nextPlayer;
      const ng = g + 1;
      if (cost.has(key) && cost.get(key) <= ng) continue;
      cost.set(key, ng);
      nodes.push({ boxes: nextBoxes, player: nextPlayer, parent: idx, move: d.ch });
      if (solvedIdx(nextBoxes)) { found = nodes.length - 1; break; }
      heapPush([ng + heuristic(nextBoxes), order++, nodes.length - 1]);
    }
  }
  if (found < 0) return null;
  let moves = '';
  for (let s = found; s > 0; s = nodes[s].parent) moves = nodes[s].move + moves;
  return { pushes: -1, moves };
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

function solveLevel(text) {
  const board = parseBoard(text);
  if (board.player < 0 || board.boxes.length === 0) return '';
  const byRooms = solveByRooms(board);
  if (byRooms !== null) return byRooms.moves;
  const whole = solvePushes(board, MAX_PUSH_STATES);
  if (whole !== null) return whole.moves;
  const astar = solveAStar(board, 300000);
  if (astar !== null) return astar.moves;
  return '';
}

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(INPUT_DIR).sort()) {
  let moves = '';
  try {
    moves = solveLevel(readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8'));
  } catch {
    moves = '';
  }
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'solution.txt'), moves + '\n');
}

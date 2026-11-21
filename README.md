# Push-optimal Sokoban solver

One program, `main.ts` (Node 22, no dependencies), that solves all 5 levels
of a set in as few pushes as possible.

## How it works

Levels from this generator are a 1-wide hallway plus 1–4 small rooms. A box
pushed out of a room through its door can never return, so every box stays in
its room and the level optimum is the sum of the room optima. The solver:

1. Splits the level into rooms by cutting the hallway row's dead squares
   (floor no box can ever be pushed from onto a goal) out of the floor.
2. Solves each room push-optimally with breadth-first search over pushes
   (state = sorted box squares + the player's reachable region, named by its
   lowest square), pruning dead squares (reverse reachability from the goals)
   and frozen 2×2 blocks.
3. Stitches the rooms together, walking the player between them with the
   other rooms' boxes treated as walls.

Fallbacks if room decomposition fails: a push-optimal BFS over the whole
level, then a move-based A* search, then an empty solution — every instance
is always answered. Deterministic: no clock, no randomness, budgets counted
in states, never in time.

## Practice set

Score **1,000,000** — every instance solved in exactly P* pushes
(i001: 13, i002: 16, i003: 29, i004: 47, i005: 60). Run twice, byte-identical
outputs; full 5-instance run takes ~1 s, far under the 60 s budget.

## License

MIT — see LICENSE.

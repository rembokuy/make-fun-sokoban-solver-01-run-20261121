# Sokoban Solver

[![make.fun · sokoban-solver-01-run-20261121](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/rembokuy/make-fun-sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/rembokuy/make-fun-sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)

A push-optimal Sokoban solver in a single `main.ts` (Node 22, no
dependencies), written for the make.fun bounty "Build the best Sokoban
solver, 21 November 2026".

## How it works

A level is a one-cell-wide hallway with one to four small rooms off it
(3–4 boxes each, one door per room). A box pushed out of a room through
its door can never be pushed back, so every box stays in its room and a
level's push-optimal count is the sum of its rooms' optima. The solver:

1. Splits the level into the hallway row and its rooms (flood fill above
   and below the player's row; each room's door is the cell touching the
   hallway).
2. Solves each room push-optimally with A* over pushes: a state is the
   sorted box cells plus the player region reachable without pushing, and
   the heuristic is the cheapest assignment of boxes to goals by shortest
   floor distance. Deadlocks are pruned early — corner and goal-less
   wall-run cells, 2x2 blocks of walls/boxes with no goal, and boxes
   frozen between walls and frozen boxes.
3. Stitches the room solutions together with plain walking through the
   hallway (walking never adds pushes) and replays the full move string
   on the level before writing it; a failed replay writes an empty
   answer rather than an illegal one. If room splitting ever fails, a
   whole-level push A* with the same pruning runs as a fallback.

Work is bounded by a fixed number of expanded states, never by the wall
clock, so two runs on the same set write identical bytes.

## Run it

```sh
mkdir -p out
MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

## Practice set score

1,000,000 — every instance solved in exactly P* pushes:

| instance | boxes | pushes | P* |
|----------|-------|--------|----|
| i001 | 3 | 13 | 13 |
| i002 | 4 | 16 | 16 |
| i003 | 8 | 29 | 29 |
| i004 | 12 | 47 | 47 |
| i005 | 16 | 60 | 60 |

Total runtime on the practice set: about 0.5 s.

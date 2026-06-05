# Long-running N=4 dimension-2 executions

Built by the repair-clock theory: fully-synced dim-2 blocks (star `B1`, two-pairs `B9`) stacked through repairing-sync connectors so the whole execution keeps an exact **2-coordinate clock** no matter how long it runs. Every file is **z3-verified dim 2**. Generator: `gen_long_examples.py`.

| file | syncs | events | construction |
|---|---|---|---|
| `N4_long_repeatstar_x3_01.yaml` | 15 | 49 | repeated star, identity seams |
| `N4_long_repeatstar_x6_02.yaml` | 30 | 94 | repeated star, identity seams |
| `N4_long_repeatstar_x10_03.yaml` | 50 | 154 | repeated star, identity seams |
| `N4_long_hetchain_b1b9_01.yaml` | 40 | 124 | B1/B9 alternating, repaired |
| `N4_long_rotstar_x5_01.yaml` | 30 | 94 | rotating-star, crossings repaired |
| `N4_long_rotstar_x8_02.yaml` | 48 | 148 | rotating-star, crossings repaired |

All verified in 700.5s by `clock_check_syncs` (z3: poset = intersection of two linear extensions, AND the rank-pair clock reproduces happened-before exactly).

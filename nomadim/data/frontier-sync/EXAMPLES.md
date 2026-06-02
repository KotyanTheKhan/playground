# Landmark example executions

A saved, dimension-verified execution for each interesting finding. Every file
is a runnable `nomadim` execution document with `meta.dimension`; dimensions
marked "z3" are verified by the SMT oracle (`confirm_dim.py`), the others by
`nomadim dimension`. See `FINDINGS.md` for the full discussion and `SUMMARY.md`
for the N=2..5 minimum-per-dimension dataset.

## Finding 1 — order dimension is non-monotone in the number of synchronizations

A higher dimension can be reached with *fewer* syncs; adding a sync can lower the
dimension.

| pair | file | S | dim |
|------|------|---|-----|
| N=4 cheap & high-dim | `N4_S4_dim3_real1000cap_01.yaml` | 4 | 3 |
| N=4 costlier & lower-dim | `N4_S5_dim2_real4_01.yaml` | 5 | 2 |
| N=5 cheap & high-dim | `N5_S6_dim3_real1000cap_01.yaml` | 6 | 3 |
| N=5 costlier & lower-dim | `N5_S7_dim2_real4_01.yaml` | 7 | 2 |

## Finding 2 — maximum order dimension grows 2 -> 3 -> 4 with N

The largest dimension any fully frontier-synchronized execution of N processes
attains. Far below the vector-clock ceiling of N.

| N | max dim | example file | S |
|---|---------|--------------|---|
| 2 | 2 | `N2_S1_dim2_real2_01.yaml` | 1 |
| 3 | 2 | `N3_S3_dim2_real4_01.yaml` | 3 |
| 4 | 3 | `N4_S4_dim3_real1000cap_01.yaml` | 4 |
| 5 | 3 | `N5_S6_dim3_real1000cap_01.yaml` | 6 |
| 6 | 3 | `N6_S8_dim3_z3_01.yaml` | 8 |
| 7 | **4** | `N7_S11_dim4_z3_01.yaml` | 11 |

## Finding 3 — at N=7 the max dimension is one sync ABOVE the gossip minimum

For N <= 6 the maximum dimension is attained at the minimum-sync (gossip = 2N-4)
layer. N=7 is different: its gossip-minimum S=10 executions are only dimension 3;
dimension 4 first appears at S=11.

| file | S | dim | role |
|------|---|-----|------|
| `N7_S10_dim3_z3_01.yaml` | 10 | 3 | gossip-optimal minimum -> only dim 3 |
| `N7_S11_dim4_z3_01.yaml` | 11 | 4 | minimum S that reaches dim 4 |
| `N7_S12_dim4_z3_01.yaml` | 12 | 4 | another dim-4 example |

## Cautionary example — "slow to brute-force-color" is not high dimension

`N6_S8_dim3_z3_01.yaml`: 65+ critical pairs; nomadim's exact colorer does not
3-color it within minutes (it looked like a dimension-4 candidate), yet z3 proves
it dimension 3 in milliseconds. Use the z3 oracle, not wall-clock, to judge
dimension for the larger posets.

## Reproduce

- `generate.py` — N=2..5 minimum-per-dimension dataset.
- `classify_z3.py <multidoc>` / `confirm_dim.py <exec> <t>` — z3 dimension oracle.
- `hunt_n7.py`, `min_s_dim4.py`, `constructive_s10.py` — N=7 dimension-4 search.

# Composition examples — legend (how the files relate)

All files are **executions** (`execution:` form: `n_procs` + an ordered list of
pairwise syncs). Every execution here is **fully frontier-synchronized** and every
dimension is **verified with `nomadim dimension`** (the `--le 2` / `--max-cpairs`
flags for the larger ones). A `sync(p,q)` is an X-cross rendezvous that weaves two
timelines; `dim 2` = the order needs only two timelines, `dim 3` = three.

The central question: **compose two or more dim-2 executions by a frontier — when
does the result stay dim 2?**

## File families

```
 COMPOSITE  (the whole execution)          ──made of──▶  its PARTS (constituent sub-executions)

 ── dim raised to 3 (DISJOINT blocks + a bridge frontier) ───────────────────────
 01_two_pairs_cross_dim3.yaml      (N=4, dim 3)   =  01_partA_pair01      (pair {0,1}, dim 2)
                                                  ⊕  01_partB_pair23      (pair {2,3}, dim 2)
                                                  ⊕  01_frontier_cross    (frontier [0,2][1,3], dim 2)
 03_N5_lean_dim3.yaml              (N=5, dim 3)   =  03_partA_cluster012  (cluster {0,1,2}, dim 2)
                                                  ⊕  03_partB_pair34      (pair {3,4}, dim 2)
                                                  ⊕  03_frontier          (frontier [0,3][2,4], dim 2)

 ── dim kept at 2 (coordinator / balanced merge) ────────────────────────────────
 02_coordinator_balanced_dim2.yaml (N=4, dim 2)   =  02_partA_fanout (dim 2) ⊕ 02_partB_fanin (dim 2)
 04_N5_balanced_dim2.yaml          (N=5, dim 2)   =  04_partA_fanout (dim 2) ⊕ 04_partB_fanin (dim 2)

 ── dim kept at 2 (compose 4-PROCESS dim-2 executions via a SHARED HUB) ──────────
 10_two_coords_sharedhub_dim2.yaml   (N=7,  dim 2) =  10_partA_coord_0123 (4-proc coord, dim 2)
                                                   ⊕  10_partB_coord_0456 (4-proc coord, dim 2)
                                                      (blocks share hub = process 0)
 11_three_coords_sharedhub_dim2.yaml (N=10, dim 2) =  11_partA_coord_0123 (4-proc coord, dim 2)
                                                   ⊕  11_partB_coord_0456 (4-proc coord, dim 2)
                                                   ⊕  11_partC_coord_0789 (4-proc coord, dim 2)
                                                      (all blocks share hub = process 0)
```

## The legend, in one table

| Composite | N | dim | composed of | how the parts are joined |
|-----------|---|-----|-------------|--------------------------|
| `01_two_pairs_cross_dim3` | 4 | **3** | `01_partA_pair01`, `01_partB_pair23` | + `01_frontier_cross` (disjoint pairs, **cross** bridge) |
| `02_coordinator_balanced_dim2` | 4 | **2** | `02_partA_fanout`, `02_partB_fanin` | coordinator fan-out then fan-in |
| `03_N5_lean_dim3` | 5 | **3** | `03_partA_cluster012`, `03_partB_pair34` | + `03_frontier` (disjoint blocks, **lean** bridge) |
| `04_N5_balanced_dim2` | 5 | **2** | `04_partA_fanout`, `04_partB_fanin` | coordinator fan-out then fan-in |
| `10_two_coords_sharedhub_dim2` | 7 | **2** | `10_partA_coord_0123`, `10_partB_coord_0456` | two 4-proc coordinators **sharing the hub** |
| `11_three_coords_sharedhub_dim2` | 10 | **2** | `11_partA/B/C_coord_*` | three 4-proc coordinators **sharing the hub** |

Every `part*` / `frontier*` file is itself **dim 2**. Only the *full* compositions
`01` and `03` reach **dim 3**.

## The takeaway

Composing dimension-2 executions does **not** automatically stay dimension 2 — it
depends entirely on the connecting frontier:

- **Disjoint blocks joined by a lean/cross bridge → dim 3** (`01`, `03`). Scarce
  cross-meetings funnel all causality through a few hub events; that skew needs a
  third timeline.
- **Joined through a balanced coordinator / shared hub → dim 2** (`02`, `04`, and
  the 4-process examples `10`, `11`). A single hub that gathers from everyone and
  scatters back to everyone keeps the order grid-like, so two timelines suffice —
  for **any** number of 4-process coordinator blocks.

So: **two (or more) 4-process dim-2 executions compose to a dim-2 execution
exactly when they are stitched through a common coordinator** (`10`, `11`); stitch
them as independent blocks with a cross frontier and the dimension jumps to 3
(`01`). This is the execution-level face of the non-monotonicity in
`../frontier-sync/FINDINGS.md` (*more / better-balanced synchronization → lower
dimension*), and the structural cousin of the abstract antichain dichotomy in
`execution/FrontierCompose.v` (`threshold_dim_le2` vs the S₃ crown).

*(Dimensions verified with the `nomadim` CLI; the larger composites use
`nomadim dimension --le 2 --max-cpairs 600 --max-vertices 600 <file>`, which is the
cheap "is it dimension ≤ 2?" test.)*

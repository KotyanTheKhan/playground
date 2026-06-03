# Composing fully-synced executions by a frontier

These are **executions** (`execution:` form — `n_procs` + an ordered list of
pairwise syncs/meetings), not abstract posets. Each is **fully frontier
synchronized** (every process's start precedes every process's last event) and
each dimension below is **verified with `nomadim dimension`**. Open them in the
nomadim editor (swimlane / execution view, or expand to the poset) and press
*Compute dimension* to confirm.

The question: take two (or more) synchronized blocks and connect them by a
**frontier** of meetings — when does the composite stay dimension 2?

| File | What it composes | dim | Verified |
|------|------------------|-----|----------|
| `01_two_pairs_cross_dim3.yaml` | two synced pairs `{0,1}`,`{2,3}` joined by a **cross** frontier `[0,2],[1,3]` (minimal 4-sync) | **3** | `nomadim dimension` |
| `02_coordinator_balanced_dim2.yaml` | same 4 processes, synchronized through a **coordinator** (hub) — one extra sync | **2** | `nomadim dimension --max-vertices` |
| `03_N5_lean_dim3.yaml` | 5 processes, **lean** minimum (6-sync) merge | **3** | `nomadim dimension --max-vertices` |
| `04_N5_balanced_dim2.yaml` | 5 processes, **balanced** coordinator (7-sync) | **2** | `nomadim dimension --max-vertices` |

## The finding (counterintuitive)

Composing two **dimension-2** blocks does **not** automatically stay dimension 2.
The *cheapest* way to fully synchronize — a lean cross-merge (`01`, `03`) — is the
**most tangled** (dimension **3**): scarce meetings funnel all the causality
through a few hub events, a skewed pattern that needs a third timeline. Spending
**one extra sync** to route the synchronization through a balanced **coordinator**
(`02`, `04`) makes the order grid-like, and the dimension drops back to **2**.

> **More gossip → less tangle.** Minimizing syncs and minimizing dimension are
> competing goals. (This is Finding 1 of `../frontier-sync/FINDINGS.md`; the
> N≤6 max dimension is 3 and dimension 4 first appears at N=7.)

Note the contrast with the *abstract* antichain picture (`execution/FrontierCompose.v`,
the `threshold_dim_le2` / crown dichotomy): there, a single bipartite frontier
between two flat antichains stays dim 2 unless it is a crossing S₃. Here, each
sync is an **X-cross that weaves two timelines** (not a flat edge), so the merge
geometry is richer — and the lean merge is already dim 3 well before any S₃-style
crossing. The two models answer the same question ("does the connecting frontier
keep dimension low?") in their own settings.

Building blocks (already in `../frontier-sync/`): `N2_S1_dim2_real2_01.yaml`
(two processes, dim 2) and `N3_S3_dim2_real4_02.yaml` (three processes, dim 2) are
the small fully-synced atoms these larger executions compose.

## Constituent parts (what each composite is built from)

For every composite, the pieces it is composed of are shipped as separate
`NN_part*` / `NN_frontier*` files (same process space, the relevant subset of
syncs in their original relative order). **Every part is itself dimension 2** —
only the *full* lean compositions (`01`, `03`) reach dimension 3.

| Composite | = parts (⊕ in sync order) | each part's dim |
|-----------|---------------------------|-----------------|
| `01_two_pairs_cross_dim3` (dim 3) | `01_partA_pair01` ⊕ `01_partB_pair23` ⊕ `01_frontier_cross` | 2, 2, 2 |
| `02_coordinator_balanced_dim2` (dim 2) | `02_partA_fanout` ⊕ `02_partB_fanin` | 2, 2 |
| `03_N5_lean_dim3` (dim 3) | `03_partA_cluster012` ⊕ `03_partB_pair34` ⊕ `03_frontier` (interleaved) | 2, 2, 2 |
| `04_N5_balanced_dim2` (dim 2) | `04_partA_fanout` ⊕ `04_partB_fanin` | 2, 2 |

So in `01`/`03` you can watch the tangle appear: two dim-2 blocks and a dim-2
connecting frontier, each harmless alone, combine into a dim-3 whole. In `02`/`04`
the two dim-2 phases combine and stay dim 2. (For `03` the block and frontier syncs
are interleaved in time; the part files show *which* processes meet, the composite
file gives the exact order.)

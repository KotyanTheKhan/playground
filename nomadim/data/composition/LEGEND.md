# Composition examples — legend (how the files relate)

All files are **executions** (`execution:` form: `n_procs` + an ordered list of
pairwise syncs). Each is **fully frontier-synchronized** and every dimension is
**verified with the `nomadim` CLI** (`dimension`, or `dimension --le 2
--max-cpairs 800 --max-vertices 800 <file>` — the cheap "is it ≤ 2?" test — for the
bigger ones). A `sync(p,q)` is an X-cross rendezvous weaving two timelines.

**Central question:** compose two (or more) dimension-2 executions by a frontier —
**when does the result stay dimension 2?**

## Folder layout

```
composition/
  LEGEND.md                         <- this file
  4proc-blocks-to-dim2/             <- the headline: compose 4-PROCESS dim-2 execs -> dim-2 exec
    disjoint-two-coords-hubbridge-N8/   two DISJOINT 4-proc coords + hub bridge   (dim 2)
    two-coords-sharedhub-N7/            two 4-proc coords sharing the hub          (dim 2)
    three-coords-sharedhub-N10/         three 4-proc coords sharing the hub        (dim 2)
    four-coords-sharedhub-N13/          four 4-proc coords sharing the hub         (dim 2)
  small-compositions/               <- didactic N=4,5 (where dim CAN jump to 3)
    two-pairs-cross-dim3/               two pairs + CROSS bridge                   (dim 3)
    coordinator-balanced-dim2/          coordinator fan-out/fan-in                 (dim 2)
    n5-lean-dim3/                       cluster + pair, lean bridge                (dim 3)
    n5-balanced-dim2/                   coordinator fan-out/fan-in                 (dim 2)
```

Every example is **one folder** = a `composite.yaml` + its constituent
`block-*` / `part-*` / `frontier-*` files. Open any folder in the nomadim editor.

## Each composite and what it is built from

### `4proc-blocks-to-dim2/` — composing 4-process dim-2 executions into a dim-2 execution

| Folder | N | dim | composite = parts | how joined |
|--------|---|-----|-------------------|-----------|
| `disjoint-two-coords-hubbridge-N8` | 8 | **2** | `block-A-coord-0123` ⊕ `block-B-coord-4567` ⊕ `frontier-hubbridge` | two **disjoint** 4-proc coordinators, joined **hub-to-hub** `[0,4]` |
| `two-coords-sharedhub-N7` | 7 | **2** | `block-A-coord-0123` ⊕ `block-B-coord-0456` | two 4-proc coordinators **sharing the hub** (proc 0) |
| `three-coords-sharedhub-N10` | 10 | **2** | `block-A/B/C-coord-*` | three 4-proc coordinators sharing the hub |
| `four-coords-sharedhub-N13` | 13 | **2** | `block-A/B/C/D-coord-*` | four 4-proc coordinators sharing the hub |

Every `block-*` is itself a **4-process dim-2 coordinator** (verified). The
shared-hub (star) composition keeps dim 2 for **any** number of blocks
(N = 7, 10, 13 all verified); the disjoint hub-bridge keeps dim 2 too.

### `small-compositions/` — the didactic contrast (dim can jump to 3)

| Folder | N | dim | composite = parts | how joined |
|--------|---|-----|-------------------|-----------|
| `two-pairs-cross-dim3` | 4 | **3** | `part-A-pair01` ⊕ `part-B-pair23` ⊕ `frontier-cross` | disjoint pairs, **cross** bridge `[0,2][1,3]` |
| `coordinator-balanced-dim2` | 4 | **2** | `part-A-fanout` ⊕ `part-B-fanin` | coordinator fan-out then fan-in |
| `n5-lean-dim3` | 5 | **3** | `part-A-cluster012` ⊕ `part-B-pair34` ⊕ `frontier` | disjoint blocks, **lean** bridge |
| `n5-balanced-dim2` | 5 | **2** | `part-A-fanout` ⊕ `part-B-fanin` | coordinator fan-out then fan-in |

Here too every `part-*` / `frontier-*` is dim 2; only the *full* lean/cross
compositions reach dim 3.

## The rule (the whole point)

Composing dimension-2 executions does **not** automatically stay dimension 2 — it
is decided by the connecting frontier:

- **Disjoint blocks + a CROSS bridge → dim 3** (`two-pairs-cross-dim3`,
  `n5-lean-dim3`). Cross meetings interlock the two halves so no two timelines
  suffice.
- **Joined through a HUB — shared or bridged — → dim 2.** Whether the blocks
  *share* a coordinator (`*-sharedhub-*`) or are disjoint and bridged
  **hub-to-hub** (`disjoint-two-coords-hubbridge-N8`), the order stays grid-like
  and two timelines suffice — for any number of 4-process blocks.

So: **two-or-more 4-process dim-2 executions compose to a dim-2 execution exactly
when they are stitched through a common/coordinated hub** (a single gather-point
that everyone reaches and that then reaches everyone). Stitch them with a *cross*
frontier instead and the dimension jumps to 3.

The same dichotomy appears abstractly in `execution/FrontierCompose.v`
(`threshold_dim_le2`: a non-crossing frontier preserves dim ≤ 2; the S₃ crown
raises it to 3) and quantitatively in `../frontier-sync/FINDINGS.md`
(better-balanced synchronization → lower dimension).

*(One structure left out on purpose: a 2-level hierarchical coordinator tree —
sub-hubs under a super-hub — was inconclusive here (the fast colorer choked, the
documented hard case needing z3), so it is not shipped as a verified dim-2
example.)*

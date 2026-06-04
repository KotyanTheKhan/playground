# Connector recovery of crowns, N = 5..8: the transposition law

Extends the N=4 connector-rescue result (`COMPOSE_N4.md`) to N = 5, 6, 7, 8.

**Setup.** Compose two minimum dimension-2 N-process executions, A then B, by
gluing A's output frontier to B's input frontier under a frontier matching `pi`
(a permutation of the N channels). Most matchings produce a **crown** (dimension
3); a **connector** of a few syncs inserted between A and B can recover
dimension 2. We use the canonical dim-2 block, the **star** gossip (gather to a
hub, scatter back; `S = 2N-3`) -- for N >= 6 the full set of dim-2 blocks cannot
be enumerated, so the star is the representative block. (For N=5 a 6-block /
120-matching scan with the actual enumerated blocks gave the same picture:
`compose_n5_connector.py`, 6% direct dim-2, 12 crown classes, all recovered.)

## The result: recovery cost = number of transpositions of the matching

The crown/recovery structure is **independent of N** -- it depends only on the
cycle type of the matching `pi`, and the *same* connector works at every N:

| matching `pi` | crown? | recovery connector | length |
|---------------|--------|--------------------|--------|
| identity | no (dim 2) | -- | 0 |
| hub <-> leaf transposition | **no (dim 2)** | -- | 0 |
| leaf transposition (2-cycle) | yes | `(1,2)` | **1** |
| leaf 3-cycle | yes | `(1,2)(1,3)` | **2** |
| leaf 4-cycle | yes | `(1,2)(1,3)(1,4)` | **3** |
| leaf d-cycle | yes | `(1,2)(1,3)...(1,d)` | **d-1** |
| double transposition (2,2) | yes | `(1,2)(3,4)` | **2** |
| full N-cycle | yes | `(1,2)(1,3)...(1,N)` | **N-1** |

So **the minimal connector that recovers a crown is a "fan" of one sync per
transposition in the matching's cycle decomposition**:

    recovery length  =  (number of transpositions of pi)  =  N - (number of cycles of pi)
                     =  sum over cycles of (cycle_length - 1).

Each crossing introduced by the matching costs exactly one synchronization to
undo; a d-cycle is d-1 crossings, recovered by a fan `(1,2)(1,3)...(1,d)` rooted
at one channel of the cycle. A product of disjoint cycles is recovered by the
union of their fans (e.g. the double transposition by `(1,2)(3,4)`).

## Evidence

- The fan connector of `d-1` syncs recovers the d-cycle crown for **every** d =
  2..N and **every** N = 5,6,7,8 (z3-verified, including the 7-sync fan for the
  full 8-cycle). So `d-1` is an achievable upper bound for all d.
- It is also the **minimum** where brute force is feasible: a leaf 2-cycle needs
  1 (not 0), a 3-cycle needs 2 (not 1), a 4-cycle needs 3 (the length-3 fan is 1
  of 216 connectors; length <=2 fails). For d >= 5 the minimum is >2 (length-<=2
  search fails) and matches the fan value `d-1` by the same pattern.
- N-independence: identical table for N = 5, 6, 7, 8; the connector lives entirely
  on the moved channels, so neither the hub count nor N changes it.
- `hub <-> leaf` transpositions never crown -- swapping the hub with a leaf is a
  symmetry of the star, so it introduces no crossing.

## Examples

`connector_examples/` holds 52 verified executions (26 crowns + 26 recoveries),
named `N{n}_{matching}_crown_dim3.yaml` and
`N{n}_{matching}_recovered_conn{len}_dim2.yaml`, for N = 5..8 and matching =
leaf-d-cycle (d = 2..N), full-N-cycle, and double transposition.

Reproduce: `scan_connector_multi.py` (the N=5..8 scan) and
`compose_n5_connector.py` (the N=5 enumerated-block scan).

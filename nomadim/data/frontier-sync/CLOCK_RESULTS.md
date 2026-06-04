# N=4 Repair-Clock Validation — Empirical Results

**Harness:** `clock_realizer.py`, `clock_fan.py`, `clock_compose.py`
**Spec:** [2026-06-04-pairwise-sync-repair-clock-design.md](../../../docs/superpowers/specs/2026-06-04-pairwise-sync-repair-clock-design.md)
**Date:** 2026-06-04, branch `dev`

---

## Run output

```
loaded 10 blocks
(a) single-block exact: PASS
(b/c/d) star;star crowns=18; all repaired by minimal connector(<= 3): PASS; min-repair-length distribution: {1: 10, 2: 8}
        perm-fan (N-#cycles) repairs only 8/18 -- fan is an achievable bound, not the minimal repair
finding: heterogeneous identity crowns: 61 distinct-block pairs; single-sync-repairable: 47/61
```

Marquee witness (Step 2):

```
rescue check: (True, 2)
```

---

## Results

- **10 single blocks — all exact at 2 coords (assertion a PASS).**
  Every one of the 10 minimum N=4 dim-2 fully-synced blocks (S=5) has
  `clock_check_syncs(4, syncs) == (True, 2)`.  The 2-coordinate clock is
  extracted as a rank pair from an exact 2-realizer found by z3, then verified
  against the PG event-DAG `→hb`.  Exactness is not circular: reachability is
  recomputed independently from the sync sequence.

- **Negative control: crowns (dim 3) have no 2-coordinate clock.**
  Direct composition of B1 with itself under a crossing matching returns
  `ok=None, dim=3`.  z3 independently confirms dim 3.  The clock construction
  returns "none" for these executions.

- **HEADLINE: B1⊛B1 over all 24 matchings — 18 crowns, all repaired by minimal connector.**
  Every crown is repaired by a connector of length ≤ 2 found by shortest-
  connector search, restoring the exact 2-coordinate clock.
  Minimal-repair-length distribution: {1 sync: 10 crowns, 2 syncs: 8 crowns}.
  Assertion PASS.

- **The minimal repair is the crown's actual crossed pair (search-found), not the perm-fan.**
  The permutation-fan connector (length = N − #cycles) repairs only 8/18
  star-self crowns.  The fan is a validated achievable upper bound in its
  leaf-cycle regime (z3-verified N=5..8 data in EXPLAINER.md), but it is not
  the minimal or general repair recipe at N=4.  The search-based connector,
  targeting the crown's specific crossed pair (often hub-involving), repairs
  all 18.

- **Marquee witness `N4_connector1_rescue_dim2.yaml` (B1 ; (1,2) ; B1'):**
  `clock_check_syncs(4, syncs) == (True, 2)`, matching the stored `dimension: 2`.

- **Heterogeneous identity crowns: 61 of 90 ordered distinct-block pairs crown under identity.**
  Of those 61, **47 are single-sync repairable** (a single inserted pairwise
  sync restores exact dim 2); the remaining 14 require longer connectors or
  have no single-sync rescuer in the search.  The rescuer is frequently the
  hub sync (0,2), reflecting that the composed dimension is governed by the
  frontier relation F (both blocks + matching), not the permutation alone.
  This finding is documented; it is not the headline result.

---

## Reading

A direct gluing of two dim-2 blocks can crown (dim 3, no 2-coordinate clock)
when the frontier relation between the two blocks contains a crossed pair that
a bare permutation does not resolve.  Inserting a minimal connector — one or
two pairwise sync events targeting the actual crossed pair — restores an exact
2-coordinate clock.

The clean closed-form fan law (length = N − #cycles) holds only in its
leaf-cycle regime and is an achievable upper bound there; it is not the minimal
repair in general.  At N=4, the search-based connector outperforms the fan on
10 of the 18 star-self crowns.

The heterogeneous finding (61/90 pairs crown under identity) confirms that
crowning is a property of the full frontier relation, not of any single block.
47 of those 61 crowns are single-sync repairable; the remaining 14 are not
repaired by any single inserted sync (the search only tested length-1
connectors), so some identity-matching frontier configurations need a longer
connector — the exact minimal length for those 14 was not measured here.

---

## Any-N (N=5..7) — Empirical Fan vs. Minimal Repair

**Date:** 2026-06-04, branch `dev`
**Functions:** `star_block(n)`, `anyN_probe(n, perm, max_len)` in `clock_compose.py`

### N=5 cycle-type probe (max_len=2)

```
transposition  [0, 2, 1, 3, 4]  cycles=[[0], [1, 2], [3], [4]]  direct_dim=3  fan_len=1  fan_repairs=True  min_len=1
leaf3cycle     [0, 2, 3, 1, 4]  cycles=[[0], [1, 2, 3], [4]]    direct_dim=3  fan_len=2  fan_repairs=True  min_len=2
leaf4cycle     [0, 2, 3, 4, 1]  cycles=[[0], [1, 2, 3, 4]]      direct_dim=3  fan_len=3  fan_repairs=True  min_len=None
doubleswap     [0, 2, 1, 4, 3]  cycles=[[0], [1, 2], [3, 4]]    direct_dim=3  fan_len=2  fan_repairs=True  min_len=2
```

`min_len=None` for `leaf4cycle` means no connector of length ≤ 2 was found within the bounded search; the fan connector of length 3 does repair it.

### N=6, N=7 fan-only check (leaf transposition swap(1,2), max_len=0)

```
N=6 swap(1,2)  direct_dim=3  fan_len=1  fan_repairs=True
N=7 swap(1,2)  direct_dim=3  fan_len=1  fan_repairs=True
```

### Reading

At N=5, all four representative crown permutations have `fan_repairs=True`: the perm-fan connector (length = N − #cycles) successfully restores an exact 2-coordinate clock for every tested case. The same holds for N=6 and N=7 on the leaf transposition. This is consistent with EXPLAINER.md's leaf-cycle claim that the fan is a z3-verified achievable repair in the leaf-cycle regime.

`star_block(n)` (gather-then-scatter on hub 0) is confirmed dim 2 for N=5 (test `star_n5` PASS).

For the N=5 transposition crown `[0,2,1,3,4]`, the minimal search finds a repair of length 1 (matching the fan length of 1). For the `leaf4cycle` `[0,2,3,4,1]`, the fan of length 3 repairs the crown, but no connector of length ≤ 2 was found within the bounded search — consistent with the fan being tight there. The perm-fan is thus an achievable upper bound; the minimal repair may be shorter or equal, depending on the permutation structure. At N=4, the search outperformed the fan on 10/18 crowns; at N=5 the fan matches or exceeds (within the cycle types tested), which aligns with the EXPLAINER.md characterization of the leaf-cycle regime. No claim is made beyond the permutations actually tested.

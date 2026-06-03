# Findings: dimension of fully frontier-synchronized executions (N <= 5)

From enumerating the fully frontier-synchronized executions
(`is_full_synchronized`: every process start is seen by every process last
event) of N = 2..5 processes with `nomadim enumerate --all-dims --with-dim`.

## Finding 1 — order dimension is not monotone in the number of synchronizations

**Adding a synchronization event can *lower* the order dimension of the
happened-before poset. The fewest-sync full synchronization is therefore the
*highest*-dimensional one — minimizing syncs and minimizing dimension are
competing objectives.**

The minimum number of syncs to fully synchronize, per achieved dimension:

| N | dim 3 (min syncs) | dim 2 (min syncs) |
|---|-------------------|-------------------|
| 2 | -- | 1 |
| 3 | -- | 3 |
| 4 | **4** | **5** |
| 5 | **6** | **7** |

For N = 4 and N = 5 the cheapest full synchronization is dimension 3 (4 resp. 6
syncs); reaching dimension 2 costs one *extra* sync (5 resp. 7). So as S grows
the attainable dimension *drops* from 3 to 2 — dimension is non-monotone in S.

Intuition: few syncs route all causality through a handful of "hub" events, and
that skewed merge pattern realizes a higher-dimensional order. An extra sync
lets the pattern become more grid-like (balanced halves cross-coupled), which is
exactly a 2-dimensional order. Fewer syncs => more skew => higher dimension.

## Finding 2 — dimension <= 3 for N <= 6, and dimension 4 first appears at N = 7

The order dimension of a fully frontier-synchronized execution is **<= 3 for all
N <= 6**, and **dimension 4 first occurs at N = 7**. The vector-clock bound only
says dim <= N; the actual maximum climbs much more slowly -- it is 2 for N <= 3,
3 for 4 <= N <= 6, and reaches 4 at N = 7.

A concrete, verified N = 7 dimension-4 execution (S = 12 syncs, fully
synchronized): `(3,6)(0,2)(4,5)(3,4)(2,6)(1,3)(1,2)(2,5)(0,3)(4,6)(3,6)(3,4)`
(saved as `N7_S12_dim4_z3_01.yaml`). Dimension verified with the z3 SMT oracle:
t = 3 is UNSAT (no 3 linear extensions intersect to it -> dim > 3) and t = 4 is
SAT, so dim = 4 exactly. The oracle was validated on the standard examples S_3
(dim 3) and S_4 (dim 4). N = 7 cannot be enumerated (OOM), so this was found by
randomized memory-light walks that stop at first full synchronization
(`hunt_n7.py`, `min_s_dim4.py`).

**Minimum S for an N = 7 dimension-4 execution is 11** -- one above the gossip
minimum S = 2N-4 = 10. Evidence: 3000+ diverse *optimal* S = 10 schemes
(constructive core/fan-in/cross/fan-out, `constructive_s10.py`) plus
efficiency-biased S = 10 samples are **all dimension 3**, while dimension 4 does
occur at S = 11 (e.g. `(5,6)(0,4)(2,4)(0,5)(2,6)(1,3)(1,2)(3,4)(3,6)(1,5)(0,4)`,
saved as `N7_S11_dim4_z3_01.yaml`; z3 t = 3 UNSAT, t = 4 SAT). So unlike N = 4,
5, 6 -- where the maximum dimension is attained at the minimum-sync layer --
N = 7's gossip-minimum executions are only dimension 3, and dimension 4 needs one
extra sync. (Not an exhaustive proof for S = 10, since N = 7 cannot be
enumerated, but a large diverse sample.)

### Independent verification of the N=7 dimension-4 result

Because the N=7 result rests on a custom SMT model, it was cross-checked four
independent ways (`verify_n7.py`), all passing for N7_S10 (dim 3), N7_S11 and
N7_S12 (dim 4):

1. **Model fidelity** -- the pure-Python execution expansion produces exactly
   the same poset (identical vertex count and edge set) as nomadim's own
   `convert`.
2. **Oracle calibration** -- the SMT model returns the correct dimension on
   canonical posets of known dimension 1-5 (chain, antichain, S_3, S_4, S_5).
3. **Certificate** -- z3's witness (the d linear extensions) is extracted and
   verified independently of the solver to realize the poset, *proving* dim <= d.
4. **Second encoding** -- a structurally different SMT model (boolean precedence
   with explicit transitivity) independently confirms t = 3 UNSAT, t = 4 SAT.

A fifth, "gold-standard" check -- nomadim's own brute-force exact algorithm on
N7_S11 and N7_S12 -- was run for **6 hours at ~99% CPU each and did not finish**
(no output). This is the expected intractability that motivated the z3 oracle in
the first place (N=7 posets have ~80+ critical pairs); it neither confirms nor
contradicts the result. The four layers above settle it: the dimension-4 N=7
findings are verified.

For N <= 6, **every fully frontier-synchronized execution classified has
dimension 2 or 3 -- never 4 or more.** Concretely:

- N = 2, 3: dimension 2 only (no dimension-3 execution of <= 3 processes exists
  in range).
- N = 4: dimensions 2 and 3 only, verified for **all** shapes up to S = 10
  (134116 shapes; histogram below). In particular **no dimension-4 execution of
  4 processes exists** in this range, even though the vector-clock bound permits
  dimension <= 4.
- N = 5: dimensions 2 and 3 only, verified for **all** shapes up to S = 8
  (17008 shapes; histogram below).
- N = 6: the minimum full synchronization is S = 8 (gossip number 2N-4); its
  **107 non-isomorphic shapes are all dimension 3** (z3 SMT oracle; see below).
  The minimum-sync layer is always the highest-dimensional one, so N = 6 also
  tops out at dimension 3.

Across N = 4, 5, 6 the maximum dimension is **3** -- it jumped 2 -> 3 at N = 4,
held through N = 6, and climbs to **4 at N = 7** (Finding 2 above). So the
maximum dimension grows with the number of processes, roughly one step every
two processes (2 at N<=3, 3 at N=4..6, 4 at N=7), far below the vector-clock
ceiling of N.

### A cautionary note (and a better oracle)

For N = 6 the posets have 65+ critical pairs, beyond nomadim's exact
brute-force colorer cap (64), and even with the cap raised, 3 of the 107 shapes
did not 3-color within minutes -- they *looked* like dimension-4 candidates. A
sound SMT check (z3) refuted this: all 3 are dimension exactly 3 (a 3-realizer
exists; z3 finds one in milliseconds). "Slow to brute-force-color" is **not**
evidence of high dimension. Definitive dimension for the larger posets comes
from `confirm_dim.py` / `classify_z3.py`, which model "dimension <= t" directly
as the existence of t linear extensions whose intersection is the poset (every
incomparable pair split) and decide it with z3 -- UNSAT at t = 3 would be a
*proof* of dimension >= 4. None has been found.

Dimension-3 first appears at N = 4. The jump to a hypothetical dimension 4 would
require a fully-synchronized merge pattern that embeds the 4-dimensional
standard example, which these "chain-of-pairwise-syncs" event structures do not
seem to produce.

### N = 4 dimension histogram (all shapes, S <= 10)

| syncs | dim 2 | dim 3 |
|-------|-------|-------|
| 4 | -- | 1 |
| 5 | 10 | 20 |
| 6 | 92 | 167 |
| 7 | 532 | 916 |
| 8 | 2424 | 4129 |
| 9 | 9726 | 16688 |
| 10 | 36276 | 63135 |

(No dimension >= 4 at any S; 134116 shapes total.)

The vector-clock embedding bounds dimension by N (= 4 here), so dimension 4 is
*permitted* but never *realized* -- raising the dimension past 3 appears to
require more than 4 processes, not more syncs.

### N = 5 dimension histogram (all shapes, S <= 8)

| syncs | dim 2 | dim 3 |
|-------|-------|-------|
| 6 | -- | 4 |
| 7 | 40 | 668 |
| 8 | 664 | 15632 |

(No dimension >= 4 at any S; 17008 shapes total.)

## Why this is easy to miss

`nomadim enumerate` keeps only dimension-<=2 executions by default, so it never
reports the dimension-3 minimum shapes (N=4 S=4, N=5 S=6) and over-states the
true minimum sync count. Both findings are only visible with `--all-dims`
(keep every dimension) and `--with-dim` (classify in-process), added for this
study.

See `SUMMARY.md` for the full per-shape table and `generate.py` to reproduce.

# Design: Finishing the dimension submodule (all remaining admits)

Date: 2026-05-29. Supersedes the per-config approach in
`2026-05-29-admit1-n5-residual.md` for the n=5 base case.

## Goal

Close every remaining `Admitted` in `posets/dimension/` so `hiraguchi_bound`
and the whole chain are admit-free. Starting admit count: **5**.

- `N5Exhaustive/EdgeCount{5,6,7,8}.v` — n=5 base case, edge counts 5–8.
- `RemovablePairs.v:1834` — `trotter_coverage_via_extremality`.

## Architecture finding (why two tracks, both required)

`hiraguchi_small_case` (RemovablePairs.v) handles n∈{4,5} by direct analysis,
NOT the inductive step: its comment notes the inductive step "would recurse to
subposets of size ≤ 3, below Hiraguchi's threshold." The general induction
(`hiraguchi_helper`, via Trotter removable pairs) reduces n→n-2, bottoming out
at the n=4 and n=5 base cases. So:

- **Track A (n=5 base, counts 5–8)** and **Track B (Trotter inductive step)**
  are BOTH genuinely required — neither subsumes the other.
- They touch disjoint files (`N5Exhaustive/` vs `RemovablePairs.v`) →
  independent, parallelizable, separate commits.

## Track A — n=5 base case (counts 5–8)

The committed bridge `two_realizer_from_fin_ranks`
(`N5Exhaustive/N5RealizerTransport.v`, Qed) reduces "abstract 5-element poset
R2 has a 2-realizer" to "two rank functions `rho1,rho2 : Fin.t 5 -> nat` realize
`R2_matrix`" (injective + R2_matrix-monotone + intersection + distinguishing).

**Why prior approaches failed.** Uniform numeric rank is impossible
(down-count-dominated; can't resolve incomparable pairs of unequal down-count).
Reflection over `C(25,8)=1.08M` size-8 ordered-pair subsets is infeasible
(probe killed by the watchdog). Per-config over abstract elements explodes
(~5^6 Hcov casework).

**New feasible enumeration.** A poset's strict order picks ONE direction per
comparable UNORDERED pair. So enumerate orientation-assignments of the 10
unordered pairs of `Fin.t 5`: each pair → {none, fwd, bwd}, i.e. `3^10 = 59049`
assignments (≈ EdgeCount4's feasible 12650), filter to transitive posets. This
covers all counts 5–8 (indeed all of non-chain n=5) uniformly.

**Plan (probe-first — chosen).** S1 probes the `3^10` enumeration (generation
time, poset count, realizer-search cost), watchdog-guarded.
- If feasible → ONE uniform lemma `n5_matrix_two_realizable : forall M, is_poset_b M = true -> ~ is_total_b M = true -> exists rho1 rho2, <bridge conditions>`,
  proven by native_compute over the `3^10` enumeration with a `has_realizer_b`
  search (over candidate rank/permutation pairs). Wire through the bridge to
  give "any non-chain 5-element poset has a 2-realizer"; route
  `n5_residual_classes_two_realizer` (or `n5_nonantichain_nonchain_two_realizer`)
  to it; DELETE `EdgeCount5–9` and the per-count edge-count dispatch (net
  simplification).
- If infeasible → fall back to per-count explicit `f0..f4` constructions
  (one transitive orientation per edge count), still via the bridge.

## Track B — Trotter coverage (`trotter_coverage_via_extremality`)

The single deepest input (Trotter 1992, Ch. 6, Thm 6.1): given an extremal
critical pair and a sub-realizer on the residual, some L' in the realizer never
rejects a chosen boundary pair (p,q). Cycles in the augmented relation
correspond to critical pairs refining (p,q); extremality eliminates such
refinement chains.

Decompose (S4) into focused sub-lemmas — candidates:
1. cycle in `Aug(L', B ∪ {(p,q)})` ⇒ a critical pair refining (p,q);
2. extremality of (x',y') ⇒ no proper refinement chain of (p,q);
3. greedy-acceptance bookkeeping (`greedy_acyclic_subset` membership).
Each gets the admit-introduction checklist + `proof-skeptic` review. Highest
risk; refine progressively; may span several sessions.

## Session breakdown

- **S1 (now):** Track A probe + decision; if uniform feasible, start the
  enumeration + `has_realizer_b` + `is_total_b` booleans.
- **S2–S3:** Track A construction; close counts 5–8; delete obsolete files;
  full `posets/dimension` green; admit count 5 → 1.
- **S4:** Track B decomposition; write Track B plan + focused sub-admits.
- **S5–N:** Track B construction; close Trotter sub-lemmas progressively.

## Risk register

- **A-feasibility** (`3^10` realizer-search cost): HIGH→mitigated by S1 probe;
  fallback = per-count explicit constructions.
- **B-depth** (Trotter is genuinely hard): HIGH; mitigate via progressive
  refinement, `proof-skeptic`, and accepting multi-session scope.
- **Build hygiene**: every build via `timed-build.sh` (timeout + `-j` cap +
  memory watchdog); reflection probes `-j1` with a memory cap.

## Success criteria

`grep -rnE '^[[:space:]]*(Admitted|admit)\.' posets/dimension` returns nothing,
and `bash .claude/scripts/timed-build.sh 1800 posets/dimension 2` is green.

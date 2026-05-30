# Dimension Replan Status

Tracks per-session progress for `2026-05-28-dimension-replan-design.md`.

## R0 probe results (2026-05-28)

- Probe 1 (single vm_compute is_refl): instantaneous
- Probe 2 (sublists 4 all_pairs length): instantaneous
- Probe 3 (filter is_refl over 12650 sublists): instantaneous
- **Total elapsed time: 3.244 seconds**

**Decision:** GO

vm_compute completes the full 12650-sublist reflection check in under 4 seconds. Reflection approach is viable for closing admits in dimension theory.

## R1 results (2026-05-28)

- Implementation: split into 2 files for fast iteration.
  - `posets/dimension/N5Exhaustive/N5Reflect.v` (271 lines) — defs + cheap lemmas (~1.5s compile).
  - `posets/dimension/N5Exhaustive/N5Reflect_Exhaustive.v` (81 lines) — `exhaustive_4edge_decidable` + `exhaustive_4edge` (Qed via `native_cast_no_check`).
- Commit: `4c57ebe`.
- Admit count: 3 (unchanged; reductions happen in R3 wire-in).
- Lessons: monolithic file would have a slow vm_compute. Split made iteration fast. Switched to `native_cast_no_check` from `vm_cast_no_check` for ~10× kernel-recheck speedup.

## R1 refactor (2026-05-28)

- Split `N5Reflect_Exhaustive.v` into 5 parallel chunks + combiner.
  - 5 sibling chunk files: `N5Reflect_Exhaustive_{1..5}.v` (~10 lines each, `native_cast_no_check` over 1/5 of the 12650-sublist domain).
  - Combiner `N5Reflect_Exhaustive.v` (~120 lines): symbolic `firstn_skipn` / `skipn_skipn` proof to glue chunks into `exhaustive_4edge_decidable`. No vm_compute.
- Clean-build wall-clock: ~120s (native_compute saturates cores even when 5 chunks run in parallel; serialized at OS scheduler level). Sub-60s target NOT met.
- Commit: `cc131ea`.

## Tooling (2026-05-28)

- Added `.claude/scripts/timed-build.sh <secs> <target>` — self-killing bash wrapper with hard timeout, kills mise/dune/coqc descendants + clears `_build/.lock` on timeout. Use for every Coq build call.
- Commit: `6b86b15`.

## R2 partial results (2026-05-28)

- `posets/dimension/N5Exhaustive/N5Transport.v` (489 lines, 29 lemmas, 0 admits, ~90s build):
  - `Section Transport` with bijection (`from_fin`, `to_fin`, `from_fin_injective`).
  - `R2_matrix : M5`, `R2_matrix_is_poset`, `R2_matrix_edge_count_eq`.
  - Permutation infrastructure (`in_permutations_iff` + lemmas).
- Commit: `36bbf18`.

## R2 done (2026-05-29)

- `posets/dimension/N5Exhaustive/N5Iff.v` (379 lines): 10 `is_<pattern>_b_to_exists` lemmas (→ direction is sufficient for R3 wire-in; full ↔ deferred).
  - Supporting helpers: `abcde_NoDup`, `make_NoDup5`, `find_fifth_distinct` (clean pigeon via `NoDup_incl_length`, no 1024-case cascade), `perm_in_all_perms5_nodup`, `NoDup5_pairwise`.
  - 15 lemmas, 0 admits, ~90s build.
  - Commit: `545765a`.

## R3 BLOCKED on pre-existing EdgeCount4 helper bugs

R3 wire-in attempted at `EdgeCount4.v:213-221`.  Tooling discovered that 5 of the 11 `EdgeCount4_*.v` helper files DO NOT BUILD:
  - `EdgeCount4_4claw_down.v`, `EdgeCount4_K32mm.v`, `EdgeCount4_M_shape.v`, `EdgeCount4_3claw_up_xp.v`, `EdgeCount4_3claw_down_xl.v` — hang or fail.
  - `EdgeCount4_chain3_above.v` had a polarity bug (`apply strict_indicator_eq_1; assumption` failed on `delta <> gamma` when only `gamma <> delta` was in scope) — fixed in commit `388a293`.

These files were all committed in `83ee831` (Session N5 BLOCKED).  The session was tagged BLOCKED and the build was never green — those .vo files were never produced.  The Admitted at EdgeCount4.v:221 hid the failure because EdgeCount4.v itself didn't get to that admit until its helpers built.

Each broken file likely has:
  1. 2-3 polarity bugs in `apply strict_indicator_eq_1; assumption` (same shape as chain3_above).
  2. A 5^6 = 15625-case `destruct (Hcov alpha); destruct (Hcov beta); ...` cascade that takes minutes to compile.

**Resolution options for R3:**

A. **Fix each broken EdgeCount4_*.v file.** ~5-10 hours.  Polarity fixes are mechanical (1-3 per file); the slow cartesian destructs need extended (5-10 min) compile budgets.

B. **Bypass per-class dispatcher entirely.**  Replace `n5_edge_count_4_two_realizer`'s body with a reflection-only proof using R2_matrix + exhaustive_4edge + N5Iff lemmas + direct `IsRealizer` construction from `N5Realizers.v`.  Skips EdgeCount4_*.v files entirely.  ~5-8 hours.

C. **Skip R3 for now, ship R0-R2.**  Phase R partially landed: reflection infrastructure built, but admits #1 and #3 remain.  Move to Phase T (Trotter).

**Decision pending from user.**

## R3 DONE + dimension build restored (2026-05-29)

Chose **Option A**.  All 6 heavy `EdgeCount4_*.v` cascade helpers turned out to
be slow-but-VALID (no polarity bugs in the 5 untested ones — a prior pass had
already added explicit symmetry handling).  They compile in ~3 GB / ~5-8 min
each; the original "crashes" were OOM from building them in parallel at the
default `dune -j = ncpu`, not logic errors.

- **Build infra hardened** (commit `91107be`): every build now routes through
  `.claude/scripts/timed-build.sh <secs> <target> [jobs] [mem_mb]`, which adds a
  memory watchdog (default 20 GB cap, exit 137) on top of the timeout (exit
  124) and bounded `-j` (default 2).  CLAUDE.md + 5 skills updated.  Root cause
  of the repeated laptop OOM: a single heavy worker peaks ~3 GB, so `-j 10`
  reached 30+ GB on the 32 GB machine.
- **Admit #3 closed** (commit for `EdgeCount4.v`): `n5_edge_count_4_two_realizer`
  is Qed.  The reflection wire-in had two defect classes — four off-by-one
  bracket counts in the Class 11/20/12/14 destruct intro patterns, and a
  spurious `Hcov` arg on all 12 reflection-lemma applications (none of
  `R2_matrix_is_poset` / `_edge_count_eq` / the 10 `is_*_b_to_exists` take
  `Hcov`).
- **RemovablePairs.v build restored** (commit for `RemovablePairs.v`): the file
  had not compiled since `4836bcf` (committed under a "(Qed)" message but never
  built).  `aug_cycle_implies_step3_path` had 3 defects: undefined
  `clos_trans_in_rt` (added as top-level helper), a no-op
  `specialize (fun X => X) as _.` junk line, and `Hba_dec` re-inducting on
  fixed endpoints `b a` (replaced with `specialize (Hdecomp b a Hba)`).

**Full `posets/dimension` now builds green** (`-j2`, ~verified 2026-05-29).
`hiraguchi_bound` (RemovablePairs.v:2886) is a real theorem modulo the 2
remaining admits.

## Admit #1 refined via master edge-count dispatch (2026-05-29)

Plan: `docs/superpowers/plans/2026-05-29-admit1-n5-residual.md`. Did step S1.

Scoping found `n5_edge_count_{1,2,3,4}_two_realizer` were all Qed but ORPHANED
(no dispatcher routed to them), and the reflection-enumeration template does
not scale past count 4 (C(25,k) blows up).

S1 (master dispatch) — DONE:
- New focused-admit files `N5Exhaustive/EdgeCount{5,6,7,8,9}.v`, each
  `n5_edge_count_K_two_realizer` (same signature as 2/3/4), Admitted.
- `N5DispatcherShapes.v`: proved `n5_residual_classes_two_realizer` (was
  Admitted) by dispatching on `edge_count_5 R2 p q r s t`:
    - `carrier_5_destructure` completes the chosen edge to 5 carrier elements;
    - `non_antichain_iff_edge_count_pos` gives k >= 1;
    - new helper `edge_count_5_le_9_of_incomp` gives k <= 9 (incomparable pair
      contributes 0; 25-case `lia` over `strict_indicator_antisym`);
    - 11-way case routes k=1..4 to the Qed handlers, k=5..9 to the new admits,
      k=0 and k>=10 closed by `lia` against the bounds.
- Counts 1-4 of the n=5 base case are now genuinely closed.

This is progressive refinement (D4): one broad admit -> five focused
per-edge-count admits, with the surrounding plumbing all Qed.

## Count-9 closed; twin-rank technique validated (2026-05-29)

Spike S2 succeeded AND landed the proof. `N5Exhaustive/EdgeCountIncomp.v`
(all Qed) now provides the reusable machinery:
  - `comparable_indicator_sum`, `incomp_carrier_exists`, `two_incomp_le_8`
    (uniqueness of the incomparable pair when count = 9),
  - `dle`/`rk` down-count rank, `dle_mono`, `rk_strict_mono`,
  - `twin_rk_eq` (incomparable elements have equal rank when count = 9).
`EdgeCount9.v` is now Qed: `n5_edge_count_9_two_realizer` builds the 2-realizer
from `rk1 = 6*rk + lab`, `rk2 = 6*rk + (4-lab)` via `n5_two_realizer_framework`.
This is the template for counts 5-8 (reflection enumeration was infeasible).

## Uniform Fin.t 5 route — Piece 1 landed (2026-05-29)

Per-config hit a casework wall ("at most 2 incomparable pairs" needs ~5^6
abstract Hcov cases). Switched to the uniform Fin.t 5 route.

`N5Exhaustive/N5RealizerTransport.v` (Qed): `two_realizer_from_fin_ranks`
reduces "abstract R2 has a 2-realizer" to "rho1,rho2 : Fin.t 5 -> nat realize
R2_matrix" (injective + monotone + intersection + distinguishing on Fin.t 5),
discharging `n5_two_realizer_framework` via the bijection. So counts 5-8 now
reduce to CONCRETE rank constructions on f0..f4.

Remaining (Piece 2): build rho1,rho2 per edge count on Fin.t 5. The matching
case (counts 9 / 8-disjoint) is the down-count ranking ported to Fin.t 5; the
non-matching case needs a transitive orientation of the incomparability graph,
now a finite/decidable check over f0..f4.

## Session 1 of dimension-finish plan (2026-05-29): probe results

Plan: `docs/superpowers/plans/2026-05-29-dimension-finish.md`.

Task A1 probe (3^10 orientation enumeration on Fin.t 5):
- enumeration `length (enum_assignments 10) = 59049` in 2.5s (clean) — fine.
- `filter is_poset_b` over the 59049 (via `from_edges`): exceeds 120s, so
  `is_poset_b` is ~2 ms/item. A realizer SEARCH (120x120 perms per poset) on top
  is 14400x more work => the uniform reflection-with-search is INFEASIBLE.
- **A1 decision: NO uniform-with-search.**

Tooling: discovered a stale-`dune`-RPC-server confound — the watchdog killed
`rocqworker`/`coqc` but left a `dune` server that forwarded/queued later builds
behind a stuck compile. Fixed: `timed-build.sh` cleanup now reaps `dune` too.
Always `pkill -9 -f dune` before a fresh reflection build.

Refined options for the n=5 base (counts 5–8), pending next session:
  (A4) per-count explicit constructions on Fin.t 5 (destruct R2_matrix pair
       entries, provide literal `rho1,rho2`, verify via the bridge by
       vm_compute). No 59049 enumeration; feasible per-shape but voluminous.
  (A5) deterministic-orientation reflection: a CHEAP orient algorithm (no
       search) + reflect over 59049 that it realizes every n=5 poset (chunked
       native_compute, ~25 chunks). Feasible only if a correct n=5
       transitive-orientation algorithm is implemented; per-item ~is_poset_b +
       verify (~3-4 ms) => ~200s vm / less native, chunked.

## Session 2 (2026-05-29): A5 candidate FAILED; corrected algo is heavy

Implemented + validated the A5 candidate `compute_realizer`:
  L1 = toposort(M); L2 = toposort(M with ALL incomparable pairs reversed
  relative to L1). Sample check `forallb check (firstn 8000 orientations)`
  returned **false** in 97s (vm_compute, ~12 ms/item).

Why false: reversing ALL of L1's incomparabilities at once can create a cycle
(the M2 augmentation is not always acyclic) — exactly the Dushnik-Miller
subtlety. So a single fixed L1 is not enough.

**Correction:** a 2-realizer's L2 is DETERMINED by L1 (comparabilities by M,
incomparabilities reversed); so `compute_realizer` must TRY EACH linear
extension L1 (perm extending M, <=120) and return the first whose full reversal
M2 is acyclic. Correct, but ~120x the per-item cost.

**Cost reality:** the candidate was already ~12 ms/item (vm). The corrected
(try-all-L1) is ~100-200 ms/item native => 59049 items ~ 1.6-3.3 h total,
i.e. ~25-50 native chunks of multi-minute each. POSSIBLE but a heavy
multi-session build; not landable in one session.

So every cheap path is exhausted: numeric ranks impossible; reflection-search
infeasible; reflection-cheap-candidate incorrect; per-count destruct explodes
(2^20). The only mechanization left for counts 5-8 is the corrected A5
(try-all-L1 compute_realizer + heavy native chunked reflection + bridge), or a
genuinely cheaper correct transitive-orientation (Gamma-forcing) algorithm.

## Session 2 conclusion: search-based reflection ruled out; need cheap orient

Validated the CORRECTED try-all-L1 `compute_realizer` (search each of the 120
perms as L1; L2 is then forced): even `native_compute` over just 3000
orientations exceeds 150s. So ANY per-item realizer SEARCH over the 59049-item
enumeration is too slow — regardless of correctness.

**Full solution-space map for counts 5-8 (all empirically tested):**
- numeric down-count ranks — impossible (can't resolve unequal-rank incomp);
- reflection + realizer SEARCH (per item) — too slow (this session);
- reflection + cheap candidate (reverse-L1) — INCORRECT (returns false);
- per-count destruct of R2_matrix entries — 2^20 branch explosion.

**Only feasible mechanization remaining:** reflection with a CHEAP, no-search,
CORRECT transitive-orientation (Gamma-forcing) `compute_realizer` — per item
~is_poset_b + O(small), so the 59049 reflection is dominated by the is_poset_b
floor (~12-25s native, chunked ~5-8). The blocker is implementing the
Gamma-forcing orientation algorithm CORRECTLY (its correctness is then verified
by the reflection itself). This is a genuine algorithm-implementation task
(~50-100 lines of Coq functions: incomparability graph, forcing classes,
consistent orientation, rank extraction) — the S3 deliverable.

Bridge `two_realizer_from_fin_ranks` (Qed) remains the foundation: once
`compute_realizer` produces verified ranks, the bridge closes counts 5-8.

## Session 3: greedy-tc orient is the right algorithm; blocker is REPRESENTATION

Implemented the cheap, no-search, correct candidate:
  `orient M` = greedily orient each still-incomparable pair i->j in index order,
  transitively close after each (the closure performs Golumbic forcing);
  `orient2` = the conjugate (reverse relative to orient's choices); ranks =
  down-counts in the two resulting total orders; `realizes_pair` checks the
  bridge conditions. Single deterministic attempt (NO search) => cheap in ops.

But validation (firstn 6000) was killed at 150s: the matrix is represented as a
FUNCTION closure `Fin.t 5 -> Fin.t 5 -> bool`, and `tc` composes 5 `tstep`
closures per `add_edge` (~20 add_edges/item) => deeply nested closures that
vm_compute re-traverses on every lookup. The OPS are few; the closure
representation is the killer (same lesson as the earlier `mat_of` closure vs
`from_edges`).

**Fix (next step):** represent the working matrix as concrete DATA, not a
closure — an edge-LIST (transitively close the list) or a 25-bit packed nat,
converting to `M5` only at the end. Then `orient`/`tc` are fast; the reflection
over 59049 should be dominated by the is_poset_b floor (~native chunked,
feasible). The algorithm (greedy-tc) is believed correct (Golumbic forcing for
comparability graphs); the reflection will verify it.

This is a genuine efficient-representation engineering task. Counts 5-8 are NOT
closed; the path is clear but needs careful, deliberate implementation.

## Session 3 corrected scale insight: PER-COUNT, not uniform (2026-05-29)

The repeated reflection timeouts were a SCALE error: the uniform enumeration is
3^10 = 59049 assignments, and the per-item cost (is_poset_b ~2 ms on the M5
function-closure representation, + orient) makes 59049 items take many minutes —
too slow regardless of algorithm/representation (4 representations tried;
materialize-via-from_edges still killed at 6000).

**Fix: reflect PER EDGE COUNT** (the EdgeCount4-feasible granularity):
  count K enumerates ~ C(10, 10-K) * 2^K assignments:
    K=5: 252*32  = 8064;  K=6: 210*64 = 13440;
    K=7: 120*128 = 15360; K=8: 45*256 = 11520.
  Each ~ EdgeCount4's feasible 12650 (which built in ~120 s native, 5 chunks).
So counts 5-8 = FOUR per-count reflections, each EdgeCount4-scale, chunked
native — feasible, not the infeasible 59049 uniform.

**Algorithm (believed correct, UNVERIFIED — validation kept timing out at the
uniform scale):** greedy transitive-closure orientation `orient M` (orient each
still-incomparable pair i->j in index order, transitively close = Golumbic
forcing); conjugate `orient2`; ranks = down-counts of the two total orders;
`realizes_pair` checks the bridge conditions. NO search (cheap per item).

**Remaining engineering for counts 5-8 (S4+):** (1) per-count assignment
generator; (2) an EFFICIENT matrix representation (the M5 function-closure is
the per-item-cost culprit — consider a bit-packed nat or list-of-rows so
is_poset_b/orient are fast); (3) validate greedy-tc correctness on one
per-count sample; (4) 4 chunked native reflections + bridge wiring. Plus the
deep Trotter `trotter_coverage_via_extremality` (#2).

This is substantial, EdgeCount4-scale x4 + Trotter; the bridge + algorithm +
correct scale are now in hand.

## Counts 5-8: comprehensive negative — reflection hits a DUAL wall (2026-05-29/30)

Tried ~6 implementations (M5-closure, from_edges, materialize-per-step,
try-all-L1 search, greedy-tc closure, bit-packed N). Two independent walls:

1. **Correctness:** a correct transitive ORIENTATION of the incomparability
   graph must CHOOSE each pair's direction (Golumbic forcing / backtracking).
   The cheap deterministic candidates I implemented all orient by a FIXED rule
   (i->j by index) — incorrect (validation returns false; reversing all
   incomparabilities can cycle). Correct = either a 120-perm SEARCH per poset
   (slow) or an intricate forcing algorithm (unwritten).

2. **Performance:** per-item cost is ~10-15 ms ACROSS ALL representations
   (incl. bit-packed N — the greedy-tc does ~750k ops/item from full transitive
   closure after each of ~10-20 edge additions). At the enumeration sizes
   (uniform 59049, or per-count ~8-15k) this is too slow for vm_compute
   (timeouts at 6-8k items / 120-150s) and borderline+compile-overhead for
   native_compute (uniform killed at 240s).

So a reflection proof of counts 5-8 needs BOTH a correct forcing-orientation
AND serious performance tuning (cheaper-than-full-tc orientation + careful
native chunking). This is substantial performance/algorithm engineering, not
landed despite extensive effort.

**Non-reflective alternative (recommended to evaluate next): removable-point
reduction n=5 -> n=4.** n=4 base is already Qed. Hiraguchi removable-point
lemmas: dim(P) = dim(P - x) when x is a max or min (x goes last/first in both
extensions), or when x is comparable to <=1 element, etc. If every n=5
non-chain poset has such a removable point reducing to a dim<=2 4-element
subposet, counts 5-8 close WITHOUT reflection (no performance wall). Needs
formalizing the removable-point lemma(s) + showing coverage for n=5. This
sidesteps the dual wall entirely and is likely the better path.

The bridge `two_realizer_from_fin_ranks` (Qed) remains available if a cheap
correct orientation is ever found.

## Admit count: 5 (was 6)

- `RemovablePairs.v:1834` — `trotter_coverage_via_extremality` (admit #2, the
  general-n Trotter coverage keystone).
- `N5Exhaustive/EdgeCount{5,6,7,8}.v:36` — per-edge-count n=5 obligations
  (refined remnant of admit #1; counts 5/6/7/8 have 5/4/3/2 incomparable pairs,
  so the single-twin argument must generalize to several incomparable pairs —
  the incomparability graph must be 2-coloured into the two extensions).

**Next (plan S2):** spike `EdgeCount9` (k=9, <=1 incomparable pair, fewest iso
classes) to validate a technique that scales to counts 5-9, since the
`EdgeCount4` reflection template does not.

## Count-8 EXHAUSTIVENESS closed — dual wall broken (2026-05-30)

The "dual wall" (above) was about reflecting a *realizer search/orientation*
over the enumeration. This session sidestepped BOTH walls by reflecting only
*pattern membership* (no orientation algorithm, no per-item search):

- **Enumeration wall → constrained `enum_k_none`.** Instead of 3^10 = 59049 or
  C(25,8)=1.08M, enumerate length-10 option-bool lists with exactly 2 `None`s
  directly: `count8_assigns := enum_k_none 10 2` = 11520 (EdgeCount4-scale).
  Committed earlier: `coverage_8 : forallb chk8 count8_assigns = true` (5 chunks
  `N5Reflect8_ex{0..4}.v`, `native_cast_no_check`, glued in
  `N5Reflect8_Exhaustive.v`), where `chk8 a = is_poset_b (mat_of a)` implies one
  of 6 patterns `any_pattern_8_b`.
- **∀-M bridge (this session, all Qed):**
  - `N5Reflect8_Exhaustive.v` — `enum_k_none_complete`: every length-n, k-None
    list is enumerated by `enum_k_none n k`.
  - `N5Reflect8_Bridge.v` — `M_assign M` (canonical orientation of the 10
    pairs), `mat_of_M_assign : is_poset_b M -> mat_of (M_assign M) i j = M i j`
    (reconstruction, via `in_assign_edges_M_assign` + `pairs10_cover`/`_neq` +
    `in_combine_map_self`). Foundational: `poset_refl`, `poset_antisym_b`,
    `fin5` destruct tactic.
  - `N5Reflect8_Count.v` — `num_none_M_assign : is_poset_b M -> edge_count_b M=8
    -> num_none (M_assign M) = 2` (via `edge_count_pairs10` [all_pairs sum =
    pairs10 paired sum, `cbn`+`ring`], `num_none_pairs10`, `pair_sum_1`
    [per-pair antisym], `fold_combine`/`fold_add_eq`).
  - **`exhaustive_8edge : forall M, is_poset_b M = true -> edge_count_b M = 8 ->
    any_pattern_8_b M = true`** (Qed). Every 8-edge poset matches one of the 6
    count-8 iso-class patterns. Commits on branch `dimension_finish`.

This is the M5-level theorem. Whole project green via `@check` (vos).

**Remaining to close `EdgeCount8.v` admit #1-residual (NOT yet done):**
1. Transport `edge_count_5 R2 a b c d e = 8` (abstract B) → `R2_matrix` with
   `is_poset_b R2_matrix = true` and `edge_count_b R2_matrix = 8` (reuse
   `N5Transport.v`'s `R2_matrix_is_poset` / `_edge_count_eq`).
2. Apply `exhaustive_8edge` → one of `is_c8_{1..6}_b R2_matrix = true`.
3. 6 `is_c8_k_b_to_exists` iff lemmas (N5Iff template) → abstract pattern shape.
4. 6 explicit 2-realizer constructions per pattern (each a concrete 8-edge poset
   on f0..f4; give two literal total orders, verify via
   `two_realizer_from_fin_ranks` / `n5_two_realizer_framework`).
   The count-9 twin-rank does NOT directly apply (2 incomparable pairs), but each
   fixed pattern's realizer is a finite explicit check.
Then counts 5/6/7 replicate with `enum_k_none 10 {5,4,3}` + their iso-classes.

## Count-8 CLOSED end-to-end — admit 5 → 4 (2026-05-30)

`n5_edge_count_8_two_realizer` (EdgeCount8.v) is now **Qed**; the whole project
is green (`@check`). The full abstract wiring landed this session:

- `EdgeCount8_cover.v` — `five_distinct_cover` (5 distinct elts in a cardinal-5
  carrier exhaust it; reusable pigeonhole via `carrier_5_destructure`).
- `EdgeCount8_eccov.v` — `edge_count_5_cover_invariant` (permutation invariance
  of `edge_count_5`; 5^5, proved once). This is what lets each closure be a
  light **25-case** `(x,y)` enumeration instead of a 5^7 blow-up — the first
  attempt at a K32mm-style 5^7 closure timed out at 540s; the invariance lemma
  fixed it.
- `EdgeCount8_c1.v` .. `EdgeCount8_c6.v` — the 6 per-pattern handlers. Each:
  light closure (edge_count=8 over p..t ⟹ a 9th strict edge gives 9 distinct
  indicators = 1 in a sum of 20 = 8, contradiction) + explicit L1/L2 rank
  vectors fed to `n5_two_realizer_framework` (via `five_distinct_cover` for the
  cover). The count-9 twin-rank does NOT apply (2 incomparable pairs); explicit
  ranks per pattern were computed by hand and verified.
- `N5Iff.v` — 6 `is_c8_k_b_to_exists` lifting lemmas (8-edge analogue of the
  count-4 ones). NB: `apply strict_b_R2_matrix_iff in H1..H8` spawns 88 section
  side goals (`a<>b` etc.) closed by a final `all: assumption`; the Ltac form
  fails because `;`-chaining sprays `exists` onto the side goals — use `only 1:`
  or inline.
- `EdgeCount8.v` — dispatcher: 6 `classic` shape tests → per-pattern handler;
  residual closed by `exhaustive_8edge` on `R2_matrix` (count transported via
  `R2_matrix_edge_count_eq`) + the iff lemmas contradicting the refutations.

## ADMIT #1 FULLY CLOSED — all edge counts 1–9 done (2026-05-30)

`n5_residual_classes_two_realizer` (N5DispatcherShapes.v) is admit-free —
`Print Assumptions` shows only `classic`, `functional_extensionality_dep`,
`constructive_definite_description`, `Extensionality_Ensembles` (standard
classical axioms); NO `Admitted`, no `n5_edge_count_*`, no Trotter.

Counts 5/6/7 were closed exactly like count-8, fully mechanized via a Python
generator + a Coq extractor `N5Extract{5,6,7}.v` (lexmin iso-class canonical
shapes + machine-found L1/L2 2-realizer rank vectors). Per count:
- count-7: 9 iso-classes → `EdgeCount7_c1..c9` + `N5Reflect7` (8-chunk
  `coverage_7`/`exhaustive_7edge`) + 9 N5Iff lemmas + `EdgeCount7` dispatcher.
- count-6: 12 iso-classes → analogous (`EdgeCount6_c1..c12`, ...).
- count-5: 10 iso-classes → analogous (`EdgeCount5_c1..c10`, ...).
All handler closures are the light 25-case argument (a (K+1)-th distinct strict
indicator would exceed `edge_count = K`); reusable helpers `five_distinct_cover`
and `edge_count_5_cover_invariant` shared across all counts. Whole project green
(`@check`); dispatcher Qed-verified.

## Remaining admits: 1 (was 4)

- `RemovablePairs.v:1834` — `trotter_coverage_via_extremality` (admit #2, the
  general-n Trotter coverage keystone; the only remaining gap for an admit-free
  `hiraguchi_bound`).

### Trotter admit — precise decomposition (analysis 2026-05-30)

Exact remaining claim (parts (i)/(ii) of `trotter_per_L_acyclic_covering_family`
already Qed): for every boundary CP `(p,q)`, some `L'∈r'` has
`(p,q) ∈ greedy_acyclic_subset S' x' y' L' nil boundary`.

A proof (Trotter 1992 Ch.6 Thm 6.1) needs three pieces, NONE shallow:
1. **greedy-rejection ⟹ path.** `aug_cycle_implies_step3_path` (Qed) does only
   the singleton `B=[(p,q)]` case (cycle ⟹ `step3` path `p→q`). Need the general
   `B=(p,q)::acc` case: a path in `R ∪ L' ∪ {x'→y'} ∪ reversed(acc)`. UNWRITTEN.
2. **path ⟹ refining critical pair** `(p',q')` with `R p' p ∧ R q q'` ("Trotter's
   algebra", the cycle↔CP correspondence). UNWRITTEN.
3. **refining CP + boundary endpoint-sharing + extremality(x',y') ⟹ False.**
   Uses `IsExtremalCP` (exists). Connection UNWRITTEN.

No SOUND progressive refinement (smaller admit + Qed wrapper) found:
- "∃L' makes the whole boundary acyclic ⟹ greedy accepts all" — premise is FALSE
  in general (different boundary pairs need different L'; the per-L' family is
  exactly to avoid this). 
- singleton-acyclicity ⤏ greedy-acceptance (greedy accumulator is order-dependent).

Conclusion: genuinely irreducible research-grade content; multi-session
formalization of the augmented-digraph cycle↔CP algebra + extremality argument.
Do NOT fabricate a relabeling admit. The achievable milestone (admit #1, the
entire n=5 base case) is done and verified above.

### Trotter admit — PROGRESSIVE REFINEMENT landed (2026-05-30)

Piece 1 (greedy-rejection ⟹ path) is now fully Qed, and the admit was
soundly refined (the greedy plumbing is no longer in the admit):
- `aug_cycle_implies_acc_path` (Qed): generalizes `aug_cycle_implies_step3_path`
  from singleton `[(p,q)]` to arbitrary already-acyclic accumulator `acc`
  (cycle must use the new `q→p` edge ⟹ `aug_step ... acc` path `p→q`; no poset
  hyps — acyclicity of `acc` replaces them).
- `greedy_subset_contains_acc` + `greedy_reject_path` (Qed): a pair rejected by
  the greedy walker is never re-accepted, so rejection ⟹ ∃ acyclic `acc'` (a
  boundary subset) with an `aug_step ... acc'` path `p→q`.
- `trotter_coverage_via_extremality` is now **Qed**, a reduction (via `NNPP`,
  `realizer_linear`, `aug_acyclic_nil`, `greedy_reject_path`) to:
- **`trotter_path_family_impossible`** (the SOLE remaining admit,
  RemovablePairs.v:1986): for a boundary `(p,q)`, NOT every `L'∈r'` can admit an
  acyclic `acc'` with an `aug_step ... acc'` path `p→q`. This statement no
  longer mentions `greedy_acyclic_subset` — it is purely the augmented-digraph
  path family + extremality. Remaining work = pieces 2 (path ⟹ refining CP, the
  cycle↔CP algebra) + 3 (refining CP + boundary + extremality ⟹ False).
- SOUNDNESS FIX: the admit must constrain `acc' ⊆ boundary` (reversed boundary
  CPs) — with an arbitrary acyclic `acc'` the statement is likely false (e.g.
  `acc'=[(q,p)]` adds the edge `p→q` directly). `greedy_reject_path` now records
  `(forall pq, In pq acc' -> In pq acc \/ In pq rest)`, and that `⊆ boundary`
  hypothesis is threaded into `trotter_path_family_impossible`. So the admit is
  now Trotter's TRUE claim, not a too-general (false) one.

`trotter_path_family_impossible` (RemovablePairs.v:~2085) is the sole remaining
admit; it mentions only `aug_acyclic`/`aug_step`/`IsExtremalCP` (no greedy). Its
proof is the multi-session formalization of Trotter 1992 Thm 6.1's cycle↔CP
algebra + extremality elimination — genuinely irreducible; do NOT rush it.

### Piece-2 infrastructure landed (Qed, 2026-05-30)

Toward the path ⟹ refining-CP direction:
- `aug_step_nil_mono`, `aug_rt_nil_mono` — `step3 = aug_step…nil` embeds into any
  `aug_step…acc` (and its refl-trans closure).
- `aug_step_rev_edge` — `(c,d)∈acc` gives the `aug_step…acc` edge `d→c`.
- `aug_path_step3_or_via_acc` — an `aug_step…acc` path `p→q` is EITHER a pure
  `step3` path OR threads through the last reversed-boundary edge `d→c`
  (`(c,d)∈acc`), splitting into an `aug` path `p→d` and a pure `step3` path
  `c→q`. This isolates the role of the reversed boundary CPs in any augmenting
  path.

### Trotter steps 1–2 + base lemmas landed (Qed, 2026-05-30, budgeted attempt)

15 sound lemmas now bracket the admit: greedy→path (`greedy_reject_path`), path
decomposition (`aug_path_step3_or_via_acc` + mono helpers), `aug_no_backward_S'`,
`two_cp_share_top/bottom_incomp` (step 1), `clos_trans_last`/`aug_path_into_notS'`
(step 2), `rt_R_collapse`/`cp_no_R_path` (an obstruction path can't be R-only).

KEY RECONSTRUCTION FINDINGS (from the budgeted attempt):
- The file's authors marked this "delicate but standard; mechanizing it is left
  for future work" and gave a 4-element counterexample showing the constant
  witness `B_of L' = boundary` is FALSE — coverage is genuinely L'-dependent.
- The obstruction (path `p→q`) cannot be R-only (`cp_no_R_path`); it must use an
  `L'`-edge / the forced `x'→y'` / a reversed boundary edge. In the counterexample
  the culprit is an incomparable S'-pair `(z,q)` the realizer can flip.
- Closing it needs the alternating-cycle ⟹ refining-CP extraction via a
  well-founded **path induction**, then extremality — a substantial standalone
  mechanization (the deferred "future work"), not reconstructable here to sound
  formalizable precision. NOT fabricated.

REMAINING (the genuine core): combine, across ALL `L'∈r'` (using the realizer
intersection `∩L' = R|S'`), the per-`L'` paths with the extremality of
`(x',y')` to extract a critical pair refining `(x',y')` — contradiction. This is
the simultaneous-over-realizer argument and is the irreducible content; it needs
the refining-CP extraction lemma + the extremality-elimination lemma, neither of
which has a short proof. Session count of Trotter Qed lemmas added: 7
(pieces 1 + 2-start) + the sound refinement.

## (historical) Remaining admits: 4

- `RemovablePairs.v:1834` — `trotter_coverage_via_extremality` (admit #2, deep).
- `N5Exhaustive/EdgeCount{5,6,7}.v:36` — counts 5/6/7 of the n=5 base (admit #1).

**Counts 5/6/7 — replicate the count-8 pipeline.** Each needs: (0) extract the
iso-class canonical shapes for that edge count (count-8's 6 shapes were
pre-extracted in N5Reflect8.v; counts 5/6/7 shape lists are NOT yet computed —
this is the prerequisite, more classes per count: 5 has 5 incomparable pairs,
6 has 4, 7 has 3); (1) `enum_k_none 10 {5,4,3}` + chunked `native_cast`
coverage; (2) `exhaustive_{5,6,7}edge` via the SAME `M_assign`/
`mat_of_M_assign`/`*_pairs10`/`edge_count_5_cover_invariant`/`five_distinct_cover`
apparatus (all reusable); (3) per-pattern handlers (explicit ranks); (4) iff
lemmas; (5) dispatcher. The reusable helpers (`five_distinct_cover`,
`edge_count_5_cover_invariant`, the count/bridge lemmas) already exist.

## FALSE ADMIT FOUND + FIXED — hiraguchi_bound now sound (2026-05-30)

**Discovery.** The last Trotter admit `trotter_path_family_impossible` (the
boundary-CP coverage core) was FALSE as stated, not merely hard. It claimed
that for an ARBITRARY d'-realizer `r'` of the residual, every boundary critical
pair is covered (rejected from the augmented closure for some `L' ∈ r'`).

**Counterexample (5 elements, `posets/dimension/TrotterCounterexample.v`, Qed):**
model `Rel a b := a=b \/ (a=eX /\ (b∈{eD1,eD2}))` — i.e. `eX < eD1, eX < eD2`,
with `eY, eQ` otherwise isolated.
- `(eX,eY)` is an extremal critical pair; residual `S' = {eD1,eD2,eQ}` is a
  3-antichain, realized by `r' = {La, Lb}` (`La: d1<q<d2`, `Lb: d2<q<d1`).
- Boundary CP `(eX,eQ)`: under EVERY `L' ∈ r'` there is an augmenting path
  `eX → eD_i → eQ` (R-edge then L'-lift), so the forced cycle `eX → S' → eQ → eX`
  makes `(eX,eQ)` coverable by NO `L'`. All premises of the admit hold; its
  conclusion (`False`) is absurd.

**Why it was wrong.** Coverage holds only for a *coordinated* (removable-pair,
realizer) choice — the genuine Trotter content — not for an arbitrary extremal
CP + arbitrary realizer. The lift-construction proof over-generalized.

**Fix (commit b6d9069).**
- Deleted the unsound chain: `trotter_path_family_impossible`,
  `trotter_coverage_via_extremality`, `trotter_per_L_acyclic_covering_family`,
  `trotter_boundary_existence`, `trotter_boundary_coverage`.
- Rerouted `non_antichain_removable_pair_exists` to an honest `Admitted` of the
  TRUE classical Hiraguchi/Trotter removable-pair theorem. Note that
  `IsRemovablePair x y  ⟺  x≠y ∧ dim R ≤ dim(R−{x,y})+1`; the *statements* of
  `non_antichain_removable_pair_exists`, `removable_pair_exists`, and
  `hiraguchi_bound` are all true — only the prior PROOF was unsound.

**Verification.** Whole-project build green (`@all`, -j4). `Print Assumptions
hiraguchi_bound` lists exactly ONE non-standard assumption,
`non_antichain_removable_pair_exists`, plus the development's standard classical
axioms (classic, prop/functional ext, proof_irrelevance, choice,
Extensionality_Ensembles). No false step remains.

## Remaining admits: 1 (honest, true)

- `RemovablePairs.v` — `non_antichain_removable_pair_exists`: the non-antichain
  case of Hiraguchi's removable-pair theorem (classical, true; deep). This is
  now the SOLE dimension admit. Admit #1 (the entire n=5 base, counts 1–9) is
  closed and admit-free.

## DEAD END IDENTIFIED + correct path found (2026-05-30, cont.)

**The remaining admit is the OPEN Removable Pair Conjecture.**
`non_antichain_removable_pair_exists` (= ∃ removable pair for n≥4 non-antichain
non-chain) is exactly the Removable Pair Conjecture (Bogart–Trotter 1971), which
is OPEN for integer dimension (West's open-problems list). It CANNOT be proven;
`hiraguchi_helper`'s removable-pair induction is a dead end. (Confirmed: n=3 is
trivially removable, so existence ∀ n≥4 would settle the |P|≥3 conjecture.)

**(B) done (commit 0071a56):** `RemovablePairConjecture` formulated as an
unasserted `Prop` + docs/INDEX.md "Open problems" note; admit re-documented as
OPEN; memory updated. Nothing depends on the conjecture statement.

**(A) path found (commit pending):** Hiraguchi `dim ≤ ⌊n/2⌋` is a THEOREM proven
INDEPENDENTLY of the conjecture (Hiraguchi/Kimble/Trotter). The "modern proof"
(Trotter survey Thm 5.2) = two lemmas:
- **Lemma 5.4** `dim ≤ width` — ✅ ALREADY in repo (`dimension_le_width`, Qed).
- **Lemma 5.6** `dim ≤ max{2,|P−A|}` for a maximal antichain `A` — the SOLE new
  content (Kimble [33], Trotter [46]).
Combination is airtight arithmetic. Plan: `docs/superpowers/plans/2026-05-30-
hiraguchi-direct-proof.md`. Reference PDF: `docs/references/trotter-149-*.pdf`.

**GATING next step (Task 0):** pin down Lemma 5.6's realizer construction
("split all points of `P−A`", needs the tight `max{2,n}`; iterating one-point
removal `dim ≤ dim(P−x)+1` gives `n+2`, OFF BY ONE) from Trotter [46]/Kimble [33]
or reconstruct + verify on `S_k`, BEFORE writing Coq. Then formalize 5.6, wire
`hiraguchi_bound` to `dim≤width + 5.6`, drop the conjecture dependency.

## Remaining admits: 1 (OPEN conjecture — to be made unused, not closed)
- `non_antichain_removable_pair_exists` = Removable Pair Conjecture (OPEN).
  Target: make `hiraguchi_bound` independent of it via the Lemma 5.6 route, then
  it becomes the standalone documented `RemovablePairConjecture`.

## Direct Hiraguchi proof — formalization started (2026-05-30, cont.)

New, sound, all building (commits 6faa95f, 743ff6d, +lift_high):
- `AntichainDimBound.v`: `hiraguchi_combine` (Qed) — arithmetic core
  `4≤n → w+m=n → d≤w → d≤max{2,m} → d≤n/2`. `dim_le_antichain_complement`
  (Admitted, TRUE — Trotter 1975 Thm 2, full sketch in-file).
- `OnePointRemoval.v`: subtype `X−p`, lifted suborder `Llift` (+ refl/antisym/
  trans/total/extends via proof_irrelevance), and BOTH block orders proven
  linear extensions of R (Qed): `lift_low_is_linext` (zlow: Down|{p}|rest),
  `lift_high_is_linext` (zhigh: rest|{p}|Up). Formulated as `lex(zone,Llift)`.

REMAINING for `one_point_removal : dim R ≤ 1 + dim(X−p)`:
1. `lift_keep` — a linear extension of R restricting to `Llift L` on `X−p`
   (p inserted preserving L). Plan: Szpilrajn on `clos_trans (R ∪ Llift L)`;
   the closure is antisymmetric (a cycle through p forces a'=a'' with
   a'∈D(p),a''∈U(p) ⟹ a'=p, contra). [next]
2. Realizer assembly: `rB = Im (rQ ∖ {L_d}) lift_keep ∪ {lift_low L_d,
   lift_high L_d}`, |rB| ≤ d'+1; pick L_d ∈ rQ (d'≥1; d'=0 ⟹ |X|≤2, dim≤1).
3. Coverage (IsRealizer ∩rB = R): S-S pairs by lift_keep(L_i≠L_d) or
   lift_low/high(L_d); p-pairs by lift_low (p below non-D) + lift_high
   (p above non-U). [the combinatorial core]
4. `one_point_removal` via dimension_is_minimum.
Then: base case |X−A|=2 ⟹ dim≤2; polymorphic induction on |X−A| for
`dim_le_antichain_complement`; rewire `hiraguchi_bound`.

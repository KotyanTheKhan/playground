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

## Admit count: 2 (was 3)

Remaining honest admits, both large research-grade efforts:
- `N5DispatcherShapes.v:38` — `n5_residual_classes_two_realizer` (n=5 residual
  catch-all; edge counts ~5-9 not yet classified; ~60 dispatcher files route
  here).
- `RemovablePairs.v:1834` — `trotter_coverage_via_extremality`.

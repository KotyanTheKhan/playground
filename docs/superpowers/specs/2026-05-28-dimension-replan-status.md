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

## R2 remaining work (TODO for next session)

The 10 `is_<pattern>_b_iff` lemmas are NOT done.  Earlier partial attempt at `N5Transport_iff.v` had only 2 of 10 patterns and a slow `find_fifth_distinct` proof (1024-case cascade) that hangs.  Deleted.

**Next-session strategy for the 10 iff lemmas:**

1. Each pattern in its own file: `N5Iff_<pattern>.v`.  Total ~10 small files.
2. Use a shared helper file `N5Iff_Common.v` for:
   - `find_fifth_distinct` — replace the 1024-case cascade with a clean 5-element pigeon argument (use `In _ all5` + `NoDup` + length argument).
   - `extract_pattern` tactic.
   - `mk_perm5_in` tactic.
3. Each `N5Iff_<pattern>.v` follows the same template; copy-modify.
4. Target: each file < 50 lines, builds < 10s.

## R3 status

Blocked on R2's iff lemmas.  Once those are done, R3 is the mechanical wire-in (~2 hr per the design).

## Admit count: 3 (unchanged)

Phase R will close admits #1 + #3 once R2 iff lemmas land and R3 wires them in.

# Design: Dimension Proof Replan — Closing All Three Admits

**Date:** 2026-05-28
**Branch:** `dimension_finish`
**Supersedes:** `docs/superpowers/plans/2026-05-28-close-final-admits.md` (Track N portion only).
**Companion docs:**
- `docs/superpowers/specs/2026-05-28-fin5-reflection-design.md` (Phase R technical design)
- `docs/superpowers/specs/2026-05-28-status.md` (existing status snapshot)

---

## Goal

Zero admits in `posets/dimension/`. `hiraguchi_bound` fully `Qed`.

## Current state

Three admits:

| # | Admit | Location |
|---|---|---|
| 1 | `n5_residual_classes_two_realizer` | `posets/dimension/N5DispatcherShapes.v:38` |
| 2 | `trotter_coverage_via_extremality` | `posets/dimension/RemovablePairs.v:1842` |
| 3 | (anonymous exhaustiveness) | `posets/dimension/N5Exhaustive/EdgeCount4.v:221` |

Dependency chain into `hiraguchi_bound`:

```
hiraguchi_bound (Qed)
 ├── hiraguchi_helper n≥6
 │    └── ... → trotter_per_L_acyclic_covering_family
 │             └── trotter_coverage_via_extremality   ← #2
 └── hiraguchi_small_case n=5 non-antichain non-chain
      └── n5_nonantichain_nonchain_two_realizer
           └── n5_residual_classes_two_realizer        ← #1
                └── (EdgeCount4 dispatcher route)
                     └── exhaustiveness gap            ← #3
```

Both #1 and #2 must close for `hiraguchi_bound` to be Qed. #3 is a sub-problem on #1's route.

## Strategy

Two phases, sequential:

- **Phase R (Reflection):** close #1 and #3 together via `Fin.t 5` boolean reflection. Replaces the 20-iso-class cascade (Sessions N6-N9 of the prior plan) with a single computational layer + transport.
- **Phase T (Trotter):** close #2 via the existing T1–T5 staging (`Trotter/*.v`). The just-landed helper `aug_cycle_implies_step3_path` plugs into T2.

### Why this ordering (R before T)

- Phase R closes 2 of 3 admits faster than Phase T closes 1. Clear progress milestone after 3-4 sessions.
- Phase R is computational; success/failure detectable from a 30-min probe (R0). Risk is bounded.
- Phase T touches the central acyclicity scaffolding in `RemovablePairs.v`; doing it after Phase R avoids interleaving file edits across both tracks.

### Why reflection for n=5 (not cascade)

- Cascade requires N6 (`EdgeCount5.v`), N7 (`EdgeCount6_9.v`), N8 (`Exhaustive.v`), N9 (wire-in) — 4 more sessions, plus #3 remains open until N5 cleanup.
- Reflection collapses #1 and #3 into one mechanism. Once `exhaustive_4edge` is `vm_compute`-proved, the same template extends to `exhaustive_5edge`, `exhaustive_6edge`, etc. trivially.
- The previous OOM incident (cartesian destruct + `try ... eauto`) is structurally avoided by reflection — `vm_compute` is single-threaded kernel computation, not search.

## Decomposition by complexity

Per `long-running-formalization` Discipline 1:

**Mechanical-Qed (any agent can write):**
- `M5`, `is_poset_b`, `strict_b`, `edge_count_b` definitions.
- `R2_matrix` construction.
- 20 pattern booleans `is_<pattern>_b`.
- T1's CP-refinement preorder setup (uses existing `cp_le`).

**Iterable-Qed (template-replicated):**
- 20 `is_<pattern>_b_iff` lemmas (one shape per pattern; subagent-parallelizable in R2).
- T2's per-greedy-step characterization.

**Irreducible deep claims:**
- `exhaustive_4edge` — relies on `vm_compute` feasibility (R0 gate).
- T3 shadow-CP extraction (Trotter Ch.6 geometric content).
- T4 extremality contradiction (depends on T1 + T3 being usable).

## Phase R — Reflection (closes #1 + #3)

### R0: Feasibility probe (30 min, no commit)

- Create `posets/dimension/N5Exhaustive/N5Reflect_probe.v` (scratch).
- Define `is_poset_b` on `M5 = Fin.t 5 → Fin.t 5 → bool`.
- Test 1: `Eval vm_compute in is_poset_b (fun _ _ => false).` Time it.
- Test 2: `Eval vm_compute in length (filter is_poset_b <enumerate small slice of M5>).` Time it.
- Test 3: Sketch the full `forall M : M5, is_poset_b M = true → ...` proof shape and `vm_compute` on a single instance. Estimate full-enumeration time.

**Decision rule:**
- **GO** (full enumeration tractable, < 60s in kernel) → R1.
- **FALLBACK** (full enumeration > 60s) → R1' (edge-subset enumeration over ~12.6K matrices instead of ~33M).
- **ABORT** (both > 60s) → revert to cascade plan (N6–N9).

### R1: `N5Reflect.v` — defs + `exhaustive_4edge` (3-4 hr)

- File: `posets/dimension/N5Exhaustive/N5Reflect.v`.
- Defs: `M5`, `is_poset_b`, `strict_b`, `edge_count_b`, 20 pattern booleans.
- Lemma: `exhaustive_4edge : forall M, is_poset_b M = true → edge_count_b M = 4 → is_4claw_up_b M = true \/ ... \/ is_K32mm_b M = true.`
- Proof: `vm_compute` (GO path) or structured enumeration over edge-subsets (FALLBACK).
- Target: < 500 lines, Qed < 2 min.
- Build with `mise exec -- dune build -j 2` (memory safety).

**Admit-introduction guard:** no new admits expected. If `exhaustive_4edge` needs to be admitted (e.g., vm_compute blows kernel), apply the admit-introduction checklist + invoke `proof-skeptic`.

### R1' (fallback only): edge-subset enumeration (3-4 hr)

- Enumerate the 25 ordered pairs (Fin.t 5 × Fin.t 5), take sublists of size ≤ 4, restrict to those forming a poset with edge count 4. ~12.6K candidates.
- Use a `Fixpoint` over the list to certify each surviving candidate matches one pattern.

### R2: `N5Transport.v` — bridge to abstract `B` (3 hr)

- File: `posets/dimension/N5Exhaustive/N5Transport.v`.
- `Section Transport` with `Context {B : Type} (R2 : B -> B -> Prop) ...`, 5 element vars + `Hcov` + pairwise-distinct.
- `to_fin : B → Fin.t 5` (via classical choice over Hcov).
- `from_fin : Fin.t 5 → B`.
- `R2_matrix : M5`.
- `R2_matrix_is_poset`, `R2_matrix_edge_count_eq`.
- 20 `is_<pattern>_b_iff` lemmas — **subagent-parallelizable**: dispatch each pattern as an independent task, since each follows the same shape against its abstract `exists` definition in the cascade.

### R3: Wire into EdgeCount4 + N5DispatcherShapes (2 hr)

- Replace `Admitted.` at `EdgeCount4.v:221` with `apply (exhaustive_4edge ... via transport)`. Discharges #3.
- Replace `Admitted.` at `N5DispatcherShapes.v:38` by composing all `exhaustive_<k>edge` (or only `exhaustive_4edge` if the dispatcher already routes ≤3 and ≥5 elsewhere). Discharges #1.
- `mise build` green. Status doc updated. Commit.

**Phase R total: 9-12 hr / 3-4 sessions. Admit count: 3 → 1.**

## Phase T — Trotter (closes #2)

Follows the existing T1-T5 plan from `2026-05-28-close-final-admits.md`, with one modification at T2 (use the new helper).

### T1: `Trotter/CoverageRefinement.v` (3 hr, LOW risk)

- `cp_le_strict` (strict variant of existing `cp_le`).
- `cp_le_strict_irreflexive`.
- `cp_le_strict_finite_chain_terminates` via finite-induction on remaining-CP count.

### T2: `Trotter/GreedyExcluded.v` (3 hr, MED risk)

- `greedy_excluded_iff_cycle`: `(p, q) ∉ greedy_acyclic_subset ... boundary` iff adding `(q, p)` to current acc creates a cycle.
- Plugs in `aug_cycle_implies_step3_path` (already landed in `RemovablePairs.v`).
- Risk: helper's statement uses `clos_refl_trans step3 p q`; T2 may need a thin adapter.

### T3: `Trotter/CycleStructure.v` (4 hr, HIGH risk)

- `cycle_implies_shadow_cp`: a cycle in `aug_step` through `(q, p)` exposes a CP `(p', q')` with `R p' p ∧ R q q'`.
- `shadow_cp_in_accumulator`: shadow CP was added in the greedy walker's earlier step.
- Deepest mathematical content. If session 1 fails to close it: refactor (Discipline 4) into smaller admits, narrow and retry next session.

### T4: `Trotter/ExtremalityContradiction.v` (3 hr, MED risk)

- `shadow_chain_terminates_at_extremal` via T1's well-foundedness.
- `cp_chain_to_extremal_means_eq`.
- Final contradiction: chain length > 0 + extremality → False.

### T5: `Trotter/CoverageProof.v` + wire-in (2 hr, LOW risk)

- `trotter_coverage_main` (Qed) composes T1-T4 into the full statement.
- In `RemovablePairs.v`: replace `Admitted.` at line 1842 with `Proof. exact trotter_coverage_main. Qed.`.

**Phase T total: 15 hr / 5 sessions. Admit count: 1 → 0.**

## Final integration (1 hr)

- `grep -rn "^[[:space:]]*Admitted\.$" posets/` returns empty.
- `mise build` green.
- Update `docs/INDEX.md` to remove the admit notes.
- Commit final state with verification log.

## Risk register

| Risk | Phase | Mitigation |
|---|---|---|
| `vm_compute` over 2^25 matrices blows kernel | R0/R1 | R0 probe gates R1. FALLBACK to edge-subset enumeration. ABORT path reverts to cascade. |
| Pattern boolean ↔ abstract `exists` shape mismatch | R2 | Each `is_<pattern>_b_iff` is its own Qed; mismatch fails locally. Subagent-parallel dispatch isolates failures. |
| T3 shadow-CP analysis irreducible in one session | T3 | Discipline 4 progressive refinement: factor into smaller admits, narrow per session. Cap at 3 sessions then re-plan via `proof-skeptic`. |
| OOM during memory-heavy file compile | any | Build with `-j 2`. Cartesian-destruct + `eauto` chains forbidden (see `feedback_coq_oom_eauto_cascade.md`). |
| Hidden circularity between #1 and #2 | all | Cross-track dependency check (`grep` callers of each Lemma); transitively verify no Qed-chain depends on its own admit. |

## Session-management rules

- **Status doc** `docs/superpowers/specs/2026-05-28-dimension-replan-status.md` updated at every session boundary with commit hash + admit delta.
- **Admit-introduction checklist** + `proof-skeptic` agent before every new `Admitted`.
- **When-to-stop** (Discipline 5): after 3 consecutive admit-count-unchanged sessions on the same phase, stop and invoke `proof-skeptic` for re-plan.
- **Build memory cap**: `mise exec -- dune build -j 2` for any session compiling reflection or T3 files.
- **R0 is non-skippable**: no R1 commit until R0 confirms feasibility.

## Grand total

**25-28 hr over 9-10 sessions.**

| Phase | Sessions | Hours | Admit delta |
|---|---|---|---|
| R (Reflection) | 3-4 | 9-12 | -2 (#1, #3) |
| T (Trotter) | 5 | 15 | -1 (#2) |
| F (Integration) | 1 | 1 | — |
| **Total** | **9-10** | **25-28** | **-3 → 0 admits** |

## Useful file paths

- This design: `docs/superpowers/specs/2026-05-28-dimension-replan-design.md`
- Reflection technical design: `docs/superpowers/specs/2026-05-28-fin5-reflection-design.md`
- Existing plan (cascade portion superseded): `docs/superpowers/plans/2026-05-28-close-final-admits.md`
- Reflection target dir: `posets/dimension/N5Exhaustive/`
- Trotter target dir (to create): `posets/dimension/Trotter/`
- Helper just landed: `aug_cycle_implies_step3_path` at `posets/dimension/RemovablePairs.v:1651`

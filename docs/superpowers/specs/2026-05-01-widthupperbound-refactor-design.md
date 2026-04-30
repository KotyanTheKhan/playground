# WidthUpperBound.v refactor — design

**Date:** 2026-05-01
**Target file:** `posets/dilworth/WidthUpperBound.v` (currently 2785 lines, single `Section DilworthBackward`)
**Out of scope:** `Helpers.v`, `Hall.v`, `CardinalLemmas.v`, `Definitions.v`, `WidthLowerBound.v`, `DilworthTheorem.v`. No proof simplifications beyond structural extraction. `DilworthB`'s public type is preserved exactly.

## Motivation

Two near-twin lemmas, `above_chain_assignment_exists` (~900 lines) and `below_chain_assignment_exists` (~780 lines), make up ~63% of the file. They differ only in the direction of one comparison: above uses `R y x` (predecessor), below uses `R x y` (successor). They are duals under `flip R`. Beyond the duplication, both proofs are large monoliths held together by long `assert ... by { ... }` blocks (30–100 lines each), which makes them hard to read and harder to modify.

Goals:
1. Split `WidthUpperBound.v` into focused files under a new `posets/dilworth/upper_bound/` subdirectory.
2. Prove the assignment lemma **once**, parameterized on the relation direction (`flip R` instantiation gives the dual).
3. Replace anonymous `assert` blocks inside the kernel proof with named local lemmas.
4. Keep `DilworthB`'s public signature identical; keep all externally-referenced lemma names identical.
5. Build stays green at every commit; verification via `mise run build-posets`.

## External call sites (unchanged)

`DilworthB` is referenced from:
- `posets/dilworth/DilworthTheorem.v`
- `posets/dilworth/Examples.v`
- re-export in `posets/dilworth/Package.v`

Other lemmas that are exported through `Package.v` or the current `WidthUpperBound.v` keep their names. Internal/new names live under `Dilworth.upper_bound.*`.

## File layout

```
posets/dilworth/
  WidthUpperBound.v          ← facade: Require Export Dilworth.upper_bound.Backward.
  dune                       ← + (include_subdirs qualified)
  upper_bound/
    Slices.v
    HallDefect.v
    BaseCases.v
    Iter.v
    HallKernel.v
    Cover.v
    Merge.v
    Backward.v
```

### Per-file contents

| File              | Contents                                                                                                                                      | Approx lines |
|-------------------|-----------------------------------------------------------------------------------------------------------------------------------------------|--------------|
| `Slices.v`        | `la_in_Above`, `la_in_Below`, `largest_antichain_in_Above`, `largest_antichain_in_Below`, `above_contains_la`, `below_contains_la`, `sub_in_above_or_below`, `la_largest_in_above`, `la_largest_in_below`, `la_card_le_sub`, `above_card_lt`, `below_card_lt`, `antichain_lb_for_chain_cover` | ~300 |
| `HallDefect.v`    | `StrictSucc`, `StrictPred`, `dilworth_hall_defect`, `dilworth_hall_defect_pred`, `min_elements_eq_la`                                          | ~150         |
| `BaseCases.v`     | `empty_antichain_contradiction`, `singleton_antichain_is_chain`, `width_one_implies_chain`, `singleton_chain_cover`, `antichain_singleton_cover`, `below_fiber_cover_cardinal` | ~180 |
| `Iter.v`          | `chain_root_aux`, `depth_aux` (Fixpoints) and the parameter-free properties about iteration: `Hiter_eq` analogue, `Hdepth_inr/inl/le_gen`, etc. | ~150 |
| `HallKernel.v`    | The parameterized assignment kernel + its inner lemmas (see "Kernel" below)                                                                    | ~700         |
| `Cover.v`         | `above_chain_assignment_exists` (kernel @ `R`), `below_chain_assignment_exists` (kernel @ `flip R`), `chain_cover_above_existence`, `chain_cover_of_above`, `chain_cover_of_below`, `extend_cover_above`, `extend_cover_below` | ~120 |
| `Merge.v`         | `merge_above_below_covers`                                                                                                                    | ~250         |
| `Backward.v`      | `dilworth_inductive_step`, `DilworthB`                                                                                                        | ~120         |
| `WidthUpperBound.v` (facade) | `Require Export Dilworth.upper_bound.Backward.` and any other re-exports needed                                                  | ~10          |

Total: ~2000 lines (down from 2785), with the largest single file at ~700.

## Kernel design

The kernel proves the above-style assignment for an abstract poset `R'`:

```coq
(* upper_bound/HallKernel.v *)
Section Kernel.
  Context {A : Type}.
  Context (R' : A -> A -> Prop) `{IsPoset A R'}.

  Lemma chain_assignment_kernel : forall (sub la : Ensemble A) (w : nat),
    IsLargestAntichain R' sub la w ->
    Included A sub (Above R' la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R' (f x) x) /\
      (forall a, In A la a -> IsChain R' (fun x => In A sub x /\ f x = a)).
End Kernel.
```

`above_chain_assignment_exists` becomes a one-line application with `R' := R`. `below_chain_assignment_exists` applies the kernel with `R' := flip R`, using these dualities (all available as definitional or one-line rewrites):

- `Above (flip R) la = Below R la`
- `IsAntichain (flip R) la ↔ IsAntichain R la` (the definition is symmetric in `R` vs `flip R`)
- `IsLargestAntichain (flip R) sub la w ↔ IsLargestAntichain R sub la w`
- `IsChain (flip R) C ↔ IsChain R C` (definition symmetric)
- `(flip R) (f x) x ↔ R x (f x)`

### Prerequisite: `Instance flip_IsPoset`

The kernel section requires `IsPoset (flip R)`. We need to verify whether `PosetClasses.v` already provides this; if not, the first step of the refactor adds:

```coq
#[export] Instance flip_IsPoset {A} (R : A -> A -> Prop) `{IsPoset A R}
  : IsPoset (flip R) := { ... }.   (* refl/trans/antisym all symmetric *)
```

This is the only addition outside the dilworth subtree, and it's a one-screen change in `PosetClasses.v`.

### Inner lemmas of the kernel

The current 900-line proof body is held together by these `assert ... by { ... }` blocks. Each becomes a named `Lemma` inside `HallKernel.v`:

| Local name                      | Statement (informal)                                                                       |
|---------------------------------|---------------------------------------------------------------------------------------------|
| `inl_image_cardinal`            | For any `S : Ensemble A` with `cardinal A S n`, the set `{inl y : sum A A | y ∈ S}` has cardinal `n`. |
| `inr_image_cardinal`            | Same for `{inr a | a ∈ T}`.                                                                |
| `Y_cardinal`                    | `cardinal (sum A A) Y (nx + w)` for `Y = inl-image(sub) ⊎ inr-image(la)`.                  |
| `nbrs_aug_neighbors_eq`         | `set_neighbors nbrs_aug S = inl-image(StrictPred sub S) ⊎ inr-image(la)`.                  |
| `hall_condition_holds`          | The `HallCondition sub nbrs_aug` hypothesis, discharged via `dilworth_hall_defect_pred`.   |
| `la_assigned_to_dummy`          | `∀ a ∈ la, ∃ k ∈ la, m_aug a = inr k`. Uses `min_elements_eq_la`.                          |
| `dummy_target_in_la`            | If `m_aug z = inr d` for `z ∈ sub`, then `z ∈ la`. (The π-surjectivity argument.)          |
| `chain_terminates`              | `∀ x ∈ sub, chain_root_aux m_aug nx x ∈ la ∧ R' (chain_root_aux …) x`. (The Hf_assign body — currently ~300 lines of nested classical case analysis on whether the iteration ever stabilizes.) |
| `fiber_chain`                   | If `f x = f y = a` then `R' x y ∨ R' y x`. (The depth-induction body — currently ~215 lines.) |

These local lemmas use `Iter.v`'s parameter-free helpers where possible.

## Comments policy

- **File header**: 2–4 lines per file stating what it proves and where it fits.
- **Lemma comments**: at most one short comment (≤ 2 lines) per non-trivial lemma, capturing the mathematical role (the *why*), not a restatement of the type.
- **Existing in-proof narrative**: trim aggressively. Long explanatory comments that describe what the next 5 lines do (e.g., the bilingual narrative around lines 1099–1226 of the current file) get removed; the few that capture genuine proof strategy stay.
- The current banner comments (`(* === Section X === *)`) disappear naturally — each former banner becomes a file.

Net effect: comment count goes down, average usefulness goes up.

## Verification

Build command (per saved memory): `mise run build-posets`. After every step listed below, the build must pass; if it doesn't, the step is rolled back or the bug is fixed before moving on.

## Migration order (commit-by-commit)

Each numbered item is a commit; the build is green at each commit.

1. **`flip_IsPoset` instance**, only if missing from `PosetClasses.v`. Build check.
2. **Create `upper_bound/` skeleton** (empty files + `dune` change `(include_subdirs qualified)`). Build check (no-op).
3. **Move `Slices.v`** — extract small Above/Below structural lemmas. Build.
4. **Move `HallDefect.v`** — `StrictSucc/Pred`, `dilworth_hall_defect{,_pred}`, `min_elements_eq_la`. Build.
5. **Move `BaseCases.v`** — width-0/1 cases, `singleton_chain_cover`, `below_fiber_cover_cardinal`. Build.
6. **Move `Iter.v`** — `chain_root_aux`, `depth_aux`, parameter-free properties. Build.
7. **Introduce `HallKernel.v`** with the parameterized kernel proof. Re-prove `above_chain_assignment_exists` as a one-line application of the kernel. **`below_chain_assignment_exists` stays as its original proof for now**, just moved to `Cover.v`. Build.
8. **Switch `below_chain_assignment_exists`** to use the kernel via `flip R` + duality rewrites. This is the riskiest single step — doing it in isolation makes it easy to revert. Build.
9. **Move Merge.v and Backward.v**. Build.
10. **Convert `WidthUpperBound.v` to facade**. Build.
11. **Final pass**: trim/rewrite comments per the comments policy. Build.

## Risk and rollback

- The build runs after each step. If step 8 (the `flip R` switch) breaks, revert the commit and below stays as the original proof — the rest of the refactor stands.
- If `(include_subdirs qualified)` causes an import-resolution issue in the dune theory, fall back to a flat layout under `posets/dilworth/UpperBound_*.v` files, keeping the same module split. The kernel design is unaffected.
- If `Instance flip_IsPoset` exposes ambiguity with existing typeclass resolution, scope it to a sub-section using `#[local]` and use `Existing Instance` only where needed.

## Public surface (unchanged)

After the refactor, an external client writing `From Dilworth Require Import WidthUpperBound.` gets the same names available, with the same types, as today. No change to `DilworthTheorem.v`, `Examples.v`, or `Package.v`.

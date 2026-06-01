# Generic Finite-Poset Dimension Levers — Design (Sub-project B, part 2 follow-up; n-way slice 1 of 2)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** B part 2 (`Ordinal` — `barrier_dimension`, `posdim_unique`; `DimIso` — `dimension_iso`), B part 3 slice 2 (`ExtremumReduction` — the realizer-surgery proofs to port), F (`BarrierDim2` — `barrier_dim_le2`/`block_dim0_global_*` to port), and the `Dimension` theory (`dushnik_miller_exists`, `linear_sum_dimension`, `subtype_is_poset`, `cardinal_Im_injective`).
**Paper:** NomaDB TechReport.

## Why this slice exists

The goal is the n-way `fully_sync_dim_le2`: a fully-synchronized execution whose
blocks are each `dim ≤ 2` is itself `dim ≤ 2`. The natural proof iterates
`barrier_dim_le2` over the block list, splitting off the last block and recursing
on the lower part. **But the lower part is `sub_order E (union_upto …)` — a bare
poset on a subtype, NOT an `ExecPoset`** (it has no `RankedProgram`). Every existing
lever (`barrier_dimension`, `remove_min/max_preserves_dim2`, `barrier_dim_le2`,
`IsFullySync`) is stated on `ExecPoset`, so the recursion does not typecheck.

The fix: restate the lever chain on **bare finite posets** `(A, R)` with
`IsPoset A R` + `Finite (Full_set A)`. The existing `ExecPoset` proofs already
delegate to fully-generic library lemmas (`dimension_iso`, `linear_sum_dimension`,
`dushnik_miller_exists`, `cardinal_Im_injective`), so this is a **mechanical port
with the carrier abstracted**, not new mathematics.

**This spec is slice 1: the generic lever chain.** Slice 2 (out of scope here) is
the n-way `fin_fully_sync_dim_le2` + its `ExecPoset`/`IsFullySync` instantiation,
now unblocked because the recursion lives on `(A, R)`.

**Decision: ADD the generic layer; do NOT rewrite the existing `ExecPoset`
lemmas.** Their proofs and tests stay untouched (no churn/risk). The generic
lemmas are new; the n-way slice consumes them.

## Component 1 — generic predicates (`execution/FinPosetDim.v`)

No `ExecPoset` dependency (imports only `Posets`, `Dimension`, `DimIso`). In a
`Section` with `Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
(Hfin : Finite A (Full_set A))`:

```coq
Definition fin_sub_order (S : Ensemble A)
  : {z | Ensembles.In _ S z} -> {z | Ensembles.In _ S z} -> Prop :=
  fun x y => R (proj1_sig x) (proj1_sig y).
(* fin_sub_order S is a poset via subtype_is_poset R S *)

Definition fin_global_min (m : A) : Prop := forall x, R m x.
Definition fin_global_max (m : A) : Prop := forall x, R x m.

Definition fin_is_barrier (L U : Ensemble A) : Prop :=
  (forall x, Ensembles.In _ L x \/ Ensembles.In _ U x) /\
  (forall x, ~ (Ensembles.In _ L x /\ Ensembles.In _ U x)) /\
  (exists x, Ensembles.In _ L x) /\ (exists y, Ensembles.In _ U y) /\
  (forall x y, Ensembles.In _ L x -> Ensembles.In _ U y -> R x y).
```

## Component 2 — generic lemmas (`FinPosetDim.v`)

Statements mirror the `ExecPoset` versions, packaging dim≤2 as
`inhabited (PosetDimension … d) /\ d <= 2` and replacing the `exec_*` finiteness
wrappers with the explicit `Hfin`:

```coq
(* every finite poset has a dimension *)
Lemma fin_dim_exists : exists d, inhabited (PosetDimension R d).

(* a dimension-0 block is a single global extremum *)
Lemma fin_block_dim0_global_min :
  forall L U, fin_is_barrier L U -> PosetDimension (fin_sub_order L) 0 ->
    exists m, fin_global_min m /\ (forall x, Ensembles.In _ U x <-> x <> m).
Lemma fin_block_dim0_global_max :
  forall L U, fin_is_barrier L U -> PosetDimension (fin_sub_order U) 0 ->
    exists m, fin_global_max m /\ (forall x, Ensembles.In _ L x <-> x <> m).

(* removing a global extremum preserves dim <= 2 (realizer surgery, ported) *)
Lemma fin_remove_min_dim2 :
  forall m, fin_global_min m ->
    ((exists d, inhabited (PosetDimension (fin_sub_order (fun x => x <> m)) d) /\ d <= 2)
     <-> (exists d, inhabited (PosetDimension R d) /\ d <= 2)).
Lemma fin_remove_max_dim2 :
  forall m, fin_global_max m ->
    ((exists d, inhabited (PosetDimension (fin_sub_order (fun x => x <> m)) d) /\ d <= 2)
     <-> (exists d, inhabited (PosetDimension R d) /\ d <= 2)).

(* exact dim = max for both-positive blocks (port of barrier_dimension) *)
Lemma fin_barrier_dimension :
  forall L U, fin_is_barrier L U -> forall dL dU d,
    PosetDimension (fin_sub_order L) dL -> PosetDimension (fin_sub_order U) dU ->
    PosetDimension R d -> 0 < dL -> 0 < dU -> d = Nat.max dL dU.

(* the all-cases binary lever (port of barrier_dim_le2) *)
Lemma fin_barrier_dim_le2 :
  forall L U, fin_is_barrier L U ->
    (exists d, inhabited (PosetDimension (fin_sub_order L) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension (fin_sub_order U) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension R d) /\ d <= 2).
```

Proof approach: port the existing proofs (`ExtremumReduction.v`'s `lift_min`/
`lift_max` realizer surgery + `small_E_dim0` handling; `Ordinal.v`'s
`barrier_dimension_section` via `dimension_iso`+`linear_sum_dimension`;
`BarrierDim2.v`'s 3-case `barrier_dim_le2` and `block_dim0_global_*`), abstracting
`ep_carrier E ↦ A`, `ep_order E ↦ R`, `sub_order E ↦ fin_sub_order`,
`exec_has_dimension E d ↦ inhabited (PosetDimension R d)`,
`exec_dimension_exists E ↦ fin_dim_exists`, and the `ExecPoset` finiteness
(`ep_size_ok`/`cardinal_finite`) ↦ `Hfin` (use `finite_cardinal Hfin` to get the
`cardinal` for `dushnik_miller_exists`). `fin_dim_exists` = `dushnik_miller_exists`
applied to `Hfin`'s cardinal.

`fin_barrier_dim_le2` 3-case structure (identical to `barrier_dim_le2`):
`dL = 0` ⟹ `fin_block_dim0_global_min` + `fin_remove_min_dim2`; `dU = 0` ⟹
`fin_block_dim0_global_max` + `fin_remove_max_dim2`; both `> 0` ⟹
`fin_barrier_dimension` + `fin_dim_exists` + `lia`.

If `FinPosetDim.v` approaches 500 lines (the surgery is the heavy part), split the
`fin_remove_min/max_dim2` + helpers into `execution/FinPosetDimSurgery.v` (imported
by `FinPosetDim.v`); wire it like the others.

## Component 3 — consistency check (`execution/FinPosetDimExamples.v`, test-only)

```coq
Example fin_chain_reproduces_E_min :
  exists d, inhabited (PosetDimension (ep_order E_min) d) /\ d <= 2.
```
Instantiate `fin_barrier_dim_le2` at `(A := ep_carrier E_min, R := ep_order E_min)`
with finiteness from `ep_size_ok E_min` (`cardinal_finite`), the barrier
`E_min_barrier` reinterpreted as a `fin_is_barrier` (the `IsBarrier` and
`fin_is_barrier` conjunctions are identical up to `ep_order`/`R`, so its components
transfer directly — provide them), and the two block dim≤2 facts (reuse the
`E_min_block_dim2`-style results / `subposet_dimension_le` from `E_min_dim_2`).
Confirms the generic chain applies to a real `ExecPoset` and agrees with
`E_min_dim_le_2_via_barrier`.

(Note: `fin_sub_order (R := ep_order E_min) S` is definitionally
`sub_order E_min S`, so the block hypotheses line up; if the elaborator needs help,
`unfold fin_sub_order, sub_order`.)

## Files, wiring, testing

- New: `execution/FinPosetDim.v` (+ optional `execution/FinPosetDimSurgery.v` if split), `execution/FinPosetDimExamples.v`.
- `execution/dune` + `_CoqProject`: add the new modules.
- `execution/Execution.v`: export `FinPosetDim` (and `FinPosetDimSurgery` if created); NOT the examples.
- `docs/INDEX.md`: add a "Generic finite-poset dimension levers" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `fin_barrier_dim_le2` and `fin_chain_reproduces_E_min` — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `FinPosetDim.v` (+ surgery file if split): `fin_sub_order`, `fin_global_min`/`fin_global_max`, `fin_is_barrier`, `fin_dim_exists`, `fin_block_dim0_global_min`/`fin_block_dim0_global_max`, `fin_remove_min_dim2`/`fin_remove_max_dim2`, `fin_barrier_dimension`, `fin_barrier_dim_le2`. Zero admits.
2. `FinPosetDimExamples.v`: `fin_chain_reproduces_E_min`. Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.
4. The existing `ExecPoset` lemmas (`barrier_dim_le2`, `remove_min/max_preserves_dim2`, etc.) and their tests are UNCHANGED.

## Out of scope (slice 2 and beyond)

The n-way `fin_fully_sync_dim_le2` (induction on the block list over `(A,R)`,
recursing into `fin_sub_order` of the lower union) and its `ExecPoset`/`IsFullySync`
instantiation `fully_sync_dim_le2`; the paper transformations A/B; sync-shape
operational definitions and the reduce-to-sync-shape pipeline.

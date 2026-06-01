# Execution Barrier dim≤2 Lever — Design (Sub-project B, part 2 follow-up)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** B part 2 (`Ordinal` — `sub_order`, `barrier_dimension`, `posdim_unique`; `Frontier` — `IsBarrier`, `barrier_*`), B part 3 slice 2 (`ExtremumReduction` — `IsGlobalMin`/`IsGlobalMax`, `remove_min_preserves_dim2`/`remove_max_preserves_dim2`), B part 1 (`DimBridge` — `exec_has_dimension`, `exec_dimension_exists`), and the `Dimension` theory.
**Paper:** NomaDB TechReport.

## Motivation

`barrier_dimension` (B part 2) gives `dim E = max(dim L, dim U)` for a barrier
split — but only when **both blocks have dimension > 0**, because singleton/empty
posets have dimension 0 here (the empty realizer is valid) and the
`linear_sum_dimension` formula degenerates. That `dim > 0` hypothesis is awkward:
real blocks (e.g. a process doing one local op between syncs) can be singletons.

This slice removes that hypothesis for the `dim ≤ 2` use case, giving a clean,
all-cases **binary dim≤2 lever**: a barrier with both blocks `dim ≤ 2` makes the
whole `dim ≤ 2`. It composes three already-proven results — `barrier_dimension`
(both blocks `dim > 0`) and `remove_min/max_preserves_dim2` (singleton blocks are
global extrema) — by a case split on block dimensions. This is a *genuine* dim≤2
lever (unlike the `no_alt_cycle`-based lemmas, which are stronger than `dim ≤ 2`
and effectively vacuous for real posets — see the correction recorded for B part 2).

The n-way iteration (`fully_sync_dim_le2`) is **out of scope** (deferred — it needs
sub-poset recursion).

## Library facts this builds on (verified present)

- `Frontier`: `IsBarrier E L U` (5-conj: cover, disjoint, `L`/`U` inhabited, `Hbelow : forall x y, In L x -> In U y -> ep_order E x y`).
- `Ordinal`: `sub_order E S`; `Instance sub_order_poset`; `barrier_dimension : IsBarrier E L U -> forall dL dU d, PosetDimension (sub_order E L) dL -> PosetDimension (sub_order E U) dU -> PosetDimension (ep_order E) d -> 0 < dL -> 0 < dU -> d = Nat.max dL dU`; `posdim_unique`.
- `ExtremumReduction`: `IsGlobalMin E m := forall x, ep_order E m x`; `IsGlobalMax`; `remove_min_preserves_dim2 : IsGlobalMin E m -> ((exists d, inhabited (PosetDimension (sub_order E (fun x => x <> m)) d) /\ d <= 2) <-> (exists d, exec_has_dimension E d /\ d <= 2))`; `remove_max_preserves_dim2` (dual).
- `DimBridge`: `exec_has_dimension E d := inhabited (PosetDimension (ep_carrier E)(ep_order E) d)`; `exec_dimension_exists`; `exec_dim_ge_2` (its `d=0` case shows the empty-realizer ⇒ universal-relation pattern).
- `DimDefs`: `PosetDimension` fields; `IsRealizer`/`realizer_intersection`; `cardinalO_empty` (empty realizer from cardinal 0).

## Component 1 — the dim-0 → global-extremum bridge (`execution/BarrierDim2.v`)

```coq
Lemma block_dim0_global_min :
  forall E L U, IsBarrier E L U ->
    PosetDimension (sub_order E L) 0 ->
    exists m, IsGlobalMin E m /\ (forall x, Ensembles.In _ U x <-> x <> m).

Lemma block_dim0_global_max :
  forall E L U, IsBarrier E L U ->
    PosetDimension (sub_order E U) 0 ->
    exists m, IsGlobalMax E m /\ (forall x, Ensembles.In _ L x <-> x <> m).
```
Proof of `block_dim0_global_min`:
1. `PosetDimension (sub_order E L) 0` ⟹ `dimension_realizer = Empty_set` (`cardinalO_empty` on `dimension_cardinality`) ⟹ by `realizer_intersection`, `sub_order E L a b` holds for **all** `a b` (vacuous `forall L' in ∅`).
2. Hence any two elements of `{z | In L z}` are equal (`poset_antisym` on `sub_order E L`, which is now universal), i.e. all `L` elements (as `ep_carrier E`) are equal.
3. `L` inhabited (barrier) ⟹ pick witness `m ∈ L`; every `x ∈ L` equals `m`. So `forall x, In L x <-> x = m`.
4. `IsGlobalMin E m`: `intro x`; by barrier cover `x ∈ L ∨ x ∈ U`; `x ∈ L ⟹ x = m ⟹ ep_order E m m` (refl); `x ∈ U ⟹ Hbelow m x` (`m ∈ L`).
5. `U = {x | x <> m}`: `In U x <-> ~ In L x` (cover + disjoint) `<-> x <> m` (step 3).

`block_dim0_global_max` is symmetric (using `Hbelow` the other way for the global max).

## Component 2 — the all-cases binary lever (`BarrierDim2.v`)

```coq
Lemma barrier_dim_le2 :
  forall E L U, IsBarrier E L U ->
    (exists d, inhabited (PosetDimension (sub_order E L) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension (sub_order E U) d) /\ d <= 2) ->
    (exists d, exec_has_dimension E d /\ d <= 2).
```
Proof: extract `dL` (`PosetDimension (sub_order E L) dL`, `dL <= 2`) and `dU` likewise. Case on `dL`, then `dU`:
- **`dL = 0`:** `block_dim0_global_min` gives `m` (global min) with `U = {x | x <> m}`. Rewrite `U` to `(fun x => x <> m)` (the ensembles are equal — `functional_extensionality` + `propositional_extensionality` from the `<->`), turning the `U`-hypothesis into `(exists d, inhabited (PosetDimension (sub_order E (fun x => x <> m)) d) /\ d <= 2)`. Apply `remove_min_preserves_dim2 E m` (the `->` direction: block ⟹ E) to conclude `exists d, exec_has_dimension E d /\ d <= 2`. (Subsumes `dU = 0`, since `dU <= 2`.)
- **`dL = S _` (so `0 < dL`), `dU = 0`:** symmetric via `block_dim0_global_max` + `remove_max_preserves_dim2`.
- **`0 < dL`, `0 < dU`:** `destruct (exec_dimension_exists E) as [d [Hd]]`; `barrier_dimension … dL dU d (the PosetDimensions) Hd (0<dL) (0<dU)` gives `d = Nat.max dL dU`; with `dL <= 2`, `dU <= 2`, `d <= 2`; `exists d; split; [exact (inhabits Hd) | lia]`.

## Component 3 — concrete instance (`execution/BarrierDim2Examples.v`, test-only)

```coq
Example E_min_dim_le_2_via_barrier :
  exists d, exec_has_dimension E_min d /\ d <= 2.
```
Apply `barrier_dim_le2` to `E_min_barrier` (the `{a} | {b,c,d}` split from
`FrontierExamples.v`; `Lmin` is the singleton, so this exercises the `dL = 0` /
`remove_min` path). The two block `dim ≤ 2` facts come from the existing `E_min` /
block results (`subposet_reduces_dim` + `reduces_dim2` from `E_min_dim_2`, or the
slice-2 `E_min_block_dim_le_2_via_extremum`). Demonstrates the all-cases lever
composing on the singleton path. (E_min's only barrier is this singleton one, so
the `0 < dL, 0 < dU` `barrier_dimension` path is covered by the lemma but not
exercised by a concrete example here.)

## Files, wiring, testing

- New: `execution/BarrierDim2.v`, `execution/BarrierDim2Examples.v`.
- `execution/dune` + `_CoqProject`: add the two modules.
- `execution/Execution.v`: export `BarrierDim2` (not the examples).
- `docs/INDEX.md`: add a "Barrier dim≤2 lever" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `barrier_dim_le2` and `E_min_dim_le_2_via_barrier` — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `BarrierDim2.v`: `block_dim0_global_min`, `block_dim0_global_max`, `barrier_dim_le2`. Zero admits.
2. `BarrierDim2Examples.v`: `E_min_dim_le_2_via_barrier`. Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later)

The n-way `fully_sync_dim_le2` (iterate `barrier_dim_le2` over a block list — needs
sub-poset recursion); the paper transformations A/B; sync-shape operational
definitions and the reduce-to-sync-shape pipeline; re-documenting the
`no_alt_cycle` lemmas as the stronger "single-extension-reversible" condition
(a separate cleanup).

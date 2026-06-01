# Exact n-way Fully-Synchronized Dimension — Design (exact n-way dim=max, slice 2 of 2)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** slice 1 (`FinExtremumDim` — `fin_barrier_dimension_full`, `fin_singleton_dim0`), the dim≤2 n-way (`FinFullySync` — `fin_ordinal_partition`, `restrict_block`, `restricted_block_dim2`, `fin_sub_order_finite`, `fin_block_iso_full`, and the `fin_fully_sync_dim_le2_aux` induction template; `FullySyncDim2` — `fully_sync_pairwise_below`), `DimIso`, and the `Dimension` theory (`dim_ge_1_of_two`, `posdim_unique`/`fin_posdim_unique`).
**Paper:** NomaDB TechReport.

## Goal

The exact dimension of a fully-synchronized execution: for a ≥2-element carrier,
`dim(whole) = max(1, maxᵢ dim(Bᵢ))`. This is the exact-dimension sibling of the
completed dim≤2 n-way lever (`fully_sync_dim_le2`), iterating slice 1's binary
`fin_barrier_dimension_full` over the block list. Generic on `(A, R, Finite)` (so
the induction recurses into the lower sub-poset of a barrier split), then
instantiated for `IsFullySync`.

**Why `max(1, …)` and the ≥2-element hypothesis:** a singleton/empty poset has
dimension 0 here, so an ordinal sum of singletons (a chain) has whole-dimension 1
while `maxᵢ dim Bᵢ = 0` — the `max(1, …)` correction (from slice 1's
`fin_barrier_dimension_full`). The formula `dim = max(1, …)` is only correct for
≥2-element carriers (a 1-element execution has dim 0), hence the
`(exists a b, a <> b)` hypothesis.

## Representation of "max over blocks"

Thread a per-block dimension list `dims : list nat` (same length as `blocks`) with
`forall i, i < length blocks -> PosetDimension (fin_sub_order R (nth i blocks ∅)) (nth i dims 0)`,
and conclude `dW = Nat.max 1 (fold_right Nat.max 0 dims)`. No choice/definedness
machinery; the caller supplies each block's dimension; the induction peels the last
`dim` off the list alongside the last block.

## Component 1 — generic exact n-way theorem (`execution/FinFullySyncDim.v`)

In a `Section` with `Context {A} (R) {HR : IsPoset A R} (Hfin : Finite A (Full_set A))`
(matching `FinFullySync.v`):

```coq
Lemma fin_fully_sync_dimension :
  forall (blocks : list (Ensemble A)) (dims : list nat),
    fin_ordinal_partition R blocks ->
    length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (fin_sub_order R (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : A, a <> b) ->
    forall dW, PosetDimension R dW ->
      dW = Nat.max 1 (fold_right Nat.max 0 dims).
```

Proved via a carrier-quantified strong induction (mirroring
`fin_fully_sync_dim_le2_aux` in `FinFullySync.v` — the recursive call lands on the
lower sub-poset, a DIFFERENT carrier, so the aux quantifies over `(A',R',HR',Hfin')`
and inducts on a `nat` length bound):

```coq
Lemma fin_fully_sync_dimension_aux :
  forall n (A : Type) (R : A -> A -> Prop) (HR : IsPoset A R)
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)) (dims : list nat),
    length blocks <= n -> length dims = length blocks ->
    @fin_ordinal_partition A R blocks ->
    (forall i, i < length blocks ->
       PosetDimension (@fin_sub_order A R (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b, a <> b) ->
    forall dW, PosetDimension R dW -> dW = Nat.max 1 (fold_right Nat.max 0 dims).
```
`fin_fully_sync_dimension` = `fin_fully_sync_dimension_aux (length blocks) A R HR Hfin blocks dims (le_n _) …`.

Induct on `n`; peel the last block (`blocks = pre ++ [Bk]`, `dims = predims ++ [dk]`
via `exists_last`/`rev`; `length predims = length pre`). Three cases:
- **`pre = []`** (single block `[Bk]`, `dims = [dk]`): `Bk` is the full set (cover);
  `fin_block_iso_full R Bk <Bk full> dk <PosetDim block Bk dk> : inhabited (PosetDimension R dk)`,
  and `posdim_unique`/`fin_posdim_unique` with `HdW` gives `dW = dk`. `dim_ge_1_of_two dW HdW (≥2)`
  gives `dk ≥ 1`. `fold_right Nat.max 0 [dk] = Nat.max dk 0 = dk`; so `dW = dk = max 1 dk` (`lia`).
- **`pre ≠ []`**: build `fin_is_barrier R L Bk` with `L := ⋃ pre` (reuse the
  barrier construction from `fin_fully_sync_dim_le2_aux`'s `pre ≠ []` case). Let `dL`
  be `dim(fin_sub_order R L)` (from `fin_dim_exists`). `fin_barrier_dimension_full
  R Hfin L Bk Hbar dL dk dW HdL Hdk HdW : dW = Nat.max 1 (Nat.max dL dk)`.
  `destruct (classic (exists u v : {z|In L z}, u <> v))`:
  - **L has ≥2 elements:** IH (`fin_fully_sync_dimension_aux n …`) on
    `(R := fin_sub_order R L, Hfin := fin_sub_order_finite R Hfin L, blocks := map (restrict_block L) pre, dims := predims)` gives `dL = Nat.max 1 (fold_right Nat.max 0 predims)`.
    (Partition + restricted block dims via the inline restriction assembly +
    `restricted_block_dim_exact` — see Component 2.) Substitute into
    `dW = max 1 (max dL dk)`: `= max 1 (max (max 1 (fold predims)) dk) = max 1 (max (fold predims) dk) = max 1 (fold (predims++[dk]))` (the `max 1` absorbs; `fold_right Nat.max 0 (predims ++ [dk]) = Nat.max (fold_right Nat.max 0 predims) dk` by `fold_right_app`/induction). `lia` after the fold-app rewrite.
  - **L is a singleton** (`~ ∃ two distinct in L`): all `{z|In L z}` equal; `dL = 0`
    via `fin_singleton_dim0`. Establish `pre` is a single singleton block ⟹
    `fold_right Nat.max 0 predims = 0` (sub-lemma `singleton_union_pre_dims_zero`):
    `L = ⋃ pre` a single element + `pre` blocks nonempty & disjoint ⟹ `pre` has
    exactly one block (a singleton) ⟹ `predims = [d0]` with `d0 = 0` (singleton ⟹
    dim 0). So `dW = max 1 (max 0 dk) = max 1 dk = max 1 (max 0 dk) = max 1 (fold (predims++[dk]))` (`lia`, with `fold predims = max 0 0 = 0`).

## Component 2 — restriction helper generalization (`FinFullySync.v` or `FinFullySyncDim.v`)

The dim≤2 n-way used `restricted_block_dim2` (a prefix block's dim≤2 transports to
its restriction). The exact n-way needs the bare transport for ANY `d`:

```coq
Lemma restricted_block_dim_exact :
  forall (L B : Ensemble A),
    (forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
      inhabited (PosetDimension (fin_sub_order (fin_sub_order R L) (restrict_block L B)) d).
```
This is the SAME `dimension_iso` double-subtype argument as `restricted_block_dim2`,
just without the `d <= 2` carry. If `restricted_block_dim2`'s proof already factors
through such a transport, reuse it / lightly generalize; otherwise add this lemma
(in `FinFullySync.v` to sit beside its sibling, or locally in `FinFullySyncDim.v`).
The inline restricted-partition assembly (`fin_prefix_restricted_partition`-style)
from `fin_fully_sync_dim_le2_aux` is reused for the partition argument; the
per-block exact dims come from `restricted_block_dim_exact` applied to each prefix
block's `PosetDimension … (nth i predims 0)`.

## Component 3 — ExecPoset instance (`execution/FullySyncDimExact.v`)

```coq
Lemma fully_sync_dimension :
  forall E blocks dims, IsFullySync E blocks ->
    length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    forall dW, PosetDimension (ep_order E) dW ->
      dW = Nat.max 1 (fold_right Nat.max 0 dims).
```
Proof: translate `IsFullySync E blocks` → `fin_ordinal_partition (ep_order E) blocks`
(nonempty/cover/disjoint fields + `fully_sync_pairwise_below`); `Hfin` from
`ep_size_ok E` via `cardinal_finite`; `fin_sub_order (ep_order E) blk` is
definitionally `sub_order E blk`; apply `fin_fully_sync_dimension`. (Split into its
own file to keep each <500 lines; the aux induction is large.)

## Component 4 — concrete example (`execution/FinFullySyncDimExamples.v`, test-only)

The meaningful `E_min` cross-check is BLOCKED on the deferred `dim{b,c,d} = 2`
exact realizer (task #66 — `PosetDimension` is `Type`-sorted, can't be extracted
from an `inhabited`). So the example is an **all-singleton chain** instead:

```coq
Example chain_all_singleton_dim :
  exists dW, inhabited (PosetDimension <chain R> dW) /\ dW = 1.
```
A concrete ≥2-element fully-synchronized execution (or bare finite poset) whose
blocks are all singletons — e.g. a 2- or 3-element chain partitioned into singleton
blocks, `dims = [0; 0; …]`, result `dim = max(1, fold_right max 0 [0;0;…]) =
max(1, 0) = 1`. This exercises the n-way `fold` machinery + the singleton-L
recursion path end-to-end (unlike a single binary case). Reuse the `chain2_R`
bool-poset pattern from slice 1's `FinExtremumDimExamples.v`, partitioned into
`[{false}; {true}]` with `dims = [0; 0]`.

(The `E_min` nontrivial cross-check via `fully_sync_dimension` stays deferred to
task #66.)

## Files, wiring, testing

- New: `execution/FinFullySyncDim.v` (generic theorem + aux + sub-lemmas),
  `execution/FullySyncDimExact.v` (ExecPoset instance),
  `execution/FinFullySyncDimExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the new modules.
- `execution/Execution.v`: export `FinFullySyncDim FullySyncDimExact`; NOT the examples.
- `docs/INDEX.md`: add an "Exact n-way fully-synchronized dimension" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero
  `Admitted`**. Files <500 lines (split the aux if needed), each `Qed` <5 min.
- `Print Assumptions` on `fin_fully_sync_dimension`, `fully_sync_dimension`, the
  example — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `FinFullySyncDim.v`: `restricted_block_dim_exact` (or reuse), `singleton_union_pre_dims_zero`, `fin_fully_sync_dimension_aux`, `fin_fully_sync_dimension`. Zero admits.
2. `FullySyncDimExact.v`: `fully_sync_dimension`. Zero admits.
3. `FinFullySyncDimExamples.v`: `chain_all_singleton_dim`. Zero admits.
4. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope

The `E_min` nontrivial cross-check via `fully_sync_dimension` (blocked on task #66,
`dim{b,c,d} = 2` exact realizer); the paper transformations A/B; sync-shape
operational definitions; the reduce-to-sync-shape pipeline.

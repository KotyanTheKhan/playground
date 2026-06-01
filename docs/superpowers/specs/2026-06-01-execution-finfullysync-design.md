# n-way Fully-Synchronized dim≤2 — Design (Sub-project B, part 2 follow-up; n-way slice 2 of 2)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** n-way slice 1 (`FinPosetDim` — `fin_sub_order`, `fin_is_barrier`, `fin_barrier_dim_le2`, `fin_dim_exists`; `FinPosetDimSurgery`), `DimIso` (`dimension_iso`), B part 2 (`Ordinal` — `sub_order`; `FullySync` — `IsFullySync`, `union_upto`), B part 1 (`DimBridge` — `exec_has_dimension`, `ep_size_ok`), and the `Dimension` theory.
**Paper:** NomaDB TechReport.

## Goal

The headline genuine dim≤2 lever for fully-synchronized executions:
`fully_sync_dim_le2` — if a fully-synchronized execution's blocks are each
`dim ≤ 2`, the whole execution is `dim ≤ 2`. Proven by iterating
`fin_barrier_dim_le2` over the block list. The iteration recurses into the *lower
part* of a barrier split, which is a bare sub-poset (not an `ExecPoset`); slice 1
made the lever chain carrier-generic precisely to enable this. So the theorem is
proven generically on `(A, R, Finite)` and then instantiated for `IsFullySync`.

This is the GENUINE n-way lever (the `no_alt_cycle`-based `fully_sync_dim2` is
sound but vacuous for real posets — see that lemma's recorded caution).

## Library facts this builds on (verified present)

- `FinPosetDim` (slice 1, on a section `Context {A} (R) {HR : IsPoset A R} (Hfin : Finite A (Full_set A))`): `fin_sub_order R (S : Ensemble A)`; `fin_is_barrier R (L U : Ensemble A)` (5-conjunction); `fin_barrier_dim_le2 R Hfin L U : fin_is_barrier R L U -> (block L dim2) -> (block U dim2) -> (exists d, inhabited (PosetDimension R d) /\ d<=2)`; `fin_dim_exists R Hfin`.
- `DimIso`: `dimension_iso` (poset dimension invariant under order-iso).
- `FullySync`: `IsFullySync E blocks` (nonempty + cover + disjoint + every prefix split `union_upto k | complement` is an `IsBarrier`); `union_upto E blocks k`.
- `Ordinal`: `sub_order E S`; `subtype_is_poset`.
- `DimBridge`: `exec_has_dimension E d := inhabited (PosetDimension (ep_carrier E)(ep_order E) d)`; `ep_size_ok E`.
- `Dimension`/`Finite.v` pattern: `cardinal_subtype_full`/`cardinal_finite` for "a subtype of a finite type is finite".

## Component 1 — generic ordinal partition + theorem (`execution/FinFullySync.v`)

In a `Section` with `Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
(Hfin : Finite A (Full_set A))`:

```coq
Definition fin_ordinal_partition (blocks : list (Ensemble A)) : Prop :=
  (forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x) /\
  (forall x, exists i, i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x) /\
  (forall i j x, i < length blocks -> j < length blocks -> i <> j ->
     Ensembles.In _ (nth i blocks (Empty_set _)) x ->
     ~ Ensembles.In _ (nth j blocks (Empty_set _)) x) /\
  (forall i j, i < j -> j < length blocks ->
     forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                 Ensembles.In _ (nth j blocks (Empty_set _)) y -> R x y).

Lemma fin_fully_sync_dim_le2 :
  forall (blocks : list (Ensemble A)),
    fin_ordinal_partition blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (fin_sub_order R blk) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension R d) /\ d <= 2).
```

Proof by strong induction on `length blocks` (`lt_wf_ind`) or `rev_ind`:
- **0 blocks:** cover ⟹ `A` empty (`Full_set A` empty) ⟹ `dim = 0` (`fin_dim_exists` gives some `d`; an empty poset's dimension is 0 — or simply: `exists 0`/the dimension is ≤ 2 trivially since the realizer can be empty). Provide `exists d, inhabited (PosetDimension R d) /\ d <= 2` with the existing dimension and bound it (empty carrier ⇒ `dim ≤ 2`). [If awkward, exclude 0 via a nonempty `A` hypothesis derived from `Hfin`/inhabitance — but cover over an inhabited `A` forces ≥1 block, so 0-blocks only arises for empty `A`.]
- **1 block (`[B0]`):** cover + single block ⟹ `B0 = Full_set A` (as an ensemble: every `x` is in block 0). `fin_sub_order R B0` is order-iso to `R` (the map `x ↦ exist _ x (proof In B0 x)` / `proj1_sig` is a bijection preserving order). Transport the block's `dim ≤ 2` to `R` via `dimension_iso`.
- **last block peel (`blocks = pre ++ [Bk]`, `pre` nonempty):** set `L := union_upto-style ⋃ pre`, `U := Bk`. Show `fin_is_barrier R L U` (cover/disjoint/inhabited from the partition; `L`-below-`U` from the "earlier below later" clause at `j = length pre`). `fin_barrier_dim_le2 R Hfin L U Hbar` reduces to two block goals: `U` from `Bk`'s hypothesis dim≤2; `L` from the IH applied to the restricted partition (Component 2).

## Component 2 — restriction machinery (`FinFullySync.v`)

```coq
(* a block, viewed as a subset of the L-subtype *)
Definition restrict_block (L B : Ensemble A) : Ensemble {z | Ensembles.In _ L z} :=
  fun z => Ensembles.In _ B (proj1_sig z).
```
Helper lemmas:
- `fin_sub_order_finite : forall L, Finite {z | Ensembles.In _ L z} (Full_set _)` — a subtype of the finite `A` is finite (reuse the `cardinal_subtype_full`/`cardinal_finite` pattern from `execution/Finite.v`; `L`'s subtype embeds into `A`'s, which is `Hfin`).
- `restrict_partition : fin_ordinal_partition` of `(fin_sub_order R L)` for `map (restrict_block L) pre`, given `pre`'s blocks are all `⊆ L` and form the partition's prefix. (Cover/disjoint/below transfer through `proj1_sig`; nonempty since each `Bi ⊆ L`.)
- `restricted_block_dim2 : forall i < length pre, exists d, inhabited (PosetDimension (fin_sub_order (fin_sub_order R L) (restrict_block L Bi)) d) /\ d <= 2` — via `dimension_iso`: the double-subtype `{w | In (restrict_block L Bi) w}` is order-iso to `{z | In Bi z}` (both carry `R` on the underlying `A` elements; `Bi ⊆ L` makes the embedding a bijection). Transports `Bi`'s hypothesis dim≤2.

The IH (on `length pre < length blocks`) applied with `R := fin_sub_order R L`,
`Hfin := fin_sub_order_finite L`, the restricted partition, and
`restricted_block_dim2` yields `dim (fin_sub_order R L) ≤ 2` — exactly the `L`
block goal of `fin_barrier_dim_le2`.

## Component 3 — ExecPoset instantiation (`FinFullySync.v` or `FullySyncDim2.v`)

```coq
(* IsFullySync's prefix-barriers imply the pairwise earlier-below-later clause *)
Lemma fully_sync_pairwise_below :
  forall E blocks, IsFullySync E blocks ->
    forall i j, i < j -> j < length blocks ->
      forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                  Ensembles.In _ (nth j blocks (Empty_set _)) y -> ep_order E x y.

Lemma fully_sync_dim_le2 :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) ->
    (exists d, exec_has_dimension E d /\ d <= 2).
```
- `fully_sync_pairwise_below`: for `i < j`, use `IsFullySync`'s prefix-barrier at `k = j`: block `i ⊆ union_upto j` (the `L`/lower side), block `j ⊆ complement` (the `U`/upper side); the barrier's `Hbelow` gives `ep_order E x y`.
- `fully_sync_dim_le2`: assemble `fin_ordinal_partition (ep_order E) blocks` from `IsFullySync`'s nonempty/cover/disjoint fields + `fully_sync_pairwise_below`; `Hfin` from `ep_size_ok E` via `cardinal_finite`; the block hyps match (`fin_sub_order (ep_order E) blk` is definitionally `sub_order E blk`); apply `fin_fully_sync_dim_le2`. `exec_has_dimension E d` is `inhabited (PosetDimension (ep_order E) d)`.

If `FinFullySync.v` approaches 500 lines, put Component 3 in `execution/FullySyncDim2.v` (imports `FinFullySync`, `FullySync`, `Poset`, `Ordinal`, `DimBridge`).

## Component 4 — concrete instance (`execution/FinFullySyncExamples.v`, test-only)

```coq
Example E_min_is_fully_sync_2 : IsFullySync E_min [Lmin; Umin].
Example E_min_dim_le_2_via_fully_sync :
  exists d, exec_has_dimension E_min d /\ d <= 2.
```
- `E_min_is_fully_sync_2`: the 2-block decomposition `[Lmin; Umin]` (= `[{a}; {b,c,d}]` from `FrontierExamples.v`). Discharge `IsFullySync`'s four fields: nonempty (both inhabited), cover (`valid_event_min_cases` ⟹ every event in `Lmin` or `Umin`), disjoint (`a` vs not-`a`), and the single prefix barrier at `k=1` (`union_upto [Lmin;Umin] 1 = Lmin`, complement `= Umin`) = `E_min_barrier` (reuse it). This is a small new obligation.
- `E_min_dim_le_2_via_fully_sync`: `apply (fully_sync_dim_le2 E_min [Lmin; Umin] E_min_is_fully_sync_2)`; the two block dim≤2 goals from the existing `E_min` block results (`subposet_dimension_le` from `E_min_dim_2`). Recovers `E_min` dim≤2 through the n-way path — exercising the iteration on a genuine 2-block case.

## Files, wiring, testing

- New: `execution/FinFullySync.v` (Components 1–2, + Component 3 unless split into `execution/FullySyncDim2.v`), `execution/FinFullySyncExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the new modules.
- `execution/Execution.v`: export `FinFullySync` (and `FullySyncDim2` if split); NOT the examples.
- `docs/INDEX.md`: add an "n-way fully-synchronized dim≤2" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `fin_fully_sync_dim_le2`, `fully_sync_dim_le2`, `E_min_dim_le_2_via_fully_sync` — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `FinFullySync.v`: `fin_ordinal_partition`, `restrict_block`, `fin_sub_order_finite`, `restrict_partition`, `restricted_block_dim2`, `fin_fully_sync_dim_le2`. Zero admits.
2. Component 3: `fully_sync_pairwise_below`, `fully_sync_dim_le2`. Zero admits.
3. `FinFullySyncExamples.v`: `E_min_is_fully_sync_2`, `E_min_dim_le_2_via_fully_sync`. Zero admits.
4. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later)

The paper transformations A/B; sync-shape operational definitions and the
reduce-to-sync-shape pipeline; computing dimensions of larger concrete mΨ
executions; the `dim = max` exact n-way (`fin_fully_sync_dimension`, a separate
deferred item — this slice is the `dim ≤ 2` lever, not exact dimension).

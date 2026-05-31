# Execution Reduction Framework — Design (Sub-project B, part 3, slice 1)

**Date:** 2026-05-31
**Branch:** `execution_poset`
**Depends on:** A (`execution/` core), B part 1 (`DimBridge` — `exec_dimension_exists`), B part 2 (`DimIso` — `dimension_iso`; `Ordinal` — `sub_order`, `posdim_unique`; `FrontierExamples` — `Umin`), and the `Dimension` theory (`DimDefs`, `Theorems`).
**Paper:** NomaDB TechReport.

## Where this sits

Sub-project B is "reductions to sync-shape + dimension-preservation". B part 3 is
the reductions themselves (the paper's transformations). They are the hardest,
most paper-specific work, so part 3 is sliced. **This spec is part 3 slice 1: the
abstract reduction framework + a concrete instance** — the composable toolkit the
specific transformations (A/B) will plug into once each is shown to be an
order-iso / embedding / critical-pair-preserving map. The specific transformations,
the sync-shape operational definitions, and the reduce-to-sync-shape pipeline are
**out of scope** (later slices).

## Design rationale (an edge case avoided)

In this formalization a singleton (or empty) poset has dimension **0** — the empty
realizer is valid (`R x y <-> (forall L in ∅) = True`, consistent with ≤ 1
element). This makes the exact `dim = max` (`barrier_dimension`, which requires
`0 < dL, dU`) awkward for singleton blocks, and the `dim≤2 ⟸` direction would
otherwise need the deferred converse (`dim≤2 ⇒ no alt cycle`). The framework
therefore centers on **exact dimension preservation via order-iso** and **one-way
reduction via subposet** — both fully supported by `dimension_iso` and
`subposet_dimension_le`, with no edge cases.

## Library facts this builds on (verified present)

- `DimDefs`: `PosetDimension R d` (class, with `dimension_is_minimum`).
- `Theorems`: `subposet_dimension_le : forall (R) {IsPoset A R} (S : Ensemble A) (d_p), PosetDimension R d_p -> exists d_q, inhabited (PosetDimension (fun x y => R (proj1_sig x)(proj1_sig y)) d_q) /\ d_q <= d_p`; `subtype_is_poset`.
- B part 1/2: `dimension_iso : (order-iso f,g) -> PosetDimension R d -> PosetDimension S d`; `posdim_unique : PosetDimension R d -> PosetDimension R d' -> d = d'`; `exec_dimension_exists`; `sub_order`, `E_min`, `E_min_dim_2`, `Umin`.

## Component 1 — the two reduction relations (`execution/Reduction.v`)

Stated on general posets. Public names fixed.

```coq
Definition PreservesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall d, PosetDimension R d <-> PosetDimension S d.

Definition ReducesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall dR dS, PosetDimension R dR -> PosetDimension S dS -> dR <= dS.
```

**Composability:**
- `preserves_dim_refl : PreservesDim R R`; `preserves_dim_sym : PreservesDim R S -> PreservesDim S R`; `preserves_dim_trans : PreservesDim R S -> PreservesDim S T -> PreservesDim R T`.
- `reduces_dim_refl : ReducesDim R R` (via `posdim_unique`: `dR = dS` so `dR <= dS`); `reduces_dim_trans : ReducesDim R S -> ReducesDim S T -> ReducesDim R T` (needs `S` to have a dimension to bridge — add hypothesis `(exists dS, PosetDimension S dS)`, automatic for finite/execution posets).
- `preserves_dim_reduces : PreservesDim R S -> (exists dS, PosetDimension S dS) -> ReducesDim R S` (and the symmetric `ReducesDim S R`).

## Component 2 — instances + dim≤2 corollaries (`Reduction.v`)

```coq
Lemma iso_preserves_dim :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S} (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
    (forall a a', R a a' <-> S (f a) (f a')) ->
    PreservesDim R S.

Lemma subposet_reduces_dim :
  forall (B : Type) (S : B -> B -> Prop) `{IsPoset B S} (Sub : Ensemble B),
    ReducesDim (fun x y : {z | Ensembles.In _ Sub z} =>
                  S (proj1_sig x) (proj1_sig y)) S.

Lemma embedding_reduces_dim :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S} (f : A -> B),
    (forall a a', a <> a' -> f a <> f a') ->                 (* injective *)
    (forall a a', R a a' <-> S (f a) (f a')) ->              (* order-embedding *)
    ReducesDim R S.

Lemma preserves_dim2 :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop),
    PreservesDim R S ->
    ((exists d, PosetDimension R d /\ d <= 2) <-> (exists d, PosetDimension S d /\ d <= 2)).

Lemma reduces_dim2 :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop),
    ReducesDim R S ->
    (exists dR, PosetDimension R dR) ->
    (exists d, PosetDimension S d /\ d <= 2) ->
    (exists d, PosetDimension R d /\ d <= 2).
```

Proof notes:
- `iso_preserves_dim`: `dimension_iso` forward (`f`,`g`) and backward (`g`,`f`, using the symmetric hypotheses and `R a a' <-> S (f a)(f a')` rearranged to `S b b' <-> R (g b)(g b')`).
- `subposet_reduces_dim`: from `subposet_dimension_le S Sub dS Hd` get `d_q <= dS` with `inhabited (PosetDimension (subposet) d_q)`; `posdim_unique` identifies `d_q = dR` (the given subposet dimension); so `dR <= dS`.
- `embedding_reduces_dim`: the image `Im A f` is a subposet of `S` order-iso to `R` (build the iso `A ≅ {b | In (Im A f) b}` from the injective embedding); compose `iso_preserves_dim` (`PreservesDim R (image subposet)`) with `subposet_reduces_dim` (`ReducesDim (image subposet) S`) and `preserves_dim_reduces`/`reduces_dim_trans`.
- `preserves_dim2`: transport the dimension witness `d` through `PreservesDim` (both directions); `d <= 2` is carried.
- `reduces_dim2`: from `exists dR` and `exists d (=dS) <= 2`, `ReducesDim` gives `dR <= dS <= 2`.

## Component 3 — concrete instance (`execution/ReductionExamples.v`, test-only)

`E_min` (from `DimExamples.v`), `Umin := fun x => proj1_sig x <> (0,0)` (from `FrontierExamples.v`); `sub_order E_min Umin` is definitionally the block subposet `{x | In Umin x}` under `ep_order E_min`.

```coq
Example E_min_block_reduces :
  ReducesDim (sub_order E_min Umin) (ep_order E_min).

Example E_min_block_dim_le_2 :
  exists d, PosetDimension (sub_order E_min Umin) d /\ d <= 2.

Example reduction_chain_demo :
  ReducesDim (sub_order E_min Umin) (ep_order E_min).
```

Strategies:
- `E_min_block_reduces`: `apply subposet_reduces_dim` (the carrier/relation of `sub_order E_min Umin` matches the general subposet form definitionally).
- `E_min_block_dim_le_2`: `apply reduces_dim2` with `E_min_block_reduces`; `exists dR` from `dushnik_miller_exists` on the finite block (its cardinality from the finite `ep_carrier E_min`); the `S`-side `exists d ≤ 2` is `E_min_dim_2` (`exec_has_dimension E_min 2` = `inhabited (PosetDimension (ep_order E_min) 2)`, unwrap with `2 <= 2`).
- `reduction_chain_demo`: compose `iso_preserves_dim` with the identity iso on `E_min` (`f := id`, `g := id`) giving `PreservesDim (ep_order E_min) (ep_order E_min)`, then `preserves_dim_reduces`/`reduces_dim_trans` with `E_min_block_reduces` — exercising the composability algebra end-to-end on a real execution.

## Files, wiring, testing

- New: `execution/Reduction.v`, `execution/ReductionExamples.v`.
- `execution/dune` + `_CoqProject`: add the two modules.
- `execution/Execution.v`: export `Reduction` (not `ReductionExamples`).
- `docs/INDEX.md`: add a "Reduction framework" subsection.
- Every file builds via `.claude/scripts/timed-build.sh`; whole-`execution` and `@all` green; **zero `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `preserves_dim2`, `reduces_dim2`, `E_min_block_dim_le_2` — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `Reduction.v`: `PreservesDim`, `ReducesDim`, the composability lemmas, `iso_preserves_dim`, `subposet_reduces_dim`, `embedding_reduces_dim`, `preserves_dim2`, `reduces_dim2`. Zero admits.
2. `ReductionExamples.v`: `E_min_block_reduces`, `E_min_block_dim_le_2`, `reduction_chain_demo`. Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later B slices)

Paper Transformations A (synchronization-square contraction) and B; sync-shape /
synchronous-message operational definitions; the reduce-to-sync-shape pipeline and
its termination. Each later transformation discharges its dimension preservation by
exhibiting an `iso_preserves_dim` / `embedding_reduces_dim` / critical-pair-preserving
witness and applying this framework.

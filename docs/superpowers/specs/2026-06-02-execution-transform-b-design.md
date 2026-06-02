# Transformation B (inter-synchronization / critical-pair simplification) — Design

**Date:** 2026-06-02
**Branch:** `execution_poset`
**Depends on:** the dimension/Dilworth libraries — `dimension_le_width` (`WidthBound.v`), `width_exists` (`WidthExists.v`), `pigeonhole_chains_antichains` (`WidthLowerBound.v`), `IsChain`/`IsChainCover`/`IsAntichain`/`Width`/`IsLargestAntichain` (`dilworth/Definitions.v`); execution `FullySyncDim2` (`fully_sync_dim_le2`), `Ordinal` (`sub_order`), `DimTwoGeneric` (`dim2_record`), `ChainDim` (`chain_dim_1`).
**Paper:** NomaDB TechReport — Transformation B.

## Goal & framing

The paper's **Transformation B** observes that *"two processes between synchronizations form
at most 2 critical pairs"* and simplifies each inter-synchronization interval to "one local
modification," **preserving the critical-pair / dimension property**. The faithful mathematical
core: a block spanned by **2 processes** is covered by **2 chains** (each process's events are a
chain under program order), so it has **width ≤ 2**, hence **dimension ≤ 2** (`dimension_le_width`).
This is exactly "≤ 2 critical pairs ⟹ dim ≤ 2," and — being a property of the per-block
dimension only — is preserved under any block replacement that keeps the block 2-process
(mirroring how Transformation A used `transform_preserves_dimension`).

**Honest caveats (recorded, as for Transformation A):**
- The paper's inter-sync geometry is informally specified; the concrete blocks below are OUR
  faithful realization.
- "Critical pairs" are the informal motivation; we formalize the equivalent dimension bound
  (width ≤ 2 ⟹ dim ≤ 2), which is what makes the transformation dimension-preserving.

## Component 1 — the faithful general lemma (`execution/TransformB.v`)

```coq
(* a finite poset whose carrier is covered by two chains has dimension <= 2 *)
Lemma two_chain_cover_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (C0 C1 : Ensemble A) (n : nat),
    cardinal A (Full_set A) n -> Inhabited A (Full_set A) ->
    IsChain R C0 -> IsChain R C1 ->
    (forall x, Ensembles.In A (Full_set A) x ->
        Ensembles.In A C0 x \/ Ensembles.In A C1 x) ->
    forall d, PosetDimension R d -> d <= 2.
```
Proof sketch:
- Build `cover := fun c => c = C0 \/ c = C1` and `IsChainCover R (Full_set A) cover` from the
  hypotheses (chains, inclusion trivial, covers by the disjunction).
- `width_exists n Hcard Hinhab` ⟹ `exists w, inhabited (Width R (Full_set A) w)`; take `HW`.
- `dimension_le_width n d w Hcard Hdim HW : d <= w`.
- `w <= 2`: `Width` exposes `width_la` with `IsLargestAntichain (Full_set A) width_la w`
  (an antichain of cardinality `w`, included in `Full_set`). Obtain `cardinal cover ncov`
  (`ncov <= 2` from the `Add`/`card_add` form). If `w > ncov`, `pigeonhole_chains_antichains`
  gives two **distinct** antichain elements in a common chain ⟹ comparable ⟹ (antichain) equal
  — contradiction. So `w <= ncov <= 2`.
- `d <= w <= 2`.

NOTE: the `cardinal cover` value is `2` (if `C0 ≠ C1`) or `1`; either way `≤ 2`, and `w ≥ 3`
contradicts via pigeonhole. Handle the cover cardinality with `Add`/`card_add` (and a
`classic`/`==`-decision on `C0 = C1`), or — simpler — prove the antichain bound directly:
`forall anti, IsAntichain R anti -> Included A anti (Full_set A) -> forall m, cardinal A anti m -> m <= 2`
by extracting 3 distinct elements from `m ≥ 3` (`cardinal_invert` ×3), pigeonholing them into
`C0`/`C1`, and deriving comparability ⟹ equality ⟹ contradiction; then `w <= 2` since
`width_la` is such an antichain. Prefer whichever is cleaner; the direct antichain bound avoids
the `cover` cardinality bookkeeping.

## Component 2 — concrete 2-process block (`execution/TransformB.v`)

A standalone 4-event block = two disjoint 2-chains (process 0: `a0 ≺ a1`; process 1:
`b0 ≺ b1`; no cross relations — the "between syncs, no messages" shape):
```coq
Inductive B2 : Set := a0 | a1 | b0 | b1.
Definition B2_R (x y : B2) : Prop := … (* a0<a1, b0<b1, reflexive; a's || b's *)
```
- `B2_R` is an `IsPoset`; carrier finite (4 elements).
- `dim B2_R ≤ 2`: EITHER apply `two_chain_cover_dim_le2` with `C0 = {a0,a1}`, `C1 = {b0,b1}`
  (the faithful route), OR build `PosetDimension B2_R 2` directly via `dim2_record` (reusing #66:
  two key-based linear extensions + incomparable pair `a0,b0`) and weaken to `≤ 2`. Provide the
  `two_chain_cover_dim_le2` instantiation as the headline; `dim2_record` is the fallback.
- `B2_simplified` — Transformation B's "one local modification": the contracted block is a single
  chain (`p0 ≺ p1`), `dim = 1 ≤ 2` via `chain_dim_1`. (The simplification merges the two
  inter-sync segments into one local edge.)

## Component 3 — Transformation B as a dimension-property-preserving swap (`TransformB.v`)

```coq
(* a fully-sync execution all of whose blocks are 2-chain-covered (<= 2 dim) has dim <= 2;
   replacing one such block by another 2-chain-covered block preserves this. *)
Lemma transform_B_preserves_dim2 :
  forall E blocks,
    IsFullySync E blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension E d /\ d <= 2.
```
This is `fully_sync_dim_le2` (already proven) — the Transformation-B content is the per-block
hypothesis `dim ≤ 2`, which Component 1/2 supply for any 2-process block. State
`transform_B_preserves_dim2` as the named corollary and a `Remark` that a 2-process block
discharges the per-block obligation via `two_chain_cover_dim_le2` (each process = a chain). The
"swap" is: both the original and simplified blocks are ≤ 2, so the bound is invariant — matching
the paper's "preserves the dimension property."

## Component 4 — example (`execution/TransformBExamples.v`, test-only)

```coq
Example B2_dim_le2 : exists d, inhabited (PosetDimension B2_R d) /\ d <= 2.
Example transform_B_example :
  (* dim of <2-process block> <= 2  AND  dim of <simplified block> <= 2,
     so swapping preserves dim <= 2 *) …
```
Concrete `B2` (2-process block) and `B2_simplified` (chain), both `dim ≤ 2`, demonstrating the
equal-bound that drives the transformation. If the full execution-level swap is heavy, the
block-level equal-bound fact is the honest minimal example (as Transformation A fell back to).

## Files, wiring, testing
- New: `execution/TransformB.v` (exported), `execution/TransformBExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add both. `execution/Execution.v`: export `TransformB`.
- `docs/INDEX.md`: a "Transformation B" subsection.
- Whole-project green; **zero `Admitted`**; files <500 lines; each `Qed` <5 min.
- `Print Assumptions two_chain_cover_dim_le2` + the example recorded.

## Acceptance criteria
1. `TransformB.v`: `two_chain_cover_dim_le2`, the concrete `B2`/`B2_R` block (`dim ≤ 2`), the
   `B2_simplified` chain (`dim ≤ 2`), `transform_B_preserves_dim2`. Zero admits.
2. `TransformBExamples.v`: `B2_dim_le2`, `transform_B_example`. Zero admits.
3. Whole-project green; `Execution.v` exports `TransformB`; INDEX updated; assumptions recorded.

## Out of scope
The multi-frontier thick-barrier generalization; an execution-`sub_order`-level generic
2-process-block lemma (the bare-block realization + `fully_sync_dim_le2` corollary suffice);
any formalization of "critical pairs" as such (we formalize the equivalent dimension bound).

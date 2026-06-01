# Transformation A (Synchronization-Square Contraction) — Design (Sub-project B, transformations slice 1)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** the completed dimension arc — `FullySyncDimExact` (`fully_sync_dimension`), `FinPosetDimSurgery` (`fin_small_dim_le_2`'s total-order/singleton-realizer machinery, `fin_dim_exists`, `fin_posdim_unique`), `AntichainComplement` (`dim_ge_1_of_two`), `FullySync` (`IsFullySync`), `Ordinal`/`Poset` (`sub_order`, `ep_size_ok`), and `Dimension`.
**Paper:** NomaDB TechReport.

## Goal & framing

Formalize the paper's **Transformation A** (contract a 4-event "synchronization
square" — a bidirectional Pᵢ↔Pⱼ exchange with no local modifications between the
send/receive operations — into the "2 synchronized points" join/fork form) as a
**dimension-preserving block replacement** within a fully-synchronized execution.

**Why block replacement (not raw poset surgery):** the paper frames A as operating
"between synchronizations" and claims it preserves *critical-pair position / the
dimension property* (NOT order-isomorphism — confirmed by close reading; the
contraction geometry is informally specified). Our `fully_sync_dimension` makes a
fully-sync execution's dimension `max(1, maxᵢ dim Bᵢ)` — a function of the per-block
dimensions ONLY. So replacing one block by another of EQUAL dimension preserves the
whole execution's dimension, with no global critical-pair reasoning. Transformation
A is exactly such a replacement: the sync-square block and its contracted form have
equal dimension.

**Honest caveats (recorded):**
- The paper's square→2-points geometry is informally specified; `B_square` /
  `B_contracted` below are OUR concrete realization, chosen faithful in spirit.
- The natural sync square is a chain (dimension 1), and the contracted form is also
  a chain (dimension 1). So this slice demonstrates dimension *preservation* of the
  contraction at the block-dimension level — matching the paper, where A *preserves*
  (does not lower) dimension. The dimension reduction in NomaDB comes from the
  overall synchronization *pattern*, not from A itself.

## Library facts this builds on (verified present)

- `FullySyncDimExact.fully_sync_dimension : forall E blocks dims, IsFullySync E blocks -> length dims = length blocks -> (forall i, i < length blocks -> PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) -> (exists a b : ep_carrier E, a <> b) -> forall dW, PosetDimension (ep_order E) dW -> dW = Nat.max 1 (fold_right Nat.max 0 dims)`.
- `FinPosetDimSurgery.fin_small_dim_le_2` (builds the singleton realizer `{R}` of a total order, `cardinal {R} 1`, `dimension_is_minimum … : dW <= 1` — read its body); `fin_dim_exists`; `fin_posdim_unique`.
- `AntichainComplement.dim_ge_1_of_two : forall d, PosetDimension R d -> (exists a b, a <> b) -> 1 <= d` (R explicit).
- `IsFullySync`, `sub_order`, `ep_size_ok`, `cardinal_finite`.

## Component 1 — `chain_dim_1` (`execution/ChainDim.v`)

Generic, reusable: a total order on ≥2 elements has dimension exactly 1.

```coq
Lemma chain_dim_1 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)),
    (forall x y, R x y \/ R y x) ->        (* total order *)
    (exists a b : A, a <> b) ->            (* >= 2 elements *)
    PosetDimension R 1.
```
Proof (`Nat.le_antisymm` on `dW`, where `dW` from `fin_dim_exists`):
- `dW <= 1`: the singleton realizer `Singleton _ R` realizes the total `R` (R is its
  own linear extension), cardinality 1, `dimension_is_minimum … : dW <= 1`. Port the
  exact construction from `fin_small_dim_le_2` (it builds precisely this and derives
  `<= 1` before weakening to `<= 2`).
- `dW >= 1`: `dim_ge_1_of_two R dW HdW <≥2 elts>`.
- So `dW = 1`; but we want `PosetDimension R 1` — actually build it directly: get
  `dW` with `PosetDimension R dW` (fin_dim_exists), show `dW = 1` by the two bounds,
  `subst`/`rewrite` to conclude `PosetDimension R 1`.

## Component 2 — block-replacement dimension invariance (`execution/TransformA.v`)

```coq
Lemma transform_preserves_dimension :
  forall E blocks dims E' blocks' dims',
    IsFullySync E blocks -> length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    IsFullySync E' blocks' -> length dims' = length blocks' ->
    (forall i, i < length blocks' ->
       PosetDimension (sub_order E' (nth i blocks' (Empty_set _))) (nth i dims' 0)) ->
    (exists a b : ep_carrier E', a <> b) ->
    fold_right Nat.max 0 dims = fold_right Nat.max 0 dims' ->
    forall dW dW', PosetDimension (ep_order E) dW -> PosetDimension (ep_order E') dW' ->
      dW = dW'.
```
Proof: `fully_sync_dimension` on `E` ⟹ `dW = Nat.max 1 (fold_right Nat.max 0 dims)`;
on `E'` ⟹ `dW' = Nat.max 1 (fold_right Nat.max 0 dims')`; equal folds ⟹ `dW = dW'`
(`congruence`/`lia`). A direct corollary.

## Component 3 — the concrete square / contracted blocks (`TransformA.v`)

Two small posets, each a chain (dimension 1 via `chain_dim_1`), interchangeable as
blocks:
- **`B_square`** — the 4-event synchronization square as a standalone poset:
  events `{s0, r1, s1, r0}`, order the chain `s0 ≺ r1 ≺ s1 ≺ r0` (from `s0→r1` msg,
  `r1≺s1` prog, `s1→r0` msg, transitively a total order). Realize as a concrete
  finite poset (e.g. carrier `Fin 4` / a 4-element `nat` subset with `≤`), total.
  `dim B_square = 1` via `chain_dim_1` (it's a chain on 4 ≥2 elements).
- **`B_contracted`** — the "2 synchronized points": a 2-element chain `p0 ≺ p1`
  (one rendezvous point per process). Total, ≥2 elements. `dim B_contracted = 1`
  via `chain_dim_1`.
- `dim B_square = dim B_contracted = 1` (both `chain_dim_1`).

(Represent both as bare finite posets — `nat`-subset or `bool`/`Fin` carriers with
their `≤` — reusing the `chain2_R`-style pattern from `FinExtremumDimExamples.v` for
`B_contracted`, and an analogous 4-element chain for `B_square`.)

## Component 4 — Transformation A as a block swap (`TransformA.v`)

```coq
Lemma transform_A_preserves :
  forall E blocks dims E' blocks' dims',
    (* E and E' are fully-sync with block lists pre ++ [B_square-block] ++ suf
       and pre ++ [B_contracted-block] ++ suf, agreeing on pre/suf dims, and the
       swapped block has dim 1 on both sides *)
    IsFullySync E blocks -> … -> IsFullySync E' blocks' -> … ->
    (* the dims lists agree because the swapped block is dim 1 on both sides
       and pre/suf blocks are identical *)
    fold_right Nat.max 0 dims = fold_right Nat.max 0 dims' ->
    forall dW dW', PosetDimension (ep_order E) dW -> PosetDimension (ep_order E') dW' ->
      dW = dW'.
```
This is `transform_preserves_dimension` specialized to the case where `dims` and
`dims'` differ only in one slot, both equal to 1 (`dim B_square = dim B_contracted`),
so `fold_right Nat.max 0 dims = fold_right Nat.max 0 dims'` (the differing slot
contributes the same `1` to the max; surrounding slots identical). The fold-equality
hypothesis is discharged from "the two dims lists agree pointwise except at the
swapped index, where both are 1" — a `fold_right Nat.max` congruence (prove a small
`fold_max_eq_of_pointwise` or just supply `dims`/`dims'` that are literally equal
lists where the swapped block's `1` sits in the same position).

Simplest concrete form: state `transform_A_preserves` with `dims = dims'` literally
(both block lists yield the SAME dims list — `pre`-dims ++ `[1]` ++ `suf`-dims), so
the fold-equality is `eq_refl` and `transform_preserves_dimension` closes it. The
"transformation" is: same dims list, different executions (one with `B_square`, one
with `B_contracted`), same dimension.

## Component 5 — concrete example (`execution/TransformAExamples.v`, test-only)

A concrete small fully-sync execution containing the square block and its contracted
variant, with `dim` shown equal:
```coq
Example transform_A_example :
  (* dim of <fully-sync exec with B_square block> = dim of <same with B_contracted> *)
  …
```
Build two concrete fully-sync executions (or reuse the all-singleton chain pattern
extended with the square/contracted block) and apply `transform_A_preserves` /
`transform_preserves_dimension`. If constructing two full `IsFullySync` witnesses is
heavy, the minimal honest example is: `dim B_square = dim B_contracted = 1` (two
`chain_dim_1` applications) — demonstrating the per-block equal-dimension fact that
drives the transformation. Prefer the fuller execution-level example if tractable;
fall back to the block-level equal-dimension fact otherwise.

## Files, wiring, testing

- New: `execution/ChainDim.v`, `execution/TransformA.v`, `execution/TransformAExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the three modules.
- `execution/Execution.v`: export `ChainDim TransformA` (not the examples).
- `docs/INDEX.md`: add a "Transformation A" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero
  `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `transform_preserves_dimension`, `chain_dim_1`, and the
  example — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `ChainDim.v`: `chain_dim_1`. Zero admits.
2. `TransformA.v`: `transform_preserves_dimension`, `B_square`/`B_contracted` (each
   `dim = 1`), `transform_A_preserves`. Zero admits.
3. `TransformAExamples.v`: `transform_A_example` (execution-level, or the block-level
   fallback). Zero admits.
4. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope

Transformation B (separate later slice); sync-shape operational definitions at the
`Op`/`Schedule` program level; the full reduce-to-sync-shape pipeline; the `E_min`
exact cross-check (task #66).

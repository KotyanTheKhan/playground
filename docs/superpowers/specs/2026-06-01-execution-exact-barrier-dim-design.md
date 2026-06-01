# Exact Barrier Dimension — Design (exact n-way dim=max, slice 1 of 2)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** n-way slice 1 (`FinPosetDimSurgery` — `fin_lift_min/max`, `fin_global_min/max`, `fin_sub_order`, `fin_dim_exists`, `fin_small_dim_le_2`; `FinPosetDim` — `fin_is_barrier`, `fin_block_dim0_global_min/max`, `fin_barrier_dimension`), `DimIso` (`dimension_iso`), and the `Dimension` theory (`subposet_dimension_le`, `dim_ge_1_of_two`, `posdim_unique`, `cardinal_Im_injective`, `cardinalO_empty`, `linear_sum_dimension`).
**Paper:** NomaDB TechReport.

## Goal & decomposition

The exact n-way dimension of a fully-synchronized execution: `dim(whole) =
max(1, maxᵢ dim(Bᵢ))` for executions with ≥2 elements. This is the exact-dimension
sibling of the completed dim≤2 n-way lever (`fully_sync_dim_le2`).

**Why `max(1, …)` and not plain `max`:** in this formalization a singleton (or
empty) poset has dimension **0** (the empty realizer is valid). An n-block ordinal
sum of singletons (a chain) has whole-dimension 1, but `maxᵢ dim(Bᵢ) = 0`. So the
honest closed form carries a `max(1, …)` correction, and the binary
`barrier_dimension` (which needs both blocks `dim > 0`) does NOT suffice for
singleton blocks.

The full result is too large for one spec — it re-does the extremum-surgery +
barrier arc at the **exact** dimension level. Decomposition:
- **Slice 1 (this spec):** the exact extremum-surgery lemmas (`fin_add_min_dim`,
  `fin_add_max_dim`: adding a global extremum gives `dim = max(d, 1)`) + the binary
  all-cases `fin_barrier_dimension_full` (`dim = max(1, max(dL, dU))`).
- **Slice 2 (later):** the n-way `fin_fully_sync_dimension` + its
  `ExecPoset`/`IsFullySync` instance `fully_sync_dimension`.

## Library facts this builds on (verified present)

- `linear_sum_dimension : PosetDimension RA dA -> PosetDimension RB dB -> PosetDimension LinearSumRel dSum -> 0<dA -> 0<dB -> dSum = max dA dB` (LinearSum.v).
- `barrier_dimension`/`fin_barrier_dimension : … -> 0 < dL -> 0 < dU -> d = Nat.max dL dU`.
- `dim_ge_1_of_two : forall d, PosetDimension R d -> (exists a b, a <> b) -> 1 <= d` (AntichainComplement.v).
- `posdim_unique`, `subposet_dimension_le`, `cardinalO_empty`, `cardinal_Im_injective`.
- `fin_lift_min/max` (+ `_is_linext`, `_inj`), `fin_global_min/max`, `fin_sub_order`, `fin_dim_exists`, `fin_small_dim_le_2` (FinPosetDimSurgery).
- `fin_is_barrier`, `fin_block_dim0_global_min/max` (`PosetDimension (fin_sub_order R L) 0 -> exists m, fin_global_min R m /\ (forall x, In U x <-> x <> m)`), `fin_barrier_dimension` (FinPosetDim).

## Component 1 — exact extremum lemmas (`execution/FinExtremumDim.v`)

On a `Section` with `Context {A} (R) {HR : IsPoset A R} (Hfin : Finite A (Full_set A))`:

```coq
Lemma fin_add_min_dim :
  forall m, fin_global_min R m ->
    (exists x, x <> m) ->                                  (* the rest is inhabited *)
    forall d, PosetDimension (fin_sub_order R (fun x => x <> m)) d ->
      forall dW, PosetDimension R dW -> dW = Nat.max d 1.

Lemma fin_add_max_dim :
  forall m, fin_global_max R m ->
    (exists x, x <> m) ->
    forall d, PosetDimension (fin_sub_order R (fun x => x <> m)) d ->
      forall dW, PosetDimension R dW -> dW = Nat.max d 1.
```

**The `(exists x, x <> m)` hypothesis is required:** without it, `R = {m}` (a
singleton) has `dW = 0` but `max(d,1) = max(0,1) = 1` — the equation would fail.
With it, `R` has ≥2 elements.

Proof of `fin_add_min_dim` (both bounds; `Nat.le_antisymm`):
- **`dW ≤ max(d, 1)`** (the surgery): case `d`.
  - `d = S d'`: the rest's realizer has `d` linear extensions; lift each by placing
    `m` at the bottom (`fin_lift_min m LB`, already proven a linear extension
    (`fin_lift_min_is_linext`) and injective (`fin_lift_min_inj`)). The image
    realizer of `R` has cardinality `d` (`cardinal_Im_injective`); it IS a realizer
    (every pair of `R` is forced — `m` below all, off-`m` from the rest's
    realizer). `dimension_is_minimum` ⟹ `dW ≤ d = max(d,1)`. (This is exactly the
    backward direction of `fin_remove_min_dim2`, but tracking exact cardinality `d`
    rather than `≤ 2`. Port that proof.)
  - `d = 0`: the rest is a singleton ⟹ `R` is a 2-element chain (total order). A
    single linear extension `= R` is a realizer (cardinality 1); `dimension_is_minimum`
    ⟹ `dW ≤ 1 = max(0,1)`. (Reuse `fin_small_dim_le_2`'s totality argument, sharpened
    to a size-1 realizer.)
- **`dW ≥ max(d, 1)`** (two parts, `Nat.max_lub`):
  - `dW ≥ d`: the rest `fin_sub_order R (fun x => x <> m)` is a subposet of `R`
    (`subposet_dimension_le R (fun x => x <> m) dW HdW` gives `exists dq, … /\ dq ≤ dW`;
    `posdim_unique` identifies `dq = d`); so `d ≤ dW`.
  - `dW ≥ 1`: `R` has two distinct elements (`m` and the witness `x ≠ m` from the
    hypothesis); `dim_ge_1_of_two dW HdW (ex x m …)` ⟹ `1 ≤ dW`.

`fin_add_max_dim` is the dual (place `m` at the top via `fin_lift_max`).

If `FinExtremumDim.v` approaches 500 lines, split `fin_add_max_dim` (+ helpers) into
`execution/FinExtremumDimMax.v`.

## Component 2 — binary exact barrier dimension (`FinExtremumDim.v`)

```coq
Lemma fin_barrier_dimension_full :
  forall L U, fin_is_barrier R L U ->
    forall dL dU dW,
      PosetDimension (fin_sub_order R L) dL ->
      PosetDimension (fin_sub_order R U) dU ->
      PosetDimension R dW ->
      dW = Nat.max 1 (Nat.max dL dU).
```
(`fin_is_barrier` guarantees `L`, `U` both inhabited ⟹ `R` has ≥2 elements, making
the `max 1 (…)` exact in every case.)

Proof by case on `dL`, `dU` (mirrors `fin_barrier_dim_le2`'s 3-case split):
- **both `> 0`:** `fin_barrier_dimension R L U HB dL dU dW … (0<dL)(0<dU) : dW = max dL dU`;
  since both `> 0`, `max dL dU ≥ 1`, so `= max 1 (max dL dU)` (`lia`).
- **`dL = 0`:** `fin_block_dim0_global_min R L U HB HdL` gives `m` (global min) with
  `forall x, In U x <-> x <> m`. So `U = (fun x => x <> m)` (ensemble equality via
  `functional_extensionality`+`propositional_extensionality`), and
  `fin_sub_order R U = fin_sub_order R (fun x => x <> m)` (so `dU` is the rest's
  dimension). `U` inhabited (from `fin_is_barrier`) ⟹ `exists x, x <> m`.
  `fin_add_min_dim R m Hmin (that) dU dW … : dW = max dU 1`. With `dL = 0`:
  `max 1 (max 0 dU) = max 1 dU = max dU 1 = dW` (`lia`).
- **`dL = S _`, `dU = 0`:** symmetric via `fin_block_dim0_global_max` + `fin_add_max_dim`
  (`L = {x | x <> m}`, `m` global max).
(The both-`0` case is subsumed by `dL = 0` with `dU = 0`: `dW = max 0 1 = 1 = max 1 (max 0 0)`.)

## Component 3 — concrete instance (`execution/FinExtremumDimExamples.v`, test-only)

`E_min` (4 events, dim 2) with its bottom barrier `Lmin = {a} | Umin = {b,c,d}`
(`a` a global min, `Lmin` a singleton ⟹ `dim Lmin = 0` — exercises the
`fin_add_min_dim` / `dL = 0` path):

```coq
Example E_min_exact_dim_via_barrier :
  exists dW, PosetDimension (ep_order E_min) dW /\ dW = 2.
```
Instantiate `fin_barrier_dimension_full` at `(ep_carrier E_min, ep_order E_min, Hfin)`
with `E_min_barrier` (as a `fin_is_barrier (ep_order E_min) Lmin Umin`), needing:
- `dim (fin_sub_order (ep_order E_min) Lmin) = 0` — `Lmin = {a}` is a singleton; its
  sub-poset has the empty realizer ⟹ dimension 0 (provide a `PosetDimension … 0`
  witness: empty realizer, `card_empty`, minimality `0 ≤ n`). A small
  `singleton ⟹ dim 0` sub-lemma.
- `dim (fin_sub_order (ep_order E_min) Umin) = 2` — the `{b,c,d}` block is exactly
  dimension 2 (`c < d`, `b` incomparable to both). An explicit-realizer sub-proof
  `dim_block_bcd_2` (~the effort of `E_min_dim_2`: two linear extensions whose
  intersection is the block order, plus an incomparable pair for `dim ≥ 2`).
- then `fin_barrier_dimension_full` gives `dim E_min = max(1, max(0, 2)) = 2`,
  cross-checking the existing `E_min_dim_2`.

**Fallback** (if `dim_block_bcd_2` overruns): a cheap 2-element-chain example
exercising `fin_add_min_dim` with `d = 0` (`dim = max(0,1) = 1`), instead of the
`E_min` cross-check.

## Files, wiring, testing

- New: `execution/FinExtremumDim.v` (+ optional `FinExtremumDimMax.v`),
  `execution/FinExtremumDimExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the new modules.
- `execution/Execution.v`: export `FinExtremumDim` (+ `FinExtremumDimMax` if split);
  NOT the examples.
- `docs/INDEX.md`: add an "Exact barrier dimension" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero
  `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `fin_barrier_dimension_full` and the example — expected only
  standard classical/choice axioms; recorded.

## Acceptance criteria

1. `FinExtremumDim.v`: `fin_add_min_dim`, `fin_add_max_dim` (`dim = max(d,1)`),
   `fin_barrier_dimension_full` (`dim = max(1, max(dL, dU))`). Zero admits.
2. `FinExtremumDimExamples.v`: `E_min_exact_dim_via_barrier` (or the 2-chain
   fallback). Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (slice 2 and beyond)

The n-way `fin_fully_sync_dimension` (`dim = max(1, maxᵢ dim Bᵢ)`, by induction on
the block list reusing the slice-1 binary lemma + the `fin_fully_sync_dim_le2`
induction skeleton) and its `ExecPoset`/`IsFullySync` instance `fully_sync_dimension`;
the paper transformations; sync-shape operational definitions.

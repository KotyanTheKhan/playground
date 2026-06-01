# Execution Extremum Reduction — Design (Sub-project B, part 3, slice 2)

**Date:** 2026-05-31
**Branch:** `execution_poset`
**Depends on:** A (core), B part 1 (`DimBridge` — `exec_has_dimension`, `exec_dimension_exists`), B part 2 (`Ordinal` — `sub_order`, `posdim_unique`), B part 3 slice 1 (`Reduction` — `subposet_reduces_dim`, `reduces_dim2`), `DimExamples`/`FrontierExamples` (`E_min`, `hb_a_*`), and the `Dimension` theory.
**Paper:** NomaDB TechReport.

## Context: a correction that motivates this slice

While scoping the "critical-pair-preservation" slice we found that the library's
`no_alt_cycle` (`~∃ alternating cycle of critical pairs`) is equivalent to
"∃ a *single* linear extension reversing all critical pairs" — **strictly stronger
than `dim ≤ 2`** (a 2-realizer splits the reversal across two extensions). E.g.
`{b,c,d}` (`c < d`, `b` incomparable to both) is dimension 2 but fails
`no_alt_cycle` (reversing `(c,b)` and `(b,d)` forces `d < b < c`, contradicting
`c < d`). So the `no_alt_cycle`-based `dim ≤ 2` lemmas (`exec_dim_le_2_of_no_alt_cycle`,
`barrier_dim2`, `fully_sync_dim2`) are *sound but rarely applicable* to
genuine-dim-2 posets. The **genuine** `dim ≤ 2` levers are explicit realizers,
`dimension_iso`, `barrier_dimension` (`dim = max`), and the reduction framework.
This slice delivers a real, paper-aligned reduction (removing a non-critical
element) proven through **exact dimension / realizers**, not `no_alt_cycle`.

Note also: a singleton/empty poset has dimension **0** in this formalization (the
empty realizer is valid), so `barrier_dimension`/`linear_sum_dimension` (which
require both blocks' dimensions `> 0`) cannot handle the singleton `{m}` block from
removing one element. The mechanism is therefore **direct realizer surgery**:
adding a global extremum gives `dim = max(dim rest, 1)`.

## Library facts this builds on (verified present)

- `DimDefs`: `PosetDimension`, `IsRealizer`, `IsLinearExtension`, `IsTotalOrder`.
- `Ordinal`: `sub_order E S := fun (x y : {z | In S z}) => ep_order E (proj1_sig x)(proj1_sig y)`; `Instance sub_order_poset`; `posdim_unique`.
- `Reduction`: `subposet_reduces_dim`, `reduces_dim2`.
- `DimBridge`: `exec_has_dimension E d := inhabited (PosetDimension (ep_carrier E)(ep_order E) d)`; `exec_dimension_exists`.
- `DimExamples`: `E_min`, `E_min_dim_2`, and `hb_a_b`/`hb_a_c`/`hb_a_d` (the global-min facts for `a = (0,0)`); `valid_event_min_cases`.

## Component 1 — extremum predicates & the realizer-surgery core (`execution/ExtremumReduction.v`)

```coq
Definition IsGlobalMin (E : ExecPoset) (m : ep_carrier E) : Prop :=
  forall x, ep_order E m x.
Definition IsGlobalMax (E : ExecPoset) (m : ep_carrier E) : Prop :=
  forall x, ep_order E x m.

(* The "remove m" subposet. *)
Notation removed E m := (sub_order E (fun x => x <> m)).
```

**The reduction theorem (the substantive result):**

```coq
Lemma remove_min_preserves_dim2 :
  forall E m, IsGlobalMin E m ->
    ((exists d, inhabited (PosetDimension (removed E m) d) /\ d <= 2)
     <->
     (exists d, exec_has_dimension E d /\ d <= 2)).

Lemma remove_max_preserves_dim2 :
  forall E m, IsGlobalMax E m ->
    ((exists d, inhabited (PosetDimension (removed E m) d) /\ d <= 2)
     <->
     (exists d, exec_has_dimension E d /\ d <= 2)).
```

Proof structure for `remove_min_preserves_dim2`:
- **Forward** (`E dim ≤ 2 ⟹ block dim ≤ 2`): the block is `sub_order E (fun x => x <> m)`; `subposet_reduces_dim` gives `ReducesDim (removed E m) (ep_order E)`; `reduces_dim2` transports `dim ≤ 2` down. (Reuses the reduction framework; easy.)
- **Backward** (`block dim ≤ 2 ⟹ E dim ≤ 2`): the realizer surgery.
  1. From `exists d, inhabited (PosetDimension (removed E m) d) /\ d <= 2`, get a realizer `RB` of `removed E m` with `cardinal RB d`, `d <= 2`.
  2. Lift each linear extension `LB` of the block to a linear extension `LE` of `ep_order E`:
     ```coq
     LE a b := a = m \/ (b <> m /\ exists (Ha : a <> m)(Hb : b <> m),
                          LB (exist _ a Ha) (exist _ b Hb)).
     ```
     (`m` is placed at the bottom; off `m`, follow `LB`.) Use `proof_irrelevance` for the witness proofs.
  3. Prove `IsLinearExtension (ep_order E) LE`:
     - total: case `a = m` / `b = m` / both `≠ m` (use `LB` totality);
     - `IsPoset LE`: refl/antisym/trans by the same case split (`m` below all; off-`m` from `LB`);
     - `linear_extends`: `ep_order E a b -> LE a b`. If `a = m`, left disjunct. Else `a <> m`; then `b <> m` (else `ep_order E a m` with `m` global min forces `a = m` by antisymmetry — contradiction), so use `LB`'s `linear_extends` (note `removed E m` order on the projections is `ep_order E a b`).
  4. The lifted realizer `RE := Im _ _ RB (lift)` (map `LB ↦ LE`). Show `IsRealizer (ep_order E) RE`:
     - `realizer_linear`: each member is a lift, a linear extension (step 3);
     - `realizer_intersection`: `ep_order E a b <-> forall LE in RE, LE a b`. For `a = m`: every `LE m b` holds (left disjunct) and `ep_order E m b` holds (global min) — both sides true. For `a <> m, b = m`: `ep_order E a m` is false (global min + antisym) and some `LE a m` is false (right disjunct needs `b <> m`) — both false. For `a, b <> m`: reduces to `RB`'s intersection (`= removed E m` order `= ep_order E a b`).
     - cardinal: `lift` is injective (recover `LB` from `LE` by restriction), so `cardinal RE d` via `cardinal_Im_injective`.
  5. `d <= 2` and `RE` a realizer of `ep_order E` ⇒ `dim (ep_order E) <= 2` via `dimension_is_minimum` + `exec_dimension_exists`; package as `exists d', exec_has_dimension E d' /\ d' <= 2`.
- `remove_max_preserves_dim2`: dual (append `m` at top).

This is the one genuinely substantive proof (~150–250 lines), structurally similar to the `LP` construction (`Ordinal.v`) and `dimension_iso` (`DimIso.v`). If it overruns 500 lines, split the `IsLinearExtension`/`IsRealizer` lemmas into a helper file.

## Component 2 — concrete instance (`execution/ExtremumReductionExamples.v`, test-only)

```coq
Example E_min_a_global_min : IsGlobalMin E_min ev_a.   (* ev_a = the (0,0) event from DimExamples *)
Example E_min_remove_min_dim2 :
  (exists d, inhabited (PosetDimension (removed E_min ev_a) d) /\ d <= 2)
  <->
  (exists d, exec_has_dimension E_min d /\ d <= 2).
Example E_min_block_dim_le_2_via_extremum :
  exists d, inhabited (PosetDimension (removed E_min ev_a) d) /\ d <= 2.
```

Strategies:
- `E_min_a_global_min`: `intro x`; by `valid_event_min_cases x`, `proj1_sig x ∈ {(0,0),(0,1),(1,0),(1,1)}`; for `(0,0)` it's `ep_order E_min a a` (refl), for the others use `hb_a_b`/`hb_a_c`/`hb_a_d` (canonicalizing via `proof_irrelevance` as in `DimExamples`/`FrontierExamples`). (Reuse the `ev_a`/`eq_ev_*` helpers.)
- `E_min_remove_min_dim2`: `apply (remove_min_preserves_dim2 E_min ev_a E_min_a_global_min)`.
- `E_min_block_dim_le_2_via_extremum`: the `<-` direction of `E_min_remove_min_dim2` applied to `E_min`'s known `dim ≤ 2` (from `E_min_dim_2`: `exists 2; split; [exact E_min_dim_2 | lia]`) — i.e. demonstrate the reduction yields the block's `dim ≤ 2` (the genuine replacement for the impossible `no_alt_cycle` instance).

## Files, wiring, testing

- New: `execution/ExtremumReduction.v`, `execution/ExtremumReductionExamples.v`.
- `execution/dune` + `_CoqProject`: add the two modules.
- `execution/Execution.v`: export `ExtremumReduction` (not the examples).
- `docs/INDEX.md`: add an "Extremum reduction" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero `Admitted`**. Files <500 lines (split the surgery if needed), each `Qed` <5 min.
- `Print Assumptions` on `remove_min_preserves_dim2` and `E_min_block_dim_le_2_via_extremum` — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `ExtremumReduction.v`: `IsGlobalMin`/`IsGlobalMax`, `remove_min_preserves_dim2`, `remove_max_preserves_dim2`. Zero admits.
2. `ExtremumReductionExamples.v`: `E_min_a_global_min`, `E_min_remove_min_dim2`, `E_min_block_dim_le_2_via_extremum`. Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later slices)

The paper's Transformation A/B (synchronization-square contraction) — which would
exhibit `dimension_iso`/`embedding`/extremum-style witnesses and apply the
framework; the n-way `fully_sync_dimension` (deferred); sync-shape operational
definitions; the reduce-to-sync-shape pipeline. (Also tracked: the
`no_alt_cycle`-based lemmas should be re-documented as the stronger
"single-extension-reversible" condition — a separate cleanup, not this slice.)

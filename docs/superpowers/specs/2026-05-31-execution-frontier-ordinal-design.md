# Execution Frontiers & Ordinal-Sum Decomposition — Design (Sub-project B, part 2)

**Date:** 2026-05-31
**Branch:** `execution_poset`
**Depends on:** sub-project A (`execution/` core), B part 1 (`DimBridge`, `DimCriticalPairs` — esp. `exec_dim_le_2_of_no_alt_cycle`, `exec_critical_pair`), and the `Dimension` theory (`DimDefs`, `CriticalPairs`, `Theorems`, `LinearSum`).
**Paper:** NomaDB TechReport.

## Where this sits

Sub-project B is "reductions to sync-shape + dimension-preservation". B part 1
built the dimension bridge. **This spec is B part 2, first slice: the frontier /
Ψ(N,S) theory and the ordinal-sum decomposition** — the structural backbone the
paper's reduction strategy rests on. It deliberately **excludes** (a) the
enumeration counts (1,2,10,40,180) and minimal-depth numbers (5,7,9) — hard
combinatorics, the same flavor as the pruned N5 work; (b) any *universal* dim-2
claim (the paper only proves dim-2 for N=3 and specific patterns); (c) the
reduction transformations A/B themselves (later slices).

## Paper definitions used (precise)

- **Frontier**: a set `F` of poset points that can exist simultaneously; any two
  points joined by a directed path cannot share a frontier (⇒ antichain); frontier
  size = number of processes (one point per process).
- **Fully synchronized** `F1 ≺ F2`: every element of `F1` precedes every element of
  `F2`.
- **Minimal mΨ**: no intermediate frontier synchronized with one boundary but not
  the other.

## Modeling notes (important)

- The ordinal-sum theory is cleanest stated **abstractly on a finite poset** — it is
  exactly what the library's `LinearSum` proves on the sum type `A + B`. We state it
  on an `ExecPoset E` (carrier `ep_carrier E`, order `ep_order E`).
- Our example `sched_n3` has **no non-trivial barrier** (its process-0 last event and
  process-2 events are concurrent; the top is not a global max). But `E_min` (from B
  part 1) **does**: its bottom event `a = (0,0)` lies below all of `{b,c,d}`, so
  `{a} | {b,c,d}` is a barrier. We use `E_min` as the concrete instance.
- Genuinely fully-synchronized executions come from rendezvous synchronizations,
  which the one-op-per-frontier `Schedule` cannot directly express; the theory here
  is therefore stated at the `ExecPoset` / general level, independent of how the
  execution was built.

## Library facts this builds on (verified present)

- `LinearSum.v` (Section with `RA : A->A->Prop`, `RB : B->B->Prop`, both `IsPoset`):
  `LinearSumRel : A + B -> A + B -> Prop` (ordinal sum);
  `linear_sum_critical_pairs : IsCriticalPair LinearSumRel x y <-> (within-A or within-B critical pair)`;
  `linear_sum_dimension : PosetDimension RA dA -> PosetDimension RB dB -> PosetDimension LinearSumRel dSum -> 0<dA -> 0<dB -> dSum = max dA dB`.
- `Theorems.v`: `subposet_dimension_le` (subposet dimension ≤ whole); `subtype_is_poset` (`{x | In S x}` is a poset under the restricted relation).
- B part 1: `exec_critical_pair E x y := IsCriticalPair (ep_order E) x y`; `exec_dim_le_2_of_no_alt_cycle : ~(alt cycle of critical pairs) -> exists d, exec_has_dimension E d /\ d<=2`; `IsAlternatingCycle`.

## Component 1 — frontiers & barriers (`execution/Frontier.v`)

Stated on `Context (E : ExecPoset)`. Public names fixed.

```coq
Definition ConsistentCut (C : Ensemble (ep_carrier E)) : Prop :=
  forall x y, ep_order E x y -> Ensembles.In _ C y -> Ensembles.In _ C x.   (* down-closed under hb *)

Definition Frontier (F : Ensemble (ep_carrier E)) : Prop :=
  exists C, ConsistentCut C /\
            (forall x, Ensembles.In _ F x <-> (Ensembles.In _ C x /\ forall y, Ensembles.In _ C y -> ~ ep_order E x y \/ y = x)).
  (* F = maximal elements of a consistent cut C *)

Definition IsBarrier (L U : Ensemble (ep_carrier E)) : Prop :=
  (forall x, Ensembles.In _ L x \/ Ensembles.In _ U x) /\         (* cover *)
  (forall x, ~ (Ensembles.In _ L x /\ Ensembles.In _ U x)) /\     (* disjoint *)
  (exists x, Ensembles.In _ L x) /\ (exists y, Ensembles.In _ U y) /\ (* both inhabited *)
  (forall x y, Ensembles.In _ L x -> Ensembles.In _ U y -> ep_order E x y). (* L wholly below U *)
```

**Structural lemmas (guaranteed):**
- `frontier_is_antichain : Frontier F -> forall x y, In F x -> In F y -> ep_order E x y -> x = y`.
- `barrier_lower_consistent : IsBarrier L U -> ConsistentCut L` (L is down-closed: if `hb x y`, `y∈L`, then `x∈L` — else `x∈U` and barrier gives `hb y x`, with `hb x y` ⇒ `x=y∈L`, contra).
- `barrier_upper_disjoint_below : IsBarrier L U -> forall x y, In U x -> In L y -> ~ ep_order E x y` (no U→L edge; from barrier + antisymmetry).

## Component 2 — the dimension-iso lemma (`execution/DimIso.v`)

Reusable general poset machinery (isolated; could later move to `posets/dimension`).

```coq
Lemma dimension_iso :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S}
         (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->        (* bijection *)
    (forall a a', R a a' <-> S (f a) (f a')) ->                  (* order iso *)
    forall d, PosetDimension R d -> PosetDimension S d.
```
Strategy: map a realizer of `R` to a realizer of `S` by transporting each linear
extension `L` to `fun b b' => L (g b) (g b')`; the bijection makes this a linear
extension of `S`, preserves intersection (`= S`) and cardinality, and minimality
transports symmetrically (apply the lemma both ways with `f`,`g` swapped). ~80–150
lines. ZERO admits; if it stalls, this whole component plus the `barrier_dimension`
stretch is deferred (the guaranteed group in Component 3 does not depend on it).

## Component 3 — barrier decomposition (`execution/Ordinal.v`)

Sub-posets of a barrier: `P|L := (fun (x y : {z | In L z}) => ep_order E (proj1_sig x) (proj1_sig y))` (via `subtype_is_poset`), similarly `P|U`.

Define once: `no_alt_cycle (A:Type) (R:A->A->Prop) : Prop := ~ (exists cycle, (forall p, List.In p cycle -> IsCriticalPair R (fst p) (snd p)) /\ IsAlternatingCycle R cycle)`.

**Guaranteed group:**
- `barrier_critical_pairs : IsBarrier L U -> forall x y, exec_critical_pair E x y -> (In L x /\ In L y) \/ (In U x /\ In U y)` — direct: a cross pair is comparable (barrier), hence not incomparable, hence not critical.
- `barrier_dim_ge : IsBarrier L U -> forall dL dU d, PosetDimension (P|L) dL -> PosetDimension (P|U) dU -> PosetDimension (ep_order E) d -> max dL dU <= d` — from `subposet_dimension_le` on each block.
- `barrier_no_alt_cycle_propagation : IsBarrier L U -> no_alt_cycle _ (P|L) -> no_alt_cycle _ (P|U) -> no_alt_cycle _ (ep_order E)` — an alternating cycle of `ep_order E`-critical pairs cannot cross blocks: every `ep_order E`-critical pair lies within a block (`barrier_critical_pairs`) and the connecting `R`-relations only go L→U (never U→L, by `barrier_upper_disjoint_below`), so any cycle stays within a single block; a whole-poset critical pair within `L` is also a `P|L`-critical pair (the down/up conditions restrict), so that cycle is a `P|L` alternating cycle, contradicting `no_alt_cycle _ (P|L)`. (Phrased in terms of `no_alt_cycle`, NOT dim ≤ 2, so it does **not** depend on the deferred converse.)
  - Corollary `barrier_dim2 : IsBarrier L U -> no_alt_cycle _ (P|L) -> no_alt_cycle _ (P|U) -> exists d, exec_has_dimension E d /\ d <= 2` — apply `barrier_no_alt_cycle_propagation` then `exec_dim_le_2_of_no_alt_cycle` to the **whole** `ExecPoset E` (the blocks appear only through `no_alt_cycle`, so no block-level dim lemma is needed). **The reduction lever.**

**Stretch:**
- `barrier_dimension : IsBarrier L U -> forall dL dU d, PosetDimension (P|L) dL -> PosetDimension (P|U) dU -> PosetDimension (ep_order E) d -> 0<dL -> 0<dU -> d = max dL dU` — build the order-iso `ep_carrier E ≅ {x|L x} + {x|U x}` with `ep_order E ≅ LinearSumRel (P|L) (P|U)` (the barrier makes every L→U pair related and no U→L — exactly `LinearSumRel`), transport via `dimension_iso`, invoke `linear_sum_dimension`.

**Iterated decomposition:**
- `IsFullySync (blocks : list (Ensemble (ep_carrier E))) : Prop` — the blocks are nonempty, pairwise disjoint, cover the carrier, and for each `i` the split `(B0∪…∪Bi) | (B_{i+1}∪…∪B_last)` is an `IsBarrier`.
- `fully_sync_no_alt_cycle : IsFullySync blocks -> (forall blk, List.In blk blocks -> no_alt_cycle _ (P|blk)) -> no_alt_cycle _ (ep_order E)` — induction on `blocks`, iterating `barrier_no_alt_cycle_propagation`.
- `fully_sync_dim2 : IsFullySync blocks -> (forall blk, List.In blk blocks -> no_alt_cycle _ (P|blk)) -> exists d, exec_has_dimension E d /\ d <= 2` — `fully_sync_no_alt_cycle` then `exec_dim_le_2_of_no_alt_cycle`. **Headline reduction-enabling theorem (guaranteed):** every block free of alternating cycles ⟹ the whole fully-synchronized execution is dim ≤ 2.
- `fully_sync_dimension : IsFullySync blocks -> dim (ep_order E) = max over blocks of (dim P|blk)` — iterate `barrier_dimension` (stretch; rides on `barrier_dimension`).

## Component 4 — concrete instance (`execution/FrontierExamples.v`, test-only)

- `E_min` from B part 1; events `a=(0,0), b=(0,1), c=(1,0), d=(1,1)`.
- `Lmin := fun x => proj1_sig x = (0,0)`; `Umin := fun x => proj1_sig x <> (0,0)`.
- `Example E_min_barrier : IsBarrier E_min Lmin Umin` — `a ≺ b,c,d` gives "L wholly below U"; cover/disjoint/inhabited by `valid_event_min_cases`-style case analysis (reuse the technique from `DimExamples.v`).
- `Example E_min_barrier_cps : forall x y, exec_critical_pair E_min x y -> (In Lmin x /\ In Lmin y) \/ (In Umin x /\ In Umin y)` — apply `barrier_critical_pairs` to `E_min_barrier`.
- If the stretch lands: re-derive `dim E_min = max(1,2) = 2` through `barrier_dimension` as a cross-check of `E_min_dim_2`.

## Files, wiring, testing

- New: `execution/Frontier.v`, `execution/DimIso.v`, `execution/Ordinal.v`, `execution/FrontierExamples.v`.
- `execution/dune` + `_CoqProject`: add the four modules.
- `execution/Execution.v`: export `Frontier DimIso Ordinal` (not `FrontierExamples`).
- `docs/INDEX.md`: add a "Frontier / ordinal decomposition" subsection.
- Every file builds via `.claude/scripts/timed-build.sh`; whole-`execution` and `@all` green; **zero `Admitted`** (stretch deferred, not admitted). Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `fully_sync_dim2` and `barrier_critical_pairs` — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `Frontier.v`: definitions + `frontier_is_antichain`, `barrier_lower_consistent`, `barrier_upper_disjoint_below`. Zero admits.
2. `Ordinal.v` guaranteed group: `no_alt_cycle`, `barrier_critical_pairs`, `barrier_dim_ge`, `barrier_no_alt_cycle_propagation`, `barrier_dim2`, `fully_sync_no_alt_cycle`, `fully_sync_dim2`. Zero admits.
3. `DimIso.v` `dimension_iso` + `Ordinal.v` `barrier_dimension`/`fully_sync_dimension` proven OR cleanly deferred (tracked, never admitted).
4. `FrontierExamples.v`: `E_min_barrier`, `E_min_barrier_cps`. Zero admits.
5. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later B slices)

The reduction transformations A/B and their preservation proofs; sync-shape /
synchronization operational definitions on the program level; the enumeration
counts / minimal-depth numbers; universal dim-2.

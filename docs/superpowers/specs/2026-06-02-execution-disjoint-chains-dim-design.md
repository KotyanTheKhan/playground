# Disjoint-union-of-chains ⟹ dim ≤ 2; frontier blocks discharge the per-block bound — Design

**Date:** 2026-06-02
**Branch:** `execution_poset`
**Closes:** critical-review **finding 2** — `fully_sync_dim_le2`'s per-block `dim ≤ 2` hypothesis was never discharged for real frontier blocks (which can have width > 2, so `two_chain_cover_dim_le2` does NOT apply).
**Depends on:** `Dimension.DimDefs` (`PosetDimension`, `IsRealizer`, `IsLinearExtension`, `dimension_is_minimum`), `Schedule` (`desugar_rank`, `desugar_rank_form`, `op_at_desugar`), `Rank` (`hb_neq_rank_lt`, `rank_hb_le`, `rp_rank_mono`), `ScheduleWf` (`wf_schedule`, `op_for_send_iff`, `op_for_recv_iff`), `SyncShape` (`frontier_block`), `Ordinal` (`sub_order`), Stdlib `Operators_Properties` (`clos_rt_rt1n`).

## Goal

1. The **missing mathematical lemma**: a poset that is a disjoint union of chains has dim ≤ 2.
2. The **gap closer**: every frontier block of a (well-formed) schedule's execution is such a
   poset, so it has dim ≤ 2 *unconditionally* — discharging `fully_sync_dim_le2`'s per-block
   hypothesis without the unsatisfiable-for-width>2 `two_chain_cover_dim_le2`.

## Component 1 — generic `disjoint_chains_dim_le2` (`execution/DisjointChainsDim.v`)

A poset is a "disjoint union of chains" when there is a component label `comp : A -> nat` with:
- (H1) `R x y -> comp x = comp y` — `R` relates only within a component;
- (H2) `comp x = comp y -> R x y \/ R y x` — each component is a chain (totally ordered).

```coq
Lemma disjoint_chains_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (comp : A -> nat),
    (forall x y, R x y -> comp x = comp y) ->
    (forall x y, comp x = comp y -> R x y \/ R y x) ->
    forall d, PosetDimension R d -> d <= 2.
```
Proof: two explicit linear extensions (lexicographic on `(comp, R)`, with the component order
forward in `L1` and reversed in `L2`):
```coq
L1 x y := comp x < comp y \/ (comp x = comp y /\ R x y).
L2 x y := comp y < comp x \/ (comp x = comp y /\ R x y).
```
- `IsLinearExtension R L1`/`L2`: total (compare `comp`; on ties use the chain hypothesis H2),
  poset (refl/antisym/trans — lexicographic; antisym uses H1-derived same-comp + `poset_antisym`),
  extends `R` (H1: `R x y ⟹ comp x = comp y`, so `R x y ⟹ L1 x y` via the right branch).
- Intersection `R x y <-> L1 x y /\ L2 x y`: `→` by extends; `←` since `L1 ∧ L2` forces
  `comp x = comp y` (the strict branches contradict), leaving `R x y`.
- `IsRealizer R (fun L => L = L1 \/ L = L2)`; `cardinal ≤ 2`; `dimension_is_minimum Hdim … : d ≤ 2`.

No finiteness, no width, no `dimension_le_width`. (Cleaner and strictly more general than
`two_chain_cover_dim_le2`, which needed width ≤ 2.)

## Component 2 — frontier blocks are disjoint unions of chains (`DisjointChainsDim.v`)

Key structural lemma (rank-based): within one frontier, `hb` between two distinct events is a
single sender→receiver message.
```coq
Lemma hb_same_index_msg :
  forall s, wf_schedule s ->
  forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) = snd (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y -> x <> y ->
    (* x sends to y at this frontier *)
    List.In (fst (proj1_sig x), fst (proj1_sig y))
            (nth (snd (proj1_sig x)) (sch_frontiers s) []).
```
Proof: `desugar_rank_form` gives `rank e = 2·idx e + c`, `c ≤ 1` (`c = 1` iff the op is `Recv`).
With equal indices, `hb_neq_rank_lt` ⟹ `rank x < rank y` ⟹ `c_x = 0, c_y = 1` and
`rank y = rank x + 1`. Decompose `hb` left-to-right (`clos_rt_rt1n`): the first edge `x → z`
satisfies `rank x < rank z ≤ rank y = rank x + 1`, so `rank z = rank y`; then `rank_hb_le`
on `z → y` gives `rank z ≤ rank y` and the rank equality + the strict-rank-along-edges structure
forces `z = y`, i.e. `x → y` is a single `edge`. A single same-index `edge` is a message
(program edges raise the index), so `op_at p k = Send q _`, `op_at q k = Recv p _`; `op_at_desugar`
+ `op_for_send_iff` ⟹ `In (p,q) (nth k …)`.

Component label and the block lemma:
```coq
(* comp of an event in frontier-block k: a receiver maps to its sender, else to itself *)
Definition fb_comp (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  match op_at (desugar_prog s) (fst (proj1_sig x)) (snd (proj1_sig x)) with
  | Some (Recv src _) => src
  | _ => fst (proj1_sig x)
  end.

Lemma frontier_block_dim_le2 :
  forall s, wf_schedule s -> forall k, forall d,
    PosetDimension (sub_order (exec_of_schedule s) (frontier_block s k)) d -> d <= 2.
```
Proof: apply `disjoint_chains_dim_le2` to `sub_order … (frontier_block s k)` with
`comp := fun z => fb_comp s (proj1_sig z)` (lifted to the block subtype). Discharge H1 via
`hb_same_index_msg` (a comparable pair is a direct message s→r, and `fb_comp r = s = fb_comp s_send`);
H2 via: same `fb_comp` ⟹ both in one matched pair (or equal) ⟹ comparable (the message edge gives
`hb`, reflexivity otherwise), using `op_for_send_iff`/`op_for_recv_iff` under `wf_schedule`.

## Component 3 — corollary: per-block bound auto-discharged (`DisjointChainsDim.v`)

```coq
Corollary fully_sync_frontier_dim_le2 :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
    IsFullySync (exec_of_schedule s) (frontier_blocks s) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
```
Proof: `fully_sync_dim_le2` with the per-block obligation discharged by `frontier_block_dim_le2`
(each `blk ∈ frontier_blocks s` is `frontier_block s k` for some `k` via `in_map_iff`; obtain a
dimension witness via `fin_dim_exists`/`exec_dimension_exists` on the block then bound by
`frontier_block_dim_le2`). This removes the **unproven per-block hypothesis** of finding 2: for a
well-formed schedule, the frontier-block decomposition's per-block `dim ≤ 2` holds automatically.
(It still requires `IsFullySync` — finding 1's barrier — which is a *separate* limitation.)

## Component 4 — example (`execution/DisjointChainsDimExamples.v`, test-only)

A concrete frontier block of width > 2 (where `two_chain_cover_dim_le2` could not apply): a
3-process frontier with one message pair, e.g. schedule `{ nprocs := 3; frontiers := [[(0,1)]] }`,
block at index 0 = `{(0,0)→(1,0), (2,0) isolated}` (width 2 here; for width 3 use 3 procs no
message: `[[]]` over 3 procs → antichain of 3, width 3, dim 2). Show `frontier_block_dim_le2`
gives `dim ≤ 2`. Confirms the lemma applies where the width-≤2 route fails.

## Files, wiring, testing
- New: `execution/DisjointChainsDim.v` (exported), `execution/DisjointChainsDimExamples.v` (test).
- `execution/dune` + `_CoqProject`: add both. `execution/Execution.v`: export `DisjointChainsDim`.
- `docs/INDEX.md`: a subsection; note it closes review-finding 2.
- Whole-project green; **zero `Admitted`**; files <500 lines; each `Qed` <5 min.
- `Print Assumptions disjoint_chains_dim_le2 frontier_block_dim_le2` recorded (expect standard
  classical/proof-irrelevance only; the generic lemma should be axiom-light).

## Acceptance criteria
1. `disjoint_chains_dim_le2` (generic, no width/finiteness). Zero admits.
2. `hb_same_index_msg`, `fb_comp`, `frontier_block_dim_le2` (every frontier block of a wf schedule
   has dim ≤ 2). Zero admits.
3. `fully_sync_frontier_dim_le2` corollary. Concrete example. Whole-project green; INDEX updated.

## Out of scope / honestly noted
- Finding 1 (the `IsFullySync`/barrier unsatisfiability for N>4) is NOT addressed here — this
  closes only the per-block half (finding 2). `fully_sync_frontier_dim_le2` still assumes
  `IsFullySync`.
- `two_chain_cover_dim_le2` (Transformation B) is left as-is; `disjoint_chains_dim_le2` is the
  more appropriate lever and could later replace it, but TransformB is not refactored here.

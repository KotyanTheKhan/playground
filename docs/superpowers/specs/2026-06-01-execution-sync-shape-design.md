# Sync-Shape Operational Definitions + IsFullySync Bridge — Design

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** A (`Op` — `matched`, `op_at`; `Schedule` — `desugar_prog`, `op_for`, `op_for_tag`, `proc_len_desugar`, `nprocs_desugar`, `exec_of_schedule`), B (`FullySync` — `IsFullySync`, `union_upto`; `Ordinal` — `sub_order`, `no_alt_cycle`; `FullySyncDim2` — `fully_sync_dim_le2`; `Poset` — `ep_carrier`, `ep_order`).
**Paper:** NomaDB TechReport.

## Goal

Define "sync-shape" at the program (`Op`/`Program`) level, prove every frontier-model
program (`desugar s`) is sync-shaped, and prove the conditional bridge connecting the
program-level sync structure to the dimension-side `IsFullySync` machinery:
`FullySynchronizing s -> IsFullySync (exec_of_schedule s) (frontier_blocks s)`.

This gives the transformations a concrete, proven target ("sync-shaped") and links
program syntax to the poset/dimension toolkit, enabling dimension analysis of
fully-synchronizing schedules.

## Key finding (recorded)

The bridge is NOT unconditional. `IsFullySync` requires the index-`k` frontiers to be
barriers — every index-`<k` event `hb`-precedes every index-`≥k` event across ALL
processes. But `hb` only orders cross-process events through message chains; two
processes that never synchronize have concurrent events regardless of index, so their
frontiers are not barriers. Hence the `FullySynchronizing s` hypothesis: it asserts
exactly the cross-frontier ordering the barrier needs. It is a caller-discharged
hypothesis (concrete fully-synchronizing schedules satisfy it, provable case-by-case);
deriving it from a weaker per-frontier connectivity notion is a later refinement.

## Library facts this builds on (verified present)

- `Op`: `matched P p i q j t := op_at P p i = Some (Send q t) /\ op_at P q j = Some (Recv p t)`.
- `Schedule`: `op_for_tag : forall fr p k q t, (op_for fr p k = Send q t -> t = k) /\ (op_for fr p k = Recv q t -> t = k)`; `op_at_desugar`; `proc_len_desugar : forall s p, p < sch_nprocs s -> proc_len (desugar_prog s) p = length (sch_frontiers s)`; `nprocs_desugar`; `desugar_prog`, `exec_of_schedule s := exec_of (desugar s)`.
- `FullySync`: `IsFullySync E blocks` (4-conj: nonempty / cover / disjoint / prefix-barrier `forall k, 0 < k -> k < length blocks -> IsBarrier E (union_upto E blocks k) (fun x => ~ In (union_upto E blocks k) x)`); `union_upto E blocks k := fun x => exists i, i < k /\ In (nth i blocks (Empty_set _)) x`.
- `FullySyncDim2.fully_sync_dim_le2`; `Ordinal.sub_order`, `no_alt_cycle`; `Frontier.IsBarrier`.
- `ep_carrier (exec_of_schedule s)`, `ep_order`. Each event's `proj1_sig` is `(p,i)` with `i < proc_len = length (sch_frontiers s)`.

## Component 1 — program-level sync-shape (`execution/SyncShape.v`)

```coq
(* A matched message is synchronous when send and recv sit at the same local index. *)
Definition synchronous_message (P : Program) (p i q j : nat) (t : Tag) : Prop :=
  matched P p i q j t /\ i = j.

(* A program is sync-shaped: every matched send/recv pair is synchronous. *)
Definition sync_shaped (P : Program) : Prop :=
  forall p i q j t, matched P p i q j t -> i = j.

Lemma desugar_sync_shaped : forall s, sync_shaped (desugar_prog s).
```
Proof of `desugar_sync_shaped`: `intros s p i q j t [Hs Hr]` (`matched`); `Hs : op_at (desugar_prog s) p i = Some (Send q t)`, `Hr : op_at (desugar_prog s) q j = Some (Recv p t)`. By `op_at_desugar`, `op_at (desugar_prog s) p i = Some (op_for (nth i frontiers []) p i)`, so `op_for (nth i frontiers []) p i = Send q t`; `op_for_tag` ⟹ `t = i`. Similarly `op_for (nth j frontiers []) q j = Recv p t`; `op_for_tag` ⟹ `t = j`. So `i = t = j`. (Needs `p,i,q,j` in range so `op_at_desugar` applies — derive from `op_at … = Some …` being non-`None`.)

## Component 2 — frontier blocks + `FullySynchronizing` (`SyncShape.v`)

```coq
Definition frontier_block (s : Schedule) (k : nat)
  : Ensemble (ep_carrier (exec_of_schedule s)) :=
  fun x => snd (proj1_sig x) = k.

Definition frontier_blocks (s : Schedule)
  : list (Ensemble (ep_carrier (exec_of_schedule s))) :=
  map (frontier_block s) (seq 0 (length (sch_frontiers s))).

(* The cross-frontier ordering the barrier needs: every index-i event precedes
   every index-j>i event, across all processes. (The barrier condition lifted to
   the schedule; a caller-discharged hypothesis.) *)
Definition FullySynchronizing (s : Schedule) : Prop :=
  forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) < snd (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y.
```
(Phrasing `FullySynchronizing` over carrier events `x y` with `index x < index y`
avoids constructing events from raw `(p,i)` pairs and matches the barrier's `Hbelow`
shape directly.)

## Component 3 — the bridge (`SyncShape.v` or `SyncShapeBridge.v`)

```coq
Lemma fully_synchronizing_is_fully_sync :
  forall s, FullySynchronizing s ->
    (exists x : ep_carrier (exec_of_schedule s), True) ->   (* carrier inhabited; or per-frontier-nonempty *)
    IsFullySync (exec_of_schedule s) (frontier_blocks s).
```
Discharge `IsFullySync`'s four conjuncts:
1. **nonempty** — each `frontier_block s k` (for `k < #frontiers` = `length (frontier_blocks s)`) contains an event: any process `p < sch_nprocs s`'s index-`k` event (valid since `proc_len_desugar` gives length = #frontiers). (Requires `sch_nprocs s > 0`; derive from carrier inhabited, or add as a clause.)
2. **cover** — every event `x` has `snd (proj1_sig x) = i < #frontiers`, so `x ∈ nth i (frontier_blocks s) ∅`. `nth i (frontier_blocks s) ∅ = frontier_block s i` (via `nth_map` + `seq_nth`, `i < length (seq 0 #frontiers)`). Membership `snd (proj1_sig x) = i` holds by definition of the index.
3. **disjoint** — `i ≠ j`, `x ∈ frontier_block s i` (`snd = i`), `x ∈ frontier_block s j` (`snd = j`) ⟹ `i = j`, contradiction. (`nth … = frontier_block` rewrites.)
4. **prefix barrier** — for `0 < k < length (frontier_blocks s) = #frontiers`: `IsBarrier (exec_of_schedule s) (union_upto … k) (fun x => ~ In (union_upto … k) x)`. The 5 conjuncts:
   - cover/disjoint/inhabited — `union_upto … k` = events with index `< k` (via the `nth = frontier_block` rewrites: `In (nth i … ∅) x <-> snd (proj1_sig x) = i`); complement = index `≥ k`; every event is one or the other.
   - **`Hbelow`** (`forall x y, In (union_upto … k) x -> ~ In (union_upto … k) y -> ep_order E x y`): `x` has index `< k`, `y` has index `≥ k`, so `index x < index y`; `FullySynchronizing` gives `ep_order E x y`. **This consumes the hypothesis.**

The index bookkeeping (`nth (map (frontier_block s) (seq 0 n)) k ∅ = frontier_block s k`
for `k < n`; `union_upto (frontier_blocks s) k x <-> snd (proj1_sig x) < k`) is the bulk;
prove a helper `nth_frontier_blocks` and `union_upto_frontier_blocks` (small, like the
`nth_map_restrict` pattern). The substantive content is obligation 4's `Hbelow` =
`FullySynchronizing`.

## Component 4 — payoff corollary (`SyncShape.v`)

```coq
Corollary fully_synchronizing_dim2 :
  forall s, FullySynchronizing s ->
    (exists x : ep_carrier (exec_of_schedule s), True) ->
    (forall blk, List.In blk (frontier_blocks s) ->
       no_alt_cycle _ (sub_order (exec_of_schedule s) blk)) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
```
Proof: `fully_synchronizing_is_fully_sync` gives `IsFullySync … (frontier_blocks s)`;
`fully_sync_dim_le2` (from B) with the per-block `no_alt_cycle` hypothesis gives the
dim≤2 conclusion. (A fully-synchronizing schedule whose frontier blocks are each free
of alternating cycles has a dim≤2 execution — program structure → dimension bound.)

NOTE on `no_alt_cycle` weakness: per the recorded caution, `no_alt_cycle` is stronger
than dim≤2, so this corollary is the honest composition with `fully_sync_dim_le2`. (A
`fully_sync_dimension`-based exact variant could be added but needs per-block `dims`;
the dim≤2 corollary is the natural payoff for this slice.)

## Component 5 — concrete instance (`execution/SyncShapeExamples.v`, test-only)

```coq
Definition s_demo : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [(1,0)] ] |}.

Example s_demo_sync_shaped : sync_shaped (desugar_prog s_demo).
Example s_demo_fully_synchronizing : FullySynchronizing s_demo.
Example s_demo_is_fully_sync :
  IsFullySync (exec_of_schedule s_demo) (frontier_blocks s_demo).
```
- `s_demo_sync_shaped` := `desugar_sync_shaped s_demo`.
- `s_demo_fully_synchronizing`: `s_demo` has 4 events `(0,0),(1,0),(0,1),(1,1)`;
  frontier 0 = `[(0,1)]` (proc0 sends to proc1), frontier 1 = `[(1,0)]` (proc1 sends to
  proc0). `intros x y Hlt` (`index x < index y` ⟹ `index x = 0, index y = 1`). By
  `valid_event`-style case analysis, show `ep_order` from index-0 to index-1 events via
  the message/program `edge`s (`rt_step`/`rt_trans`). (Reuse the concrete-event +
  `vm_compute`-`op_at` techniques from `Examples.v`/`DimExamples.v`.)
- `s_demo_is_fully_sync` := `fully_synchronizing_is_fully_sync s_demo s_demo_fully_synchronizing <inhabited>`.

(If the `s_demo_fully_synchronizing` event-ordering proof is heavy, it is the genuine
end-to-end validation and worth the effort; no cheaper fallback that exercises the
bridge.)

## Files, wiring, testing

- New: `execution/SyncShape.v` (+ optional `execution/SyncShapeBridge.v` if >500 lines),
  `execution/SyncShapeExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the new modules.
- `execution/Execution.v`: export `SyncShape` (+ bridge file); NOT the examples.
- `docs/INDEX.md`: add a "Sync-shape" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero
  `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `desugar_sync_shaped`, `fully_synchronizing_is_fully_sync`,
  the example — expected only standard classical/choice axioms; recorded.

## Acceptance criteria

1. `SyncShape.v`: `synchronous_message`, `sync_shaped`, `desugar_sync_shaped`,
   `frontier_block`, `frontier_blocks`, `FullySynchronizing`,
   `fully_synchronizing_is_fully_sync`, `fully_synchronizing_dim2`. Zero admits.
2. `SyncShapeExamples.v`: `s_demo_sync_shaped`, `s_demo_fully_synchronizing`,
   `s_demo_is_fully_sync`. Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope

The connectivity ⟹ `FullySynchronizing` derivation (per-frontier spanning-tree); the
exact-dimension payoff variant; Transformation B; `desugar_wf` (separate deferred
task #12); the full reduce-to-sync-shape pipeline.

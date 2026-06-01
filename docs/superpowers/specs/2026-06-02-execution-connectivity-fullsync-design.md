# connectivity ⟹ FullySynchronizing — Design

**Date:** 2026-06-02
**Branch:** `execution_poset`
**Depends on:** `execution/SyncShape.v` (`FullySynchronizing`, `frontier_block(s)`, `event_at_index`, `event_index_lt`, `fully_synchronizing_dim2`), `execution/ScheduleWf.v` (`wf_schedule`, `wf_frontier`, `op_for_send_iff`, `op_for_recv_iff`, `op_at_desugar_inv`), `execution/Schedule.v` (`desugar`, `op_at_desugar`, `proc_len_desugar`, `nprocs_desugar`), `execution/Edges.v` (`edge`, `hb`).

## Goal

Replace the caller-discharged `FullySynchronizing` hypothesis with a derivation from a
concrete **per-transition connectivity** predicate over the schedule's sync pairs, so that
`fully_synchronizing_dim2` becomes usable from a graph condition rather than an assumed
barrier order.

## Key structural fact (shapes the design)

In the desugared program, **message edges are intra-frontier**: a sync pair `(p,q) ∈
frontier k` yields the edge `(p,k) → (q,k)` (same index `k`); program-order edges step
`(p,k) → (p, k+1)`. A `hb`-path has non-decreasing index, so a path from index `k` to index
`k+1` may only use frontiers `k` and `k+1`. Each frontier is a partial matching (`wf_frontier`),
so it contributes at most one directed hop per process. Therefore the **consecutive** barrier
`(p,k) hb (q,k+1)` for arbitrary `p,q` is the crux, and a fully-general "connectivity" must be
a concrete *witness* predicate over the sync pairs — not a vacuous restatement of `hb`.

## Architecture — two halves

### Half 1 — the reduction (general, `execution/ConnSync.v`)

`StepBarrier s := forall x y : ep_carrier (exec_of_schedule s),
   snd (proj1_sig y) = S (snd (proj1_sig x)) -> ep_order (exec_of_schedule s) x y`
(every event precedes every event one index higher).

```coq
Lemma step_barrier_implies_fullsync :
  forall s, 0 < sch_nprocs s -> StepBarrier s -> FullySynchronizing s.
```
Proof: auxiliary `forall d x y, snd(proj1 y) = snd(proj1 x) + S d -> ep_order … x y` by
induction on `d`. `d=0` is `StepBarrier`. `d=S d'`: let `k = snd(proj1 x) + S d'`
(`= snd(proj1 y) - 1`); `k < length frontiers` (since `snd(proj1 y) < len` by
`event_index_lt`), so `event_at_index s Hnp k` gives an intermediate `z` with `snd(proj1 z)=k`;
`hb x z` by IH (gap `d'`), `hb z y` by `StepBarrier`, combine by `hb_trans`. `FullySynchronizing`
then follows: `snd x < snd y ⟹ ∃ d, snd y = snd x + S d`, apply the auxiliary.

### Half 2 — connectivity ⟹ StepBarrier (`execution/ConnSync.v`)

**Event constructor + the two edge lemmas** (reusing `ScheduleWf`):
```coq
Definition mk_event (s : Schedule) (p k : nat)
  (Hp : p < sch_nprocs s) (Hk : k < length (sch_frontiers s))
  : ep_carrier (exec_of_schedule s).   (* via the Valid proof, like event_at_index *)

Lemma event_eq_of_proj :              (* generic subtype eq via proof_irrelevance *)
  forall s (x y : ep_carrier (exec_of_schedule s)), proj1_sig x = proj1_sig y -> x = y.

Lemma prog_step :                     (* program-order edge (p,k) -> (p, S k) *)
  forall s p k (Hp : p < sch_nprocs s) (HSk : S k < length (sch_frontiers s)),
    ep_order (exec_of_schedule s) (mk_event s p k Hp (lt_trans …)) (mk_event s p (S k) Hp HSk).

Lemma msg_step :                      (* message edge (p,k) -> (q,k) from a sync pair *)
  forall s, wf_schedule s -> forall p q k
    (Hp : p < sch_nprocs s) (Hq : q < sch_nprocs s) (Hk : k < length (sch_frontiers s)),
    List.In (p, q) (nth k (sch_frontiers s) []) ->
    ep_order (exec_of_schedule s) (mk_event s p k Hp Hk) (mk_event s q k Hq Hk).
```
`msg_step` builds the `edge` message disjunct with `t := k`: `op_at (desugar s) p k =
Some (Send q k)` from `op_at_desugar` + `op_for_send_iff` (backward, needs `wf_frontier (nth k …)`
from `wf_schedule` + `nth_In`), and `op_at … q k = Some (Recv p k)` from `op_for_recv_iff`.

**The connectivity predicate** (a concrete 4-case witness per ordered process pair per transition):
```coq
Definition step_witness (s : Schedule) (k p q : nat) : Prop :=
  p = q
  \/ List.In (p, q) (nth k (sch_frontiers s) [])
  \/ List.In (p, q) (nth (S k) (sch_frontiers s) [])
  \/ (exists r, r < sch_nprocs s /\
        List.In (p, r) (nth k (sch_frontiers s) []) /\
        List.In (r, q) (nth (S k) (sch_frontiers s) [])).

Definition StepConnected (s : Schedule) : Prop :=
  forall k, S k < length (sch_frontiers s) ->
  forall p q, p < sch_nprocs s -> q < sch_nprocs s -> step_witness s k p q.
```
Each witness case yields `hb (p,k) (q,k+1)` by composing `prog_step`/`msg_step`:
- `p=q`: `prog_step`.
- `(p,q)∈frontier k`: `msg_step` then `prog_step`.
- `(p,q)∈frontier (S k)`: `prog_step` then `msg_step`.
- witness `r`: `msg_step` (k) → `prog_step` → `msg_step` (S k).

```coq
Lemma step_connected_implies_step_barrier :
  forall s, wf_schedule s -> StepConnected s -> StepBarrier s.
Lemma step_connected_fully_synchronizing :
  forall s, wf_schedule s -> 0 < sch_nprocs s -> StepConnected s -> FullySynchronizing s.
```
`step_connected_implies_step_barrier`: for `x,y` with `snd(proj1 y) = S (snd(proj1 x))`, set
`k = snd(proj1 x)`, `p = fst(proj1 x)`, `q = fst(proj1 y)`; validity gives `p,q < nprocs`,
`k < len`, `S k < len`; rewrite `x = mk_event s p k …`, `y = mk_event s q (S k) …` via
`event_eq_of_proj`; apply `StepConnected` and discharge the witness with the four edge-path
compositions. The combined corollary chains Half 1.

### Payoff corollary
```coq
Corollary step_connected_dim2 :
  forall s, wf_schedule s -> 0 < sch_nprocs s -> StepConnected s ->
    (forall blk, List.In blk (frontier_blocks s) ->
       exists d, inhabited (PosetDimension (sub_order (exec_of_schedule s) blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
```
(= `fully_synchronizing_dim2` precomposed with `step_connected_fully_synchronizing` — now the
top-level barrier hypothesis is the concrete `wf_schedule ∧ StepConnected`.)

## Honest scope note

`StepConnected` is *satisfiable* only when the per-transition sync structure actually provides
the witnesses — for partial-matching frontiers that bounds the synchronized process count per
single transition (≈ ≤4), exactly as the intra-frontier structure forces. The **lemmas**
(`StepConnected ⟹ FullySynchronizing`) hold in full generality and are the deliverable; the
predicate honestly captures what connectivity must supply. (A multi-frontier "thick barrier"
generalization — synchronizing many processes across several frontiers between logical
barriers — is a possible later refinement, out of scope here.)

## Example (`execution/ConnSyncExamples.v`, test-only)
`s_demo` (nprocs 2, frontiers `[[(0,1)];[(1,0)]]`): prove `wf_schedule s_demo` and
`StepConnected s_demo` (the single transition `k=0`: pairs `(0,1)` via case-2 on frontier 0;
`(1,0)` via case-3 on frontier 1; diagonal via case-1), then derive `FullySynchronizing s_demo`
through `step_connected_fully_synchronizing` — cross-checking the existing hand proof
`s_demo_fully_synchronizing`.

## Files, wiring, testing
- New: `execution/ConnSync.v` (exported), `execution/ConnSyncExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add both. `execution/Execution.v`: export `ConnSync`.
- `docs/INDEX.md`: a `ConnSync.v` subsection.
- Whole-project green; **zero `Admitted`**; files <500 lines; each `Qed` <5 min.
- `Print Assumptions step_connected_fully_synchronizing` recorded (expected: the standard
  classical/proof-irrelevance axioms already in the execution layer; no `admit`).

## Acceptance criteria
1. `ConnSync.v`: `StepBarrier`, `step_barrier_implies_fullsync`, `mk_event`, `prog_step`,
   `msg_step`, `step_witness`, `StepConnected`, `step_connected_implies_step_barrier`,
   `step_connected_fully_synchronizing`, `step_connected_dim2`. Zero admits.
2. `ConnSyncExamples.v`: `wf_schedule s_demo`, `StepConnected s_demo`,
   `s_demo_fully_synchronizing_via_conn`. Zero admits.
3. Whole-project green; `Execution.v` exports `ConnSync`; INDEX updated; assumptions recorded.

## Out of scope
Transformation B; the multi-frontier thick-barrier generalization; weakening `wf_schedule`.

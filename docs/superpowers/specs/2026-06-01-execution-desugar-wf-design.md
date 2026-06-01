# `desugar_wf` — well-formedness of desugaring (core-model deferred lemma)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** `execution/Op.v` (`wf_program`, `op_at`, `matched`), `execution/Schedule.v` (`Schedule`, `Frontier`, `op_for`, `desugar_prog`, `desugar`, `op_for_tag`, `op_at_desugar`, `proc_len_desugar`, `nprocs_desugar`).
**Closes:** deferred task #12 (the core-model plan `Admitted` `wf_schedule`/`desugar_wf` and left the proof to a later slice).

## Goal

Prove `desugar_wf : forall s, wf_schedule s -> wf_program (desugar s)` — desugaring a
well-formed schedule yields a well-formed program (every send target / recv source in range,
and every send/recv uniquely matched).

## Design decision: `wf_schedule` must be STRENGTHENED

The core-model plan's `wf_schedule` only required endpoints in range
(`fst pq < n /\ snd pq < n`). **Under that definition `desugar_wf` is FALSE.**
Counterexample: a frontier `[(0,1);(0,2)]` with `sch_nprocs = 3` has all endpoints in
range, but `op_for` resolves process `0` via `find (fst = 0)` to the FIRST pair only —
`op_for [(0,1);(0,2)] 0 k = Send 1 k`. Process `2` resolves to `Recv 0 k`, a receive whose
matching send (`Send 2` at process `0`) does not exist. So `wf_recv_matched` fails.

The matching obligations force each frontier to be a **partial matching** — every process
participates at most once, in at most one role:

```coq
Definition wf_frontier (n : nat) (fr : Frontier) : Prop :=
  (forall a b, In (a, b) fr -> a < n /\ b < n /\ a <> b) /\
  NoDup (flat_map (fun pq => [fst pq; snd pq]) fr).

Definition wf_schedule (s : Schedule) : Prop :=
  forall fr, In fr (sch_frontiers s) -> wf_frontier (sch_nprocs s) fr.
```

The `NoDup (flat_map endpoints fr)` clause says: across the whole frontier, no process
appears twice — neither as two senders, two receivers, nor as both a sender and a receiver.
(`a <> b` is implied by `NoDup` but kept explicit for the in-range proof.) This is exactly
the "rendezvous matching" the sync-shape model already assumes operationally; we now name it.

## Key characterization (the engine)

Under `wf_frontier n fr`, `find` is canonical and `op_for` is fully determined by membership:

```coq
Lemma find_fst_unique : NoDup (flat_map endpoints fr) -> In (p,q) fr ->
                        find (fun pq => Nat.eqb (fst pq) p) fr = Some (p, q).
Lemma find_snd_unique : NoDup (flat_map endpoints fr) -> In (p,q) fr ->
                        find (fun pq => Nat.eqb (snd pq) q) fr = Some (p, q).
Lemma no_fst_of_recv  : NoDup (flat_map endpoints fr) -> In (s,p) fr ->
                        find (fun pq => Nat.eqb (fst pq) p) fr = None.
Lemma op_for_send_iff : wf_frontier n fr -> (op_for fr p k = Send q k <-> In (p, q) fr).
Lemma op_for_recv_iff : wf_frontier n fr -> (op_for fr p k = Recv s k <-> In (s, p) fr).
```

Forward directions (`op_for = … -> In …`) use only `find_some`; backward directions
(`In … -> op_for = …`) use the `NoDup` uniqueness. `op_for_tag` (already in Schedule.v)
fixes every Send/Recv tag to the frontier index `k`.

## Inverse range lemma

To discharge the uniqueness obligations we need: a `Some` from `op_at (desugar_prog s)`
implies in-range and reads back as `op_for`:

```coq
Lemma op_at_desugar_inv : forall s p i o,
  op_at (desugar_prog s) p i = Some o ->
  p < sch_nprocs s /\ i < length (sch_frontiers s) /\
  o = op_for (nth i (sch_frontiers s) []) p i.
```
(Out of range, `op_at` is `None`; in range it equals `op_at_desugar`.)

## The four `wf_program` fields

Let `S := length (sch_frontiers s)`. For each, `op_at (desugar_prog s) p i = Some o` gives
`p < nprocs`, `i < S`, `o = op_for fr_i p i` via `op_at_desugar_inv`, and `nprocs (desugar) =
sch_nprocs` via `nprocs_desugar`.

1. **`wf_send_targets`** — `op_at … p i = Some (Send q t)` ⟹ `In (p,q) fr_i` (by
   `op_for_tag` `t = i`, then `op_for_send_iff` fwd) ⟹ `q < sch_nprocs` (range clause) ⟹
   `q < nprocs (desugar)`.
2. **`wf_recv_sources`** — symmetric, `op_for_recv_iff` fwd ⟹ `In (p, q) fr_j` ⟹ `p < n`.
3. **`wf_recv_matched`** — `op_at … q j = Some (Recv p t)` ⟹ `t = j`, `In (p,q) fr_j`.
   - *Existence* `i = j`: `op_for_send_iff` bwd ⟹ `op_for fr_j p j = Send q j` ⟹
     `op_at (desugar) p j = Some (Send q j)` (via `op_at_desugar`, `p<n` from range, `j<S`).
   - *Uniqueness*: any `i` with `op_at … p i = Some (Send q j)` ⟹ (`op_at_desugar_inv`)
     `op_for fr_i p i = Send q j` ⟹ (`op_for_tag`) `j = i`.
4. **`wf_send_matched`** — symmetric: `Send q t` at `(p,i)` ⟹ `t = i`, `In (p,q) fr_i` ⟹
   `op_for fr_i q i = Recv p i` (`op_for_recv_iff` bwd) ⟹ existence `j = i`; uniqueness by
   `op_for_tag`.

## Files & wiring

- New: `execution/ScheduleWf.v` (defs + helpers + `desugar_wf`). Keeps `Schedule.v` stable.
- New (test): `execution/ScheduleWfExamples.v` — `wf_schedule sched_n3`, `wf_schedule s_demo`,
  `wf_schedule sched_m45` (single-pair frontiers, distinct in-range endpoints) and the derived
  `wf_program (desugar sched_n3)`.
- `execution/Execution.v`: export `ScheduleWf` (not the examples).
- `execution/dune` + `_CoqProject`: add the two modules.
- `docs/INDEX.md`: add a `ScheduleWf.v` subsection.
- Whole-project green; **zero `Admitted`**; files <500 lines; each `Qed` <5 min.
- `Print Assumptions desugar_wf` recorded — expected axiom-free (pure structural).

## Out of scope

Transformation B; connectivity ⟹ FullySynchronizing; the `E_min` exact dim cross-check (#66).

## Acceptance criteria

1. `ScheduleWf.v`: `wf_frontier`, `wf_schedule`, the `find`/`op_for` characterization
   lemmas, `op_at_desugar_inv`, and `desugar_wf`. Zero admits.
2. `ScheduleWfExamples.v`: the three `wf_schedule` witnesses + one `wf_program (desugar …)`.
   Zero admits.
3. Whole-project green; `Execution.v` exports `ScheduleWf`; INDEX updated; `Print Assumptions`
   recorded.

# connectivity ⟹ FullySynchronizing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development.

**Goal:** Derive `FullySynchronizing` from a concrete per-transition connectivity predicate `StepConnected` over the schedule's sync pairs, removing the caller-discharged barrier hypothesis.

**Architecture:** `execution/ConnSync.v` — event constructor + two edge lemmas (reusing `ScheduleWf`), the `StepBarrier ⟹ FullySynchronizing` reduction (gap induction), and `StepConnected ⟹ StepBarrier ⟹ FullySynchronizing` + a dim≤2 corollary. `execution/ConnSyncExamples.v` — `s_demo` via the new path. Builds via the wrapper.

**Tech Stack:** Rocq 9.1; `Edges` (`edge`/`hb`/`hb_trans`), `Schedule` (`desugar`/`op_at_desugar`/`proc_len_desugar`/`nprocs_desugar`), `ScheduleWf` (`wf_schedule`/`wf_frontier`/`op_for_send_iff`/`op_for_recv_iff`), `SyncShape` (`FullySynchronizing`/`event_at_index`/`event_index_lt`/`frontier_blocks`/`fully_synchronizing_dim2`).

---

## Task CS0: Scaffold
**Files:** create `execution/ConnSync.v`, `execution/ConnSyncExamples.v`; modify `execution/dune`, `_CoqProject`.
- [ ] **Step 1: `execution/ConnSync.v`**
```coq
(* connectivity => FullySynchronizing: per-transition sync-pair witnesses
   discharge the barrier ordering. *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical
                           Relation_Operators ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Frontier
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.
```
- [ ] **Step 2: `execution/ConnSyncExamples.v`**
```coq
(* s_demo is FullySynchronizing via connectivity (test-only). *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape ConnSync.
Import ListNotations.
```
- [ ] **Step 3/4:** add `ConnSync`, `ConnSyncExamples` to `execution/dune` and `_CoqProject`.
- [ ] **Step 5: build** `bash .claude/scripts/timed-build.sh 120 execution/ConnSyncExamples.vo 2` → EXIT=0.
- [ ] **Step 6: commit** `git add -A && git commit -m "chore(execution): scaffold ConnSync modules"`.

---

## Task CS1: event constructor + edge lemmas (`ConnSync.v`)
Append. These reuse `ScheduleWf`'s `op_for` characterization. Model `mk_event` on `SyncShape.event_at_index` (lines 142-155).

```coq
Definition mk_event (s : Schedule) (p k : nat)
  (Hp : p < sch_nprocs s) (Hk : k < length (sch_frontiers s))
  : ep_carrier (exec_of_schedule s).
Proof.
  refine (exist _ (p, k) _).
  unfold Ensembles.In, ValidSet, Valid. simpl. split.
  - change (p < nprocs (desugar_prog s)). rewrite nprocs_desugar. exact Hp.
  - change (k < proc_len (desugar_prog s) p). rewrite (proc_len_desugar s p Hp). exact Hk.
Defined.

Lemma mk_event_proj : forall s p k Hp Hk, proj1_sig (mk_event s p k Hp Hk) = (p, k).
Proof. intros. reflexivity. Qed.

Lemma event_eq_of_proj :
  forall s (x y : ep_carrier (exec_of_schedule s)),
    proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros s [px Hpx] [py Hpy] Heq. simpl in Heq. subst py. f_equal. apply proof_irrelevance.
Qed.

(* program-order edge (p,k) -> (p, S k) *)
Lemma prog_step :
  forall s p k (Hp : p < sch_nprocs s)
         (Hk : k < length (sch_frontiers s)) (HSk : S k < length (sch_frontiers s)),
    ep_order (exec_of_schedule s) (mk_event s p k Hp Hk) (mk_event s p (S k) Hp HSk).
Proof.
  intros s p k Hp Hk HSk.
  unfold ep_order, exec_of_schedule, exec_of. simpl. apply rt_step.
  unfold edge. simpl. left. split; reflexivity.
Qed.

(* message edge (p,k) -> (q,k) from a sync pair, under wf_schedule *)
Lemma msg_step :
  forall s, wf_schedule s -> forall p q k
    (Hp : p < sch_nprocs s) (Hq : q < sch_nprocs s) (Hk : k < length (sch_frontiers s)),
    List.In (p, q) (nth k (sch_frontiers s) []) ->
    ep_order (exec_of_schedule s) (mk_event s p k Hp Hk) (mk_event s q k Hq Hk).
Proof.
  intros s Hwf p q k Hp Hq Hk Hin.
  assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
    by (apply Hwf; apply nth_In; exact Hk).
  unfold ep_order, exec_of_schedule, exec_of. simpl. apply rt_step.
  unfold edge. simpl. right. exists k. split.
  - change (op_at (desugar_prog s) p k = Some (Send q k)).
    rewrite (op_at_desugar s p k Hp Hk). f_equal.
    exact (proj2 (op_for_send_iff (sch_nprocs s) (nth k (sch_frontiers s) []) p q k Hfr) Hin).
  - change (op_at (desugar_prog s) q k = Some (Recv p k)).
    rewrite (op_at_desugar s q k Hq Hk). f_equal.
    exact (proj2 (op_for_recv_iff (sch_nprocs s) (nth k (sch_frontiers s) []) p q k Hfr) Hin).
Qed.
```
NOTES: `mk_event`'s `change`/`rewrite` exactly mirror `event_at_index`; if `change (p < nprocs (desugar_prog s))` fails, copy `event_at_index`'s precise unfolding. In `prog_step`/`msg_step`, after `unfold ep_order, exec_of_schedule, exec_of; simpl`, the goal's `edge` operates on `desugar s` (coerced to its `rp_prog = desugar_prog s`); the `change (op_at (desugar_prog s) …)` bridges the coercion (confirmed convertible in `ScheduleWf`/`Schedule`). `op_for_send_iff`/`op_for_recv_iff` are exactly as in `ScheduleWf.v`; `op_for_recv_iff … p q k` gives `op_for (nth k) q k = Recv p k <-> In (p,q) (nth k)` (the receiver is `q`, sender `p`). If `simpl` over-reduces `proj1_sig (mk_event …)`, use `cbn` or `vm_compute`-free `change`.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 240 execution/ConnSync.vo 2` → EXIT=0.
- [ ] **Commit** `git add execution/ConnSync.v && git commit -m "feat(execution): mk_event + program/message edge lemmas"`.

---

## Task CS2: the reduction (`ConnSync.v`)
Append.
```coq
Definition StepBarrier (s : Schedule) : Prop :=
  forall x y : ep_carrier (exec_of_schedule s),
    snd (proj1_sig y) = S (snd (proj1_sig x)) ->
    ep_order (exec_of_schedule s) x y.

Lemma step_barrier_gap :
  forall s, 0 < sch_nprocs s -> StepBarrier s ->
    forall d (x y : ep_carrier (exec_of_schedule s)),
      snd (proj1_sig y) = snd (proj1_sig x) + S d ->
      ep_order (exec_of_schedule s) x y.
Proof.
  intros s Hnp HSB d. induction d as [|d' IH]; intros x y Hgap.
  - apply HSB. rewrite Hgap. lia.
  - assert (Hk : snd (proj1_sig x) + S d' < length (sch_frontiers s)).
    { pose proof (event_index_lt s y) as Hy. lia. }
    destruct (event_at_index s Hnp (snd (proj1_sig x) + S d') Hk) as [z Hz].
    apply (hb_trans (desugar s) x z y).
    + apply IH. rewrite Hz. reflexivity.
    + apply HSB. lia.
Qed.

Lemma step_barrier_implies_fullsync :
  forall s, 0 < sch_nprocs s -> StepBarrier s -> FullySynchronizing s.
Proof.
  intros s Hnp HSB. unfold FullySynchronizing. intros x y Hlt.
  apply (step_barrier_gap s Hnp HSB (snd (proj1_sig y) - S (snd (proj1_sig x)))).
  lia.
Qed.
```
NOTES: `ep_order (exec_of_schedule s) = hb (desugar s)` definitionally (see `schedule_program_agree`, proved by `reflexivity`), so `hb_trans (desugar s) x z y` applies directly; if Coq rejects the unification, `unfold ep_order, exec_of_schedule, exec_of` first, or use `poset_trans` from `hb_IsPoset`. In `step_barrier_gap` the `lia` for the `HSB`/`IH` index obligations uses `Hgap`, `Hz` (rewrite them first if `lia` can't see them: `rewrite Hgap` / `rewrite Hz` then `lia`). `event_index_lt s y : snd (proj1_sig y) < length (sch_frontiers s)`.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 240 execution/ConnSync.vo 2` → EXIT=0.
- [ ] **Commit** `git add execution/ConnSync.v && git commit -m "feat(execution): StepBarrier => FullySynchronizing reduction (gap induction)"`.

---

## Task CS3: connectivity predicate + main theorem (`ConnSync.v`)
Append.
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

(* one transition: a witness yields hb between events with the given projections *)
Lemma barrier_step :
  forall s, wf_schedule s -> forall p q k,
    p < sch_nprocs s -> q < sch_nprocs s -> S k < length (sch_frontiers s) ->
    step_witness s k p q ->
    forall (x y : ep_carrier (exec_of_schedule s)),
      proj1_sig x = (p, k) -> proj1_sig y = (q, S k) ->
      ep_order (exec_of_schedule s) x y.
Proof.
  intros s Hwf p q k Hp Hq HSk Hw x y Hx Hy.
  assert (Hk : k < length (sch_frontiers s)) by lia.
  (* canonicalize x, y *)
  assert (Hxe : x = mk_event s p k Hp Hk) by (apply event_eq_of_proj; rewrite Hx; reflexivity).
  assert (Hye : y = mk_event s q (S k) Hq HSk) by (apply event_eq_of_proj; rewrite Hy; reflexivity).
  rewrite Hxe, Hye.
  destruct Hw as [Heq | [Hk_pq | [HSk_pq | [r [Hr [Hpr Hrq]]]]]].
  - (* p = q : program step *)
    subst q.
    (* mk_event s p (S k) Hq HSk = mk_event s p (S k) Hp HSk by proof irrelevance *)
    replace (mk_event s p (S k) Hq HSk) with (mk_event s p (S k) Hp HSk)
      by (apply event_eq_of_proj; reflexivity).
    apply (prog_step s p k Hp Hk HSk).
  - (* (p,q) in frontier k : msg (k) then prog *)
    apply (hb_trans (desugar s) _ (mk_event s q k Hq Hk) _).
    + apply (msg_step s Hwf p q k Hp Hq Hk Hk_pq).
    + apply (prog_step s q k Hq Hk HSk).
  - (* (p,q) in frontier (S k) : prog then msg (S k) *)
    apply (hb_trans (desugar s) _ (mk_event s p (S k) Hp HSk) _).
    + apply (prog_step s p k Hp Hk HSk).
    + apply (msg_step s Hwf p q (S k) Hp Hq HSk HSk_pq).
  - (* witness r : msg(k) -> prog -> msg(S k) *)
    apply (hb_trans (desugar s) _ (mk_event s r k Hr Hk) _).
    + apply (msg_step s Hwf p r k Hp Hr Hk Hpr).
    + apply (hb_trans (desugar s) _ (mk_event s r (S k) Hr HSk) _).
      * apply (prog_step s r k Hr Hk HSk).
      * apply (msg_step s Hwf r q (S k) Hr Hq HSk Hrq).
Qed.

Lemma step_connected_implies_step_barrier :
  forall s, wf_schedule s -> StepConnected s -> StepBarrier s.
Proof.
  intros s Hwf HSC. unfold StepBarrier. intros x y Hgap.
  pose proof (proj2_sig x) as Hvx. pose proof (proj2_sig y) as Hvy.
  unfold Ensembles.In, ValidSet, Valid in Hvx, Hvy.
  destruct Hvx as [Hpx _]. destruct Hvy as [Hqy _].
  set (p := fst (proj1_sig x)). set (q := fst (proj1_sig y)). set (k := snd (proj1_sig x)).
  assert (Hp : p < sch_nprocs s) by (unfold p; rewrite <- nprocs_desugar; exact Hpx).
  assert (Hq : q < sch_nprocs s) by (unfold q; rewrite <- nprocs_desugar; exact Hqy).
  assert (HSk : S k < length (sch_frontiers s)).
  { pose proof (event_index_lt s y) as H. unfold k. lia. }
  assert (Hxproj : proj1_sig x = (p, k)) by (unfold p, k; symmetry; apply surjective_pairing).
  assert (Hyproj : proj1_sig y = (q, S k)).
  { unfold q. rewrite (surjective_pairing (proj1_sig y)). rewrite Hgap. reflexivity. }
  apply (barrier_step s Hwf p q k Hp Hq HSk (HSC k HSk p q Hp Hq) x y Hxproj Hyproj).
Qed.

Lemma step_connected_fully_synchronizing :
  forall s, wf_schedule s -> 0 < sch_nprocs s -> StepConnected s -> FullySynchronizing s.
Proof.
  intros s Hwf Hnp HSC.
  apply (step_barrier_implies_fullsync s Hnp).
  apply (step_connected_implies_step_barrier s Hwf HSC).
Qed.

Corollary step_connected_dim2 :
  forall s, wf_schedule s -> 0 < sch_nprocs s -> StepConnected s ->
    (forall blk, List.In blk (frontier_blocks s) ->
       exists d, inhabited (PosetDimension (sub_order (exec_of_schedule s) blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
Proof.
  intros s Hwf Hnp HSC Hblocks.
  apply (fully_synchronizing_dim2 s
           (step_connected_fully_synchronizing s Hwf Hnp HSC) Hnp Hblocks).
Qed.
```
NOTES: the `Hgap : snd (proj1_sig y) = S (snd (proj1_sig x))` makes `Hyproj` hold (`snd (proj1_sig y) = S k`). `surjective_pairing : p = (fst p, snd p)`. The `replace … by (apply event_eq_of_proj; reflexivity)` discharges proof-irrelevant `mk_event` proof-arg mismatches; if `replace` is awkward, `rewrite (event_eq_of_proj s (mk_event … Hq HSk) (mk_event … Hp HSk) eq_refl)`. The `hb_trans (desugar s)` calls rely on `ep_order (exec_of_schedule s) = hb (desugar s)` definitionally; unfold if needed.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 300 execution/ConnSync.vo 2` → EXIT=0.
- [ ] **Commit** `git add execution/ConnSync.v && git commit -m "feat(execution): StepConnected => FullySynchronizing + dim2 corollary"`.

---

## Task CS4: example + wiring + audit
**Files:** `execution/ConnSyncExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.
- [ ] **Step 1: `s_demo` via connectivity** (append to ConnSyncExamples.v)
```coq
Definition s_demo : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [(1,0)] ] |}.

Lemma wf_frontier_pair : forall n a b, a < n -> b < n -> a <> b -> wf_frontier n [(a,b)].
Proof.
  intros n a b Ha Hb Hab. unfold wf_frontier, endpoints. split.
  - intros x y [Heq|[]]. injection Heq as <- <-. repeat split; assumption.
  - simpl. constructor.
    + simpl. intros [H|[]]. apply Hab. symmetry. exact H.
    + constructor; [ simpl; intros [] | constructor ].
Qed.

Lemma wf_s_demo : wf_schedule s_demo.
Proof.
  unfold wf_schedule, s_demo. simpl. intros fr Hin.
  destruct Hin as [<- | [<- | []]]; apply wf_frontier_pair; lia.
Qed.

Lemma step_connected_s_demo : StepConnected s_demo.
Proof.
  unfold StepConnected, s_demo. simpl. intros k HSk p q Hp Hq.
  (* only k = 0 (since S k < 2) *)
  assert (k = 0) by lia. subst k.
  (* p,q in {0,1} *)
  assert (p = 0 \/ p = 1) by lia. assert (q = 0 \/ q = 1) by lia.
  unfold step_witness. simpl.
  (* case-split: (0,0),(1,1) -> p=q; (0,1) -> In frontier 0; (1,0) -> In frontier 1 *)
  destruct H as [->|->]; destruct H0 as [->|->].
  - left. reflexivity.
  - right. left. left. reflexivity.            (* (0,1) in frontier 0 = [(0,1)] *)
  - right. right. left. left. reflexivity.     (* (1,0) in frontier 1 = [(1,0)] *)
  - left. reflexivity.
Qed.

Example s_demo_fully_synchronizing_via_conn : FullySynchronizing s_demo.
Proof.
  apply (step_connected_fully_synchronizing s_demo wf_s_demo).
  - vm_compute. lia.
  - exact step_connected_s_demo.
Qed.
```
NOTE: adjust the `right. left. …` nesting to the actual `step_witness` disjunction shape and the `In … [(a,b)]` membership (`left; reflexivity` proves `In (a,b) [(a,b)]`). If `nth 0 [[(0,1)];[(1,0)]] [] = [(0,1)]` doesn't reduce under `simpl`, use `vm_compute`/`cbn`. The frontier-1 case uses `In (1,0) (nth 1 …)` = case 3 of the witness (`In (p,q) (nth (S k) …)` with `S k = 1`).
- [ ] **Step 2: build** `bash .claude/scripts/timed-build.sh 180 execution/ConnSyncExamples.vo 2` → EXIT=0.
- [ ] **Step 3: export** append `ConnSync` to `execution/Execution.v`'s `Require Export` list.
- [ ] **Step 4: whole-project** `bash .claude/scripts/timed-build.sh 1800 @all 4` → EXIT=0.
- [ ] **Step 5: audit** scratch `execution/ConnSyncAudit.v` (`From Execution Require Import ConnSync. Print Assumptions step_connected_fully_synchronizing.`), register, build, capture (expected standard classical/proof-irrelevance axioms; no `admit`), then REMOVE + revert registration.
- [ ] **Step 6: INDEX** add a `ConnSync.v` subsection (`StepBarrier`, `step_barrier_implies_fullsync`, `prog_step`/`msg_step`, `step_witness`/`StepConnected`, `step_connected_fully_synchronizing`, `step_connected_dim2`), noting the honest matching-limitation scope.
- [ ] **Step 7: commit** `git add execution/ConnSyncExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): s_demo FullySynchronizing via connectivity + export + INDEX"`.

---

## Self-Review (vs the spec)
- **Coverage:** reduction (CS2) + edge lemmas (CS1) + connectivity predicate & main theorem (CS3) + example/wiring/audit (CS4). All spec components mapped.
- **Reuse:** `msg_step` reuses `ScheduleWf.op_for_send_iff`/`op_for_recv_iff` under `wf_schedule`; `step_connected_dim2` precomposes the existing `fully_synchronizing_dim2`.
- **Name consistency:** `mk_event`/`event_eq_of_proj`/`prog_step`/`msg_step`/`StepBarrier`/`step_barrier_gap`/`step_barrier_implies_fullsync`/`step_witness`/`StepConnected`/`barrier_step`/`step_connected_implies_step_barrier`/`step_connected_fully_synchronizing`/`step_connected_dim2` consistent across CS1–CS4.
- **Honest scope:** the matching-limitation caveat is recorded in the spec + INDEX; the lemmas are general, the predicate is a concrete witness.

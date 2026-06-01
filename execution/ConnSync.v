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

Lemma prog_step :
  forall s p k (Hp : p < sch_nprocs s)
         (Hk : k < length (sch_frontiers s)) (HSk : S k < length (sch_frontiers s)),
    ep_order (exec_of_schedule s) (mk_event s p k Hp Hk) (mk_event s p (S k) Hp HSk).
Proof.
  intros s p k Hp Hk HSk.
  unfold ep_order, exec_of_schedule, exec_of. simpl. apply rt_step.
  unfold edge. simpl. left. split; reflexivity.
Qed.

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
    + apply HSB. rewrite Hgap, Hz. lia.
Qed.

Lemma step_barrier_implies_fullsync :
  forall s, 0 < sch_nprocs s -> StepBarrier s -> FullySynchronizing s.
Proof.
  intros s Hnp HSB. unfold FullySynchronizing. intros x y Hlt.
  apply (step_barrier_gap s Hnp HSB (snd (proj1_sig y) - S (snd (proj1_sig x)))).
  lia.
Qed.

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
  assert (Hxe : x = mk_event s p k Hp Hk) by (apply event_eq_of_proj; rewrite Hx; reflexivity).
  assert (Hye : y = mk_event s q (S k) Hq HSk) by (apply event_eq_of_proj; rewrite Hy; reflexivity).
  rewrite Hxe, Hye.
  destruct Hw as [Heq | [Hk_pq | [HSk_pq | [r [Hr [Hpr Hrq]]]]]].
  - subst q.
    replace (mk_event s p (S k) Hq HSk) with (mk_event s p (S k) Hp HSk)
      by (apply event_eq_of_proj; reflexivity).
    apply (prog_step s p k Hp Hk HSk).
  - apply (hb_trans (desugar s) _ (mk_event s q k Hq Hk) _).
    + apply (msg_step s Hwf p q k Hp Hq Hk Hk_pq).
    + apply (prog_step s q k Hq Hk HSk).
  - apply (hb_trans (desugar s) _ (mk_event s p (S k) Hp HSk) _).
    + apply (prog_step s p k Hp Hk HSk).
    + apply (msg_step s Hwf p q (S k) Hp Hq HSk HSk_pq).
  - apply (hb_trans (desugar s) _ (mk_event s r k Hr Hk) _).
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
  assert (Hp : fst (proj1_sig x) < sch_nprocs s) by (rewrite <- nprocs_desugar; exact Hpx).
  assert (Hq : fst (proj1_sig y) < sch_nprocs s) by (rewrite <- nprocs_desugar; exact Hqy).
  assert (HSk : S (snd (proj1_sig x)) < length (sch_frontiers s)).
  { pose proof (event_index_lt s y) as H. lia. }
  assert (Hxproj : proj1_sig x = (fst (proj1_sig x), snd (proj1_sig x)))
    by (apply surjective_pairing).
  assert (Hyproj : proj1_sig y = (fst (proj1_sig y), S (snd (proj1_sig x)))).
  { rewrite (surjective_pairing (proj1_sig y)). rewrite Hgap. reflexivity. }
  apply (barrier_step s Hwf (fst (proj1_sig x)) (fst (proj1_sig y)) (snd (proj1_sig x))
           Hp Hq HSk
           (HSC (snd (proj1_sig x)) HSk (fst (proj1_sig x)) (fst (proj1_sig y)) Hp Hq)
           x y Hxproj Hyproj).
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

(* Well-formed schedules: per-frontier partial matching; desugar preserves wf. *)
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Event Edges Rank Poset Schedule.
Import ListNotations.

Definition endpoints (pq : Pid * Pid) : list Pid := [fst pq; snd pq].

Definition wf_frontier (n : nat) (fr : Frontier) : Prop :=
  (forall a b, In (a, b) fr -> a < n /\ b < n /\ a <> b) /\
  NoDup (flat_map endpoints fr).

Lemma wf_frontier_pair : forall n a b, a < n -> b < n -> a <> b -> wf_frontier n [(a,b)].
Proof.
  intros n a b Ha Hb Hab. unfold wf_frontier, endpoints. split.
  - intros x y [Heq|[]]. injection Heq as <- <-. repeat split; assumption.
  - simpl. constructor.
    + simpl. intros [H|[]]. apply Hab. symmetry. exact H.
    + constructor; [ simpl; intros [] | constructor ].
Qed.

Definition wf_schedule (s : Schedule) : Prop :=
  forall fr, In fr (sch_frontiers s) -> wf_frontier (sch_nprocs s) fr.

Lemma in_flat_fst : forall (fr : Frontier) p q, In (p, q) fr -> In p (flat_map endpoints fr).
Proof.
  intros fr p q Hin. apply in_flat_map. exists (p, q). split; [exact Hin| left; reflexivity].
Qed.
Lemma in_flat_snd : forall (fr : Frontier) p q, In (p, q) fr -> In q (flat_map endpoints fr).
Proof.
  intros fr p q Hin. apply in_flat_map. exists (p, q). split; [exact Hin| right; left; reflexivity].
Qed.

Lemma find_none_aux : forall {A} (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> find f l = None.
Proof.
  intros A f l. induction l as [|a l' IH]; intro Hall; simpl; [reflexivity|].
  rewrite (Hall a (or_introl eq_refl)). apply IH. intros x Hx. apply Hall. right. exact Hx.
Qed.

Lemma find_fst_unique :
  forall (fr : Frontier) p q, NoDup (flat_map endpoints fr) -> In (p, q) fr ->
    find (fun pq => Nat.eqb (fst pq) p) fr = Some (p, q).
Proof.
  induction fr as [|[a b] fr' IH]; intros p q Hnd Hin; [destruct Hin|].
  simpl in Hin. simpl flat_map in Hnd. simpl.
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb a p) eqn:Hap.
    + apply Nat.eqb_eq in Hap. subst a.
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      apply Hnotin. simpl. right. apply (in_flat_fst fr' p q Hin').
    + apply IH.
      * inversion Hnd as [|x l Hnotin Hnd']. subst.
        inversion Hnd' as [|y m Hnotin2 Hnd'']. subst. exact Hnd''.
      * exact Hin'.
Qed.

Lemma find_snd_unique :
  forall (fr : Frontier) p q, NoDup (flat_map endpoints fr) -> In (p, q) fr ->
    find (fun pq => Nat.eqb (snd pq) q) fr = Some (p, q).
Proof.
  induction fr as [|[a b] fr' IH]; intros p q Hnd Hin; [destruct Hin|].
  simpl in Hin. simpl flat_map in Hnd. simpl.
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb b q) eqn:Hbq.
    + apply Nat.eqb_eq in Hbq. subst b.
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      inversion Hnd' as [|y m Hnotin2 Hnd'']. subst.
      apply Hnotin2. apply (in_flat_snd fr' p q Hin').
    + apply IH.
      * inversion Hnd as [|x l Hnotin Hnd']. subst.
        inversion Hnd' as [|y m Hnotin2 Hnd'']. subst. exact Hnd''.
      * exact Hin'.
Qed.

Lemma no_fst_of_recv :
  forall (fr : Frontier) s p, NoDup (flat_map endpoints fr) -> In (s, p) fr ->
    find (fun pq => Nat.eqb (fst pq) p) fr = None.
Proof.
  induction fr as [|[a b] fr' IH]; intros s p Hnd Hin; [destruct Hin|].
  simpl in Hin. simpl flat_map in Hnd. simpl.
  destruct Hin as [Heq | Hin'].
  - injection Heq as Ha Hb. subst s. subst p.
    destruct (Nat.eqb a b) eqn:Hap.
    + apply Nat.eqb_eq in Hap.
      exfalso. inversion Hnd as [|x l Hnotin Hnd'].
      apply Hnotin. simpl. left. symmetry. exact Hap.
    + inversion Hnd as [|x l Hnotin Hnd']. subst.
      inversion Hnd' as [|y m Hnotin2 Hnd'']. subst.
      apply find_none_aux. intros [c d] Hcd. simpl.
      destruct (Nat.eqb c b) eqn:Hcp; [|reflexivity].
      apply Nat.eqb_eq in Hcp. subst c. exfalso. apply Hnotin2.
      apply (in_flat_fst fr' b d Hcd).
  - destruct (Nat.eqb a p) eqn:Hap.
    + apply Nat.eqb_eq in Hap. subst a.
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      apply Hnotin. simpl. right. apply (in_flat_snd fr' s p Hin').
    + apply IH with (s := s).
      * inversion Hnd as [|x l Hnotin Hnd']. subst.
        inversion Hnd' as [|y m Hnotin2 Hnd'']. subst. exact Hnd''.
      * exact Hin'.
Qed.

Lemma op_for_send_iff :
  forall n fr p q k, wf_frontier n fr ->
    (op_for fr p k = Send q k <-> In (p, q) fr).
Proof.
  intros n fr p q k [Hrange Hnd]. unfold op_for. split.
  - intro H. destruct (find (fun pq => Nat.eqb (fst pq) p) fr) as [[a b]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hfst]. apply Nat.eqb_eq in Hfst. simpl in Hfst. subst a.
      injection H as <-. exact Hin.
    + destruct (find (fun pq => Nat.eqb (snd pq) p) fr) as [[a b]|]; discriminate H.
  - intro Hin. rewrite (find_fst_unique fr p q Hnd Hin). reflexivity.
Qed.

Lemma op_for_recv_iff :
  forall n fr s p k, wf_frontier n fr ->
    (op_for fr p k = Recv s k <-> In (s, p) fr).
Proof.
  intros n fr s p k [Hrange Hnd]. unfold op_for. split.
  - intro H. destruct (find (fun pq => Nat.eqb (fst pq) p) fr) as [[a b]|] eqn:Hf.
    + discriminate H.
    + destruct (find (fun pq => Nat.eqb (snd pq) p) fr) as [[a b]|] eqn:Hg.
      * apply find_some in Hg as [Hin Hsnd]. apply Nat.eqb_eq in Hsnd. simpl in Hsnd. subst b.
        injection H as <-. exact Hin.
      * discriminate H.
  - intro Hin. rewrite (no_fst_of_recv fr s p Hnd Hin).
    rewrite (find_snd_unique fr s p Hnd Hin). reflexivity.
Qed.

Lemma op_at_desugar_inv :
  forall s p i o, op_at (desugar_prog s) p i = Some o ->
    p < sch_nprocs s /\ i < length (sch_frontiers s) /\
    o = op_for (nth i (sch_frontiers s) []) p i.
Proof.
  intros s p i o H.
  destruct (Nat.ltb p (sch_nprocs s)) eqn:Hp.
  - apply Nat.ltb_lt in Hp.
    destruct (Nat.ltb i (length (sch_frontiers s))) eqn:Hi.
    + apply Nat.ltb_lt in Hi.
      rewrite (op_at_desugar s p i Hp Hi) in H. injection H as <-.
      split; [exact Hp | split; [exact Hi | reflexivity]].
    + exfalso. apply Nat.ltb_ge in Hi.
      unfold op_at in H. rewrite proc_ops_desugar in H by exact Hp.
      assert (Hnone : nth_error (map (fun k => op_for (nth k (sch_frontiers s) []) p k)
                                      (seq 0 (length (sch_frontiers s)))) i = None).
      { apply nth_error_None. rewrite length_map, length_seq. lia. }
      rewrite Hnone in H. discriminate H.
  - exfalso. apply Nat.ltb_ge in Hp.
    unfold op_at, proc_ops, desugar_prog in H. simpl in H.
    rewrite nth_overflow in H by (rewrite length_map, length_seq; exact Hp).
    simpl in H. destruct i; discriminate H.
Qed.

Theorem desugar_wf : forall s, wf_schedule s -> wf_program (desugar s).
Proof.
  intros s Hwf.
  assert (Hnp : nprocs (desugar s) = sch_nprocs s) by apply nprocs_desugar.
  constructor.
  - (* wf_send_targets *)
    intros p i q t Hsend.
    apply op_at_desugar_inv in Hsend as [Hp [Hi Ho]].
    pose proof (op_for_tag (nth i (sch_frontiers s) []) p i q t) as [Htag _].
    assert (Hofeq : op_for (nth i (sch_frontiers s) []) p i = Send q t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth i (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hi. }
    pose proof (proj1 (op_for_send_iff (sch_nprocs s) _ p q i Hfr) Hofeq) as Hin.
    destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [_ [Hq _]].
    rewrite Hnp. exact Hq.
  - (* wf_recv_sources *)
    intros q j p t Hrecv.
    apply op_at_desugar_inv in Hrecv as [Hq [Hj Ho]].
    pose proof (op_for_tag (nth j (sch_frontiers s) []) q j p t) as [_ Htag].
    assert (Hofeq : op_for (nth j (sch_frontiers s) []) q j = Recv p t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth j (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hj. }
    pose proof (proj1 (op_for_recv_iff (sch_nprocs s) _ p q j Hfr) Hofeq) as Hin.
    destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [Hp _].
    rewrite Hnp. exact Hp.
  - (* wf_recv_matched *)
    intros q j p t Hrecv.
    apply op_at_desugar_inv in Hrecv as [Hq [Hj Ho]].
    pose proof (op_for_tag (nth j (sch_frontiers s) []) q j p t) as [_ Htag].
    assert (Hofeq : op_for (nth j (sch_frontiers s) []) q j = Recv p t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth j (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hj. }
    pose proof (proj1 (op_for_recv_iff (sch_nprocs s) _ p q j Hfr) Hofeq) as Hin.
    assert (Hp : p < sch_nprocs s).
    { destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [Hp _]. exact Hp. }
    exists j. split.
    + pose proof (proj2 (op_for_send_iff (sch_nprocs s) _ p q j Hfr) Hin) as Hsend.
      change (op_at (desugar s) p j) with (op_at (desugar_prog s) p j).
      rewrite (op_at_desugar s p j Hp Hj). rewrite Hsend. reflexivity.
    + intros i' Hi'. apply op_at_desugar_inv in Hi' as [Hp' [Hi'' Ho']].
      pose proof (op_for_tag (nth i' (sch_frontiers s) []) p i' q j) as [Htag' _].
      symmetry in Ho'. specialize (Htag' Ho'). lia.
  - (* wf_send_matched *)
    intros p i q t Hsend.
    apply op_at_desugar_inv in Hsend as [Hp [Hi Ho]].
    pose proof (op_for_tag (nth i (sch_frontiers s) []) p i q t) as [Htag _].
    assert (Hofeq : op_for (nth i (sch_frontiers s) []) p i = Send q t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth i (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hi. }
    pose proof (proj1 (op_for_send_iff (sch_nprocs s) _ p q i Hfr) Hofeq) as Hin.
    assert (Hq : q < sch_nprocs s).
    { destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [_ [Hq _]]. exact Hq. }
    exists i. split.
    + pose proof (proj2 (op_for_recv_iff (sch_nprocs s) _ p q i Hfr) Hin) as Hrecv.
      change (op_at (desugar s) q i) with (op_at (desugar_prog s) q i).
      rewrite (op_at_desugar s q i Hq Hi). rewrite Hrecv. reflexivity.
    + intros j' Hj'. apply op_at_desugar_inv in Hj' as [Hq' [Hj'' Ho']].
      pose proof (op_for_tag (nth j' (sch_frontiers s) []) q j' p i) as [_ Htag'].
      symmetry in Ho'. specialize (Htag' Ho'). lia.
Qed.

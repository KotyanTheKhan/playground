From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBefore Require Import HappenedBefore.
From HappenedBefore Require Import PosetInstance.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

(* ========== Unbounded Linear Chain Example ========== *)

(* 
  We define a sequence of events where each event is on a unique process.
  Event n is on process n. This ensures acyclicity.
*)
Definition alternating_event (n : nat) : Event :=
  ⟨n, 0⟩.

Definition alternating_message (n : nat) : Message :=
  {| send_event := alternating_event n;
     recv_event := alternating_event (S n) |}.

(*
  Recursive definition of history containing messages from 0 to n-1.
  alternating_history n contains messages:
  0->1, 1->2, ..., (n-1)->n
*)
Fixpoint alternating_history (n : nat) : History :=
  match n with
  | 0 => nil
  | S n' => cons (alternating_message n') (alternating_history n')
end.

(*
  Proof that event 0 happens before event n in the history of size n.
*)
Example alternating_causality :
  forall n, alternating_event 0 ≺[alternating_history n] alternating_event n.
Proof.
  intro n.
  induction n.
  - (* Base case: 0 -> 0 *)
    apply hb_refl.
  - (* Inductive step: 0 -> S n *)
    apply hb_trans with (alternating_event n).
    + (* 0 -> n in history S n *)
      (* Extend history monotonicity *)
      assert (H_mono: forall h e_start e_end m_new, e_start ≺[h] e_end -> e_start ≺[cons m_new h] e_end).
      {
        intros h0 e_s e_e m_n H_hb.
        induction H_hb.
        - apply hb_refl.
        - apply hb_message. destruct H as [m' [Hin Hlink]].
          exists m'. split. right. assumption. assumption.
        - eapply hb_trans; eauto.
      }
      apply H_mono.
      assumption.
    + (* n -> S n in history S n *)
      apply hb_message.
      unfold message_link.
      exists (alternating_message n).
      split.
      * (* Message is in history *)
        unfold alternating_history. left. reflexivity.
      * (* Message connects n and S n *)
        split; reflexivity.
Qed.

(* ========== Acyclicity and Instance ========== *)

(* Helper: Characterize messages in the history *)
Lemma alternating_history_content : forall n m,
  In m (alternating_history n) -> exists k, k < n /\ m = alternating_message k.
Proof.
  induction n; intros m Hin.
  - (* Base: nil *)
    inversion Hin.
  - (* Step: S n *)
    simpl in Hin. destruct Hin as [Heq | Htail].
    + (* Head *)
      exists n. split. lia. symmetry. assumption.
    + (* Tail *)
      apply IHn in Htail. destruct Htail as [k [Hlt Heq]].
      exists k. split. lia. assumption.
Qed.

Lemma alternating_acyclic : forall n, IsAcyclic (alternating_history n).
Proof.
  intro n.
  unfold IsAcyclic.
  intros e H_cycle.
  
  (* We show that strict happened before implies increasing process ID *)
  assert (Mono: forall a b, strict_happened_before (alternating_history n) a b -> process a < process b).
  {
    intros a b Hsb.
    induction Hsb.
    - (* Direct message *)
      destruct H as [m [Hin [Hs Hr]]].
      (* Use helper to identify m *)
      apply alternating_history_content in Hin.
      destruct Hin as [k [Hlt Heq]].
      subst m.
      simpl in Hs, Hr.
      rewrite <- Hs, <- Hr.
      unfold alternating_event. simpl. lia.
    - (* Transitive *)
      lia.
  }
  
  apply Mono in H_cycle.
  lia.
Qed.

Instance alternating_hb (n : nat) : IsHappenedBefore (alternating_history n) (happened_before (alternating_history n)).
Proof.
  constructor.
  apply happened_before_poset.
  apply alternating_acyclic.
Defined.

From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From Stdlib Require Import Arith.

(* ========== Unbounded Alternating Example ========== *)

(* 
  We define a sequence of events where processes 0 and 1 alternate.
  Event n is on process (n mod 2) with clock n.
*)
Definition alternating_event (n : nat) : Event :=
  ⟨n mod 2, n⟩.

(* 
  We define a sequence of messages where event n sends to event n+1.
  Since clock n < clock (n+1) is always true (n < n+1), this is valid.
*)
Lemma alt_clock_lt : forall n, clock (alternating_event n) < clock (alternating_event (S n)).
Proof.
  intro n.
  unfold alternating_event; simpl.
  constructor.
Qed.

Definition alternating_message (n : nat) : Message :=
  {| send_event := alternating_event n;
     recv_event := alternating_event (S n);
     clock_lt := alt_clock_lt n |}.

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
    (* We know 0 -> n from IH *)
    (* We need to show n -> S n via message *)
    apply hb_trans with (alternating_event n).
    + (* 0 -> n *)
      (* The history for S n is (message n->Sn) :: (history n) *)
      (* We need to show that if 0 -> n in history n, it also holds in history S n *)
      
      (* Helper: extending history preserves HB *)
      assert (H_mono: forall h e_start e_end m_new, e_start ≺[h] e_end -> e_start ≺[cons m_new h] e_end).
      {
        intros h e_start e_end m_new H_hb.
        induction H_hb.
        - apply hb_refl.
        - apply hb_local. assumption.
        - apply hb_message. destruct H as [m' [Hin Hlink]].
          exists m'. split. right. assumption. assumption.
        - eapply hb_trans. 
          * apply IHH_hb1.
          * apply IHH_hb2.
      }
      apply H_mono.
      assumption.
    + (* n -> S n *)
      apply hb_message.
      unfold message_link.
      exists (alternating_message n).
      split.
      * (* Message is in history *)
        unfold alternating_history. left. reflexivity.
      * (* Message connects n and S n *)
        split; reflexivity.
Qed.

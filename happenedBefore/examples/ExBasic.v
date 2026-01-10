From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBefore Require Import LatticeOperations.

(* ========== Basic Examples ========== *)

(* Example: Create some events using notation *)
(* Example: Create some events using notation *)
Definition e0 : Event := ⟨0⟩.
Definition e1 : Event := ⟨0⟩.
Definition e2 : Event := ⟨1⟩.
Definition e3 : Event := ⟨1⟩.

(* Example: Create a message from e1 to e2 using notation *)
Definition m12 : Message := e1 →ₘ e2.
Definition example_history : History := cons m12 nil.

(* Example: Message causality *)
Example message_causality :
  e1 ≺[example_history] e2.
Proof.
  apply hb_message.
  unfold message_link.
  exists m12.
  split.
  - unfold example_history. left. reflexivity.
  - split; reflexivity.
Qed.

(* Helper: In an empty history, causality implies same process equality 
   (since only refl is possible) *)
Lemma happened_before_nil_same_process : forall e1 e2,
  happened_before nil e1 e2 -> process e1 = process e2.
Proof.
  intros e1 e2 H.
  induction H.
  - (* hb_refl *) reflexivity.
  - (* hb_message *) destruct H as [m [Hin _]]. inversion Hin.
  - (* hb_trans *) rewrite IHhappened_before1. assumption.
Qed.

(* Example: Concurrent events using notation *)
Example e0_e2_concurrent :
  e0 ∥ e2.
Proof.
  unfold concurrent.
  split; intro H.
  - (* e0 cannot happen before e2 in empty history *)
    apply happened_before_nil_same_process in H.
    unfold e0, e2 in H; simpl in H.
    discriminate.
  - (* e2 cannot happen before e0 in empty history *)
    apply happened_before_nil_same_process in H.
    unfold e0, e2 in H; simpl in H.
    discriminate.
Qed.

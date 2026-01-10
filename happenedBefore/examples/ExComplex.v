From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBeforeExamples Require Import ExBasic.

(* ========== Complex Examples ========== *)

(* Example: Complex message chain *)
Definition e4 : Event := ⟨0⟩.
Definition e5 : Event := ⟨1⟩.
Definition m23 : Message := e2 →ₘ e3.
Definition m34 : Message := e3 →ₘ e4.
Definition complex_history : History := cons m12 (cons m23 (cons m34 nil)).

(* Example: Transitive causality through multiple messages *)
Example multi_hop_causality :
  e1 ≺[complex_history] e4.
Proof.
  apply hb_trans with e2.
  - apply hb_message. unfold message_link.
    exists m12. split. unfold complex_history. left. reflexivity.
    split; reflexivity.
  - apply hb_trans with e3.
    + apply hb_message. unfold message_link.
      exists m23. split. unfold complex_history. right. left. reflexivity.
      split; reflexivity.
    + apply hb_message. unfold message_link.
      exists m34. split. unfold complex_history. right. right. left. reflexivity.
      split; reflexivity.
Qed.

(* Example: Reflexivity using notation *)
Example reflexivity_notation :
  forall e h, e ≺[h] e.
Proof.
  intros. apply hb_refl.
Qed.

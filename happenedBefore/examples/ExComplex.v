From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBeforeExamples Require Import ExBasic.

(* ========== Complex Examples ========== *)

(* Example: Complex message chain *)
Definition e4 : Event := ⟨0, 4⟩.
Definition e5 : Event := ⟨1, 4⟩.
Definition m23 : Message := (e2 →ₘ e3) ltac:(repeat constructor).
Definition m34 : Message := (e3 →ₘ e4) ltac:(repeat constructor).
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

(* Example: Same process ordering is transitive *)
Example same_process_transitive :
  forall h, e0 ≺[h] e4.
Proof.
  intro h.
  apply hb_trans with e1.
  - apply hb_local. unfold same_process_before; simpl.
    split; [reflexivity | repeat constructor].
  - apply hb_local. unfold same_process_before; simpl.
    split; [reflexivity | repeat constructor].
Qed.

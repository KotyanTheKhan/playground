From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBefore Require Import HappenedBefore.
From HappenedBefore Require Import PosetInstance.
From HappenedBeforeExamples Require Import ExBasic.
From Stdlib Require Import Lia.

(* ========== Complex Examples ========== *)

(* Example: Complex message chain across distinct processes *)
(* To ensure acyclicity without indices, we must use distinct processes *)
Definition ep1 : Event := ⟨1⟩.
Definition ep2 : Event := ⟨2⟩.
Definition ep3 : Event := ⟨3⟩.

Definition m12_complex : Message := ep1 →ₘ ep2.
Definition m23_complex : Message := ep2 →ₘ ep3.
Definition complex_history : History := cons m12_complex (cons m23_complex nil).

(* Example: Transitive causality through multiple messages *)
Example multi_hop_causality :
  ep1 ≺[complex_history] ep3.
Proof.
  apply hb_trans with ep2.
  - apply hb_message. unfold message_link.
    exists m12_complex. split. unfold complex_history. left. reflexivity.
    split; reflexivity.
  - apply hb_message. unfold message_link.
    exists m23_complex. split. unfold complex_history. right. left. reflexivity.
    split; reflexivity.
Qed.

(* Example: Reflexivity using notation *)
Example reflexivity_notation :
  forall e, e ≺[complex_history] e.
Proof.
  intros. apply hb_refl.
Qed.

(* Proof of Acyclicity for complex_history *)
Lemma complex_history_acyclic : IsAcyclic complex_history.
Proof.
  unfold IsAcyclic.
  intros e H_cycle.
  
  (* Define a measure: process ID *)
  pose (ProcessNum := fun e => process e).
  
  (* Show that strict happened-before implies strictly increasing process ID *)
  assert (H_forward: forall a b, strict_happened_before complex_history a b -> ProcessNum a < ProcessNum b).
  {
    intros a b H_sb.
    induction H_sb.
    - (* Direct message *)
      destruct H as [m [Hin [Hs Hr]]].
      unfold complex_history in Hin.
      destruct Hin as [H1 | [H2 | Hnil]]; [| |contradiction].
      + (* m12_complex: 1 -> 2 *)
        subst m. rewrite <- Hs, <- Hr.
        unfold ProcessNum, m12_complex, ep1, ep2. simpl. lia.
      + (* m23_complex: 2 -> 3 *)
        subst m. rewrite <- Hs, <- Hr.
        unfold ProcessNum, m23_complex, ep2, ep3. simpl. lia.
    - (* Transitive *)
      lia.
  }
  
  apply H_forward in H_cycle.
  lia.
Qed.

(* Instance of IsHappenedBefore *)
Instance complex_hb : IsHappenedBefore complex_history (happened_before complex_history).
Proof.
  constructor.
  apply happened_before_poset.
  apply complex_history_acyclic.
Defined.

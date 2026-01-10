From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBefore Require Import LatticeOperations.
From Stdlib Require Import Lia.
From HappenedBefore Require Import HappenedBefore.
From HappenedBefore Require Import PosetInstance.

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

(* ========== Happened-Before Instance ========== *)

(* To make this an instance of IsHappenedBefore, we need to prove it is a Poset.
   For happened_before, this requires IsAcyclic. *)

(* To make this an instance of IsHappenedBefore, we need to prove it is a Poset.
   For happened_before, this requires IsAcyclic. *)

Lemma example_history_acyclic : IsAcyclic example_history.
Proof.
  unfold IsAcyclic.
  intros e H_cycle.
  (* Cycle means e <+ e. In our history [0->1], this is impossible. *)
  
  (* We define a measure to show events proceed forward *)
  pose (ProcessNum := fun e => process e).
  assert (H_forward: forall a b, strict_happened_before example_history a b -> ProcessNum a < ProcessNum b).
  {
    intros a b H_sb.
    induction H_sb.
    - (* Direct *)
      destruct H as [m [Hin [Hs Hr]]].
      unfold example_history in Hin.
      destruct Hin as [Heq | Hnil]; [|contradiction].
      subst m. 
      (* m12 is 0->1 *)
      rewrite <- Hs, <- Hr.
      unfold ProcessNum, m12, e1, e2. simpl. auto.
    - (* Transitive *)
      lia.
  }
  
  (* Apply the measure to the cycle e <+ e *)
  apply H_forward in H_cycle.
  lia.
Qed.

Instance example_hb : IsHappenedBefore example_history (happened_before example_history).
Proof.
  constructor.
  apply happened_before_poset.
  apply example_history_acyclic.
Defined.

(* Poset instance for happened-before relation *)
Require Import Posets.PosetClasses.
Require Import EventStructure.
Require Import CausalRelation.
From Stdlib Require Import Lia.

(* ========== Helper Lemmas ========== *)
Require Import CausalRelationProps.

(* ========== Poset Instance ========== *)

(* Happened-before is a partial order (poset) ONLY if the history is acyclic *)
Instance happened_before_poset (h : History) (H_acyclic : IsAcyclic h) : IsPoset Event (happened_before h).
Proof.
  constructor.
  - (* reflexivity *)
    intro e. apply hb_refl.
  - (* antisymmetry *)
    intros e1 e2 H1 H2.
    apply (hb_antisym_of_acyclic h H_acyclic); assumption.
  - (* transitivity *)
    intros e1 e2 e3 H1 H2.
    apply hb_trans with e2; assumption.
Defined.

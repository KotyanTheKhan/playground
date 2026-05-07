(* Properties of Causal Relations *)
Require Import EventStructure.
Require Import CausalRelation.
From Stdlib Require Import Lia.

(* ========== Helper Lemmas ========== *)

(* If e1 and e2 are related by happened-before in both directions,
   and one direction uses only hb_refl, then e1 = e2 *)
Lemma hb_refl_antisym : forall h e1 e2,
  happened_before h e1 e2 ->
  e1 = e2 ->
  happened_before h e2 e1 ->
  e1 = e2.
Proof.
  intros h e1 e2 _ Heq _.
  exact Heq.
Qed.

(* Relationship between strict and non-strict happened-before *)

Lemma shb_implies_hb : forall h e1 e2,
  strict_happened_before h e1 e2 ->
  happened_before h e1 e2.
Proof.
  intros h e1 e2 H.
  induction H.
  - apply hb_message; assumption.
  - apply hb_trans with e2; assumption.
Qed.

Lemma hb_implies_shb_or_eq : forall h e1 e2,
  happened_before h e1 e2 ->
  e1 = e2 \/ strict_happened_before h e1 e2.
Proof.
  intros h e1 e2 H.
  induction H.
  - (* hb_refl *)
    left; reflexivity.
  - (* hb_message *)
    right; apply shb_message; assumption.
  - (* hb_trans *)
    destruct IHhappened_before1 as [Eq1 | SHB1];
    destruct IHhappened_before2 as [Eq2 | SHB2].
    + (* e1 = e2, e2 = e3 *)
      left; subst; reflexivity.
    + (* e1 = e2, e2 < e3 *)
      right; subst; assumption.
    + (* e1 < e2, e2 = e3 *)
      right; subst; assumption.
    + (* e1 < e2, e2 < e3 *)
      right; apply shb_trans with e2; assumption.
Qed.

(* Main Antisymmetry Lemma under Acyclicity Assumption *)

Lemma hb_antisym_of_acyclic : forall h,
  IsAcyclic h ->
  forall e1 e2,
  happened_before h e1 e2 ->
  happened_before h e2 e1 ->
  e1 = e2.
Proof.
  intros h H_acyclic e1 e2 H12 H21.
  destruct (hb_implies_shb_or_eq h e1 e2 H12) as [Eq12 | SHB12].
  - assumption.
  - destruct (hb_implies_shb_or_eq h e2 e1 H21) as [Eq21 | SHB21].
    + symmetry; assumption.
    + (* Both strictly happen before each other -> contradiction *)
      exfalso.
      assert (Cycle : strict_happened_before h e1 e1).
      { apply shb_trans with e2; assumption. }
      unfold IsAcyclic in H_acyclic.
      apply (H_acyclic e1); assumption.
Qed.

(* Distributive lattice instance for lists *)
Require Import Posets.PosetClasses.
Require Import Posets.LatticeClasses.
Require Import Structure.
Require Import Operations.
Require Import Helpers.
Require Import PosetInstance.
Require Import MeetSemilatticeInstance.
Require Import JoinSemilatticeInstance.
Require Import LatticeInstance.
From Hammer Require Import Hammer.

(* ========== Helper Lemmas for Distributivity ========== *)

Ltac solve_distrib :=
  intros;
  unfold list_meet, list_join;
  (* Rewrite false assumptions in goal *)
  repeat match goal with
  | [ H : list_leb _ _ = false |- _ ] => rewrite H
  end;
  (* Rewrite true assumptions in goal *)
  repeat match goal with
  | [ H : list_leb _ _ = true |- _ ] => rewrite H
  end;
  (* Rewrite refl *)
  repeat rewrite list_leb_refl;
  simpl;
  try reflexivity;
  (* Contradictions *)
  try match goal with
  | [ H1: list_leb ?x ?y = true, H2: list_leb ?y ?z = true, H3: list_leb ?x ?z = false |- _ ] =>
      pose proof (list_leb_trans _ _ _ H1 H2);
      rewrite H3 in *; discriminate
  | [ H1: list_leb ?x ?y = true, H2: list_leb ?y ?z = true, H3: list_leb ?z ?x = true |- _ ] =>
      assert (x = z) by (apply list_leb_antisym; [eapply list_leb_trans; eauto | auto]);
      subst; congruence
  | [ H1: list_leb ?x ?y = false, H2: list_leb ?y ?z = false, H3: list_leb ?x ?z = true |- _ ] =>
      assert (list_leb y x = true) by (destruct (list_leb_total y x); auto; rewrite H1 in *; discriminate);
      assert (list_leb z y = true) by (destruct (list_leb_total z y); auto; rewrite H2 in *; discriminate);
      assert (z = x) by (apply list_leb_antisym; [eapply list_leb_trans; eauto | auto]);
      subst; rewrite H2 in *; discriminate
  | [ H1: list_leb ?x ?y = false, H2: list_leb ?x ?z = true, H3: list_leb ?y ?z = false |- _ ] =>
      assert (list_leb y x = true) by (destruct (list_leb_total y x); auto; rewrite H1 in *; discriminate);
      assert (list_leb z y = true) by (destruct (list_leb_total z y); auto; rewrite H3 in *; discriminate);
      assert (x = z) by (apply list_leb_antisym; [eapply list_leb_trans; eauto | auto]);
      subst; rewrite H1 in *; rewrite list_leb_refl in *; discriminate
  end;
  (* Fallback to hauto for contradictions and hard cases *)
  hauto lq:on use: list_leb_total, list_leb_antisym, list_leb_trans, list_leb_refl.

(* Helper lemmas for meet distributivity - one for each of the 8 cases *)
Lemma distrib_meet_case_TTT : forall x y z,
  list_leb x y = true -> list_leb x z = true -> list_leb y z = true ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_TTF : forall x y z,
  list_leb x y = true -> list_leb x z = true -> list_leb y z = false ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_TFT : forall x y z,
  list_leb x y = true -> list_leb x z = false -> list_leb y z = true ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_TFF : forall x y z,
  list_leb x y = true -> list_leb x z = false -> list_leb y z = false ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_FTT : forall x y z,
  list_leb x y = false -> list_leb x z = true -> list_leb y z = true ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_FTF : forall x y z,
  list_leb x y = false -> list_leb x z = true -> list_leb y z = false ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_FFT : forall x y z,
  list_leb x y = false -> list_leb x z = false -> list_leb y z = true ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.

Lemma distrib_meet_case_FFF : forall x y z,
  list_leb x y = false -> list_leb x z = false -> list_leb y z = false ->
  list_meet x (list_join y z) = list_join (list_meet x y) (list_meet x z).
Proof. solve_distrib. Qed.


(* Helper lemmas for join distributivity - one for each of the 8 cases *)
Lemma distrib_join_case_TTT : forall x y z,
  list_leb x y = true -> list_leb x z = true -> list_leb y z = true ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_TTF : forall x y z,
  list_leb x y = true -> list_leb x z = true -> list_leb y z = false ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_TFT : forall x y z,
  list_leb x y = true -> list_leb x z = false -> list_leb y z = true ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_TFF : forall x y z,
  list_leb x y = true -> list_leb x z = false -> list_leb y z = false ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_FTT : forall x y z,
  list_leb x y = false -> list_leb x z = true -> list_leb y z = true ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_FTF : forall x y z,
  list_leb x y = false -> list_leb x z = true -> list_leb y z = false ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_FFT : forall x y z,
  list_leb x y = false -> list_leb x z = false -> list_leb y z = true ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.

Lemma distrib_join_case_FFF : forall x y z,
  list_leb x y = false -> list_leb x z = false -> list_leb y z = false ->
  list_join x (list_meet y z) = list_meet (list_join x y) (list_join x z).
Proof. solve_distrib. Qed.


(* ========== Distributive Lattice Instance ========== *)

Instance list_distributive_lattice : IsDistributiveLattice List list_meet list_join.
Proof.
  constructor.
  - (* distrib_meet: x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) *)
    intros x y z.
    destruct (list_leb x y) eqn:Exy;
    destruct (list_leb x z) eqn:Exz;
    destruct (list_leb y z) eqn:Eyz.
    + apply distrib_meet_case_TTT; auto.
    + apply distrib_meet_case_TTF; auto.
    + apply distrib_meet_case_TFT; auto.
    + apply distrib_meet_case_TFF; auto.
    + apply distrib_meet_case_FTT; auto.
    + apply distrib_meet_case_FTF; auto.
    + apply distrib_meet_case_FFT; auto.
    + apply distrib_meet_case_FFF; auto.
  - (* distrib_join: x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) *)
    intros x y z.
    destruct (list_leb x y) eqn:Exy;
    destruct (list_leb x z) eqn:Exz;
    destruct (list_leb y z) eqn:Eyz.
    + apply distrib_join_case_TTT; auto.
    + apply distrib_join_case_TTF; auto.
    + apply distrib_join_case_TFT; auto.
    + apply distrib_join_case_TFF; auto.
    + apply distrib_join_case_FTT; auto.
    + apply distrib_join_case_FTF; auto.
    + apply distrib_join_case_FFT; auto.
    + apply distrib_join_case_FFF; auto.
Qed.

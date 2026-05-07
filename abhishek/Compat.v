(* Compatibility shims for old Coq standard library *)
(* This file provides aliases for deprecated lemmas to ease migration *)

From Stdlib Require Export PeanoNat.
From Stdlib Require Export Arith.
From Stdlib Require Export Lia.

(* Reexport commonly needed items *)
From Stdlib Require Export Ensembles.
From Stdlib Require Export Relations_1.
From Stdlib Require Export Finite_sets.
From Stdlib Require Export Constructive_sets.
From Stdlib Require Export Powerset.
From Stdlib Require Export Powerset_facts.
From Stdlib Require Export Powerset_Classical_facts.
From Stdlib Require Export Finite_sets_facts.
From Stdlib Require Export Image.
From Stdlib Require Export Classical.
From Stdlib Require Export ClassicalChoice.

(* Compatibility aliases for renamed/moved lemmas *)
Notation le_trans := PeanoNat.Nat.le_trans.
Notation lt_trans := PeanoNat.Nat.lt_trans.
Notation le_lt_trans := PeanoNat.Nat.le_lt_trans.
Notation lt_le_trans := PeanoNat.Nat.lt_le_trans.
Notation le_antisym := PeanoNat.Nat.le_antisymm.
Notation lt_irrefl := PeanoNat.Nat.lt_irrefl.
Notation lt_asym := PeanoNat.Nat.lt_asymm.
Notation le_refl := PeanoNat.Nat.le_refl.

(* Comparison lemmas *)
Notation le_lt_or_eq := PeanoNat.Nat.le_lteq.
Notation le_or_lt := PeanoNat.Nat.le_gt_cases.

(* Arithmetic lemmas *)
Notation plus_comm := PeanoNat.Nat.add_comm.
Notation plus_assoc := PeanoNat.Nat.add_assoc.
Notation mult_comm := PeanoNat.Nat.mul_comm.
Notation mult_assoc := PeanoNat.Nat.mul_assoc.
Notation plus_0_r := PeanoNat.Nat.add_0_r.
Notation plus_0_l := PeanoNat.Nat.add_0_l.
Notation mult_0_r := PeanoNat.Nat.mul_0_r.
Notation mult_0_l := PeanoNat.Nat.mul_0_l.
Notation mult_1_r := PeanoNat.Nat.mul_1_r.
Notation mult_1_l := PeanoNat.Nat.mul_1_l.

(* Subtraction lemmas *)
Notation minus_n_O := PeanoNat.Nat.sub_0_r.
Notation minus_n_n := PeanoNat.Nat.sub_diag.

(* S and pred *)
Notation lt_n_Sn := PeanoNat.Nat.lt_succ_diag_r.
Notation le_n_Sn := PeanoNat.Nat.le_succ_diag_r.
Notation pred_Sn := PeanoNat.Nat.pred_succ.

(* Lemmas that no longer exist - provide alternatives *)
Lemma lt_n_0 : forall n, ~ n < 0.
Proof. intros. lia. Qed.

Lemma le_n_O_eq : forall n, n <= 0 -> n = 0.
Proof. intros. lia. Qed.

Lemma lt_S_n : forall n m, S n < S m -> n < m.
Proof. intros. lia. Qed.

Lemma le_S_n : forall n m, S n <= S m -> n <= m.
Proof. intros. lia. Qed.

Lemma pred_of_minus : forall n, pred n = n - 1.
Proof. intros. lia. Qed.

Lemma nat_total_order : forall m n : nat, m <> n -> m < n \/ m > n.
Proof. intros. lia. Qed.

Lemma mult_S_le_reg_l : forall n m p, S p * m <= S p * n -> m <= n.
Proof. 
  intros n m p H.
  assert (S p > 0) by lia.
  apply PeanoNat.Nat.mul_le_mono_pos_l in H; auto.
Qed.

Lemma le_lt_n_Sm : forall n m, m <= 1 -> m < S (S n).
Proof. intros. lia. Qed.

Notation mult_is_O := PeanoNat.Nat.eq_mul_0.
Notation mult_le_compat_r := PeanoNat.Nat.mul_le_mono_r.
Notation mult_lt_compat_r := PeanoNat.Nat.mul_lt_mono_pos_r.

(* Hint for omega replacement *)
Ltac omega := lia.

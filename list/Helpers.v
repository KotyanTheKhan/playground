(* Helper lemmas for list operations and orderings *)
From List Require Import Structure.
From List Require Import Operations.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.Arith.

(*
  This development uses lexicographic ordering as a tiebreaker:
  Lists are ordered first by length, then lexicographically.
  This makes the ordering total and allows all lattice properties to be proven.
*)

(* ========== Helper Lemmas for nat_leb ========== *)

Lemma nat_leb_refl : forall n, nat_leb n n = true.
Proof.
  induction n; simpl; auto.
Qed.

Lemma nat_leb_le : forall n m, nat_leb n m = true <-> n <= m.
Proof.
  induction n; destruct m; simpl; split; intros; auto; try lia.
  - apply IHn in H. lia.
  - apply IHn. lia.
Qed.

Lemma nat_leb_gt : forall n m, nat_leb n m = false <-> m < n.
Proof.
  intros. split; intros.
  - destruct (nat_leb n m) eqn:E; try discriminate.
    destruct (le_lt_dec n m).
    + apply nat_leb_le in l. rewrite l in E. discriminate.
    + auto.
  - destruct (nat_leb n m) eqn:E; auto.
    apply nat_leb_le in E. lia.
Qed.

(* ========== Helper Lemmas for Lexicographic Ordering ========== *)

Lemma list_lex_le_refl : forall l, list_lex_le l l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma list_lex_leb_refl : forall l, list_lex_leb l l = true.
Proof.
  induction l; simpl; auto.
  destruct (nat_leb n n) eqn:E.
  - destruct (nat_leb n n) eqn:E2.
    + auto.
    + discriminate.
  - pose proof (nat_leb_refl n). rewrite H in E. discriminate.
Qed.

Lemma list_leb_refl : forall l, list_leb l l = true.
Proof.
  intro l. unfold list_leb.
  pose proof (nat_leb_refl (length_List l)) as H.
  destruct (nat_leb (length_List l) (length_List l)) eqn:E.
  - destruct (nat_leb (length_List l) (length_List l)) eqn:E2.
    + apply list_lex_leb_refl.
    + discriminate.
  - rewrite H in E. discriminate.
Qed.

Lemma list_lex_le_antisym : forall l1 l2,
  list_lex_le l1 l2 -> list_lex_le l2 l1 -> l1 = l2.
Proof.
  induction l1 as [|n1 l1' IH]; intros [|n2 l2']; simpl in *; intros H1 H2.
  - reflexivity.
  - inversion H2.
  - inversion H1.
  - destruct H1 as [H1 | [Heq1 Hlex1]]; destruct H2 as [H2 | [Heq2 Hlex2]].
    + lia.
    + lia.
    + lia.
    + subst. f_equal. apply IH; auto.
Qed.

Lemma list_lex_le_trans : forall l1 l2 l3,
  list_lex_le l1 l2 -> list_lex_le l2 l3 -> list_lex_le l1 l3.
Proof.
  induction l1 as [|n1 l1' IH]; intros [|n2 l2'] [|n3 l3']; simpl in *; intros H1 H2; auto.
  - inversion H1.
  - destruct H1 as [H1' | [Heq1 Hlex1]]; destruct H2 as [H2' | [Heq2 Hlex2]].
    + left. lia.
    + left. lia.
    + subst. left. auto.
    + subst. right. split; auto. eapply IH; eauto.
Qed.

Lemma list_lex_leb_iff : forall l1 l2,
  list_lex_leb l1 l2 = true <-> list_lex_le l1 l2.
Proof.
  induction l1 as [|n1 l1' IH]; intros [|n2 l2']; simpl; split; intros H.
  - auto.
  - auto.
  - auto.
  - auto.
  - discriminate.
  - inversion H.
  - destruct (nat_leb n1 n2) eqn:E1; destruct (nat_leb n2 n1) eqn:E2.
    + apply IH in H. right. split; auto.
      apply nat_leb_le in E1. apply nat_leb_le in E2. lia.
    + left. apply nat_leb_le in E1. apply nat_leb_gt in E2. lia.
    + discriminate.
    + discriminate.
  - destruct H as [H | [Heq Hlex]].
    + assert (Hle1: nat_leb n1 n2 = true) by (apply nat_leb_le; lia).
      rewrite Hle1. assert (Hle2: nat_leb n2 n1 = false) by (apply nat_leb_gt; lia).
      rewrite Hle2. auto.
    + subst. simpl. rewrite nat_leb_refl. apply IH. auto.
Qed.

Lemma list_lex_leb_total : forall l1 l2,
  list_lex_leb l1 l2 = true \/ list_lex_leb l2 l1 = true.
Proof.
  induction l1 as [|n1 l1' IH]; intros [|n2 l2'].
  - left. simpl. auto.
  - left. simpl. auto.
  - right. simpl. auto.
  - simpl.
    destruct (Nat.lt_trichotomy n1 n2) as [Hlt | [Heq | Hgt]].
    + (* n1 < n2 *)
      left.
      assert (Hle1: nat_leb n1 n2 = true) by (apply nat_leb_le; lia).
      rewrite Hle1.
      assert (Hle2: nat_leb n2 n1 = false) by (apply nat_leb_gt; lia).
      rewrite Hle2. auto.
    + (* n1 = n2 *)
      subst.
      simpl.
      rewrite nat_leb_refl. simpl.
      apply IH.
    + (* n1 > n2 *)
      right.
      assert (Hle1: nat_leb n2 n1 = true) by (apply nat_leb_le; lia).
      rewrite Hle1.
      assert (Hle2: nat_leb n1 n2 = false) by (apply nat_leb_gt; lia).
      rewrite Hle2. auto.
Qed.

(* ========== Helper Lemmas for list_leb ========== *)

Lemma list_leb_iff : forall l1 l2,
  list_leb l1 l2 = true <-> list_le l1 l2.
Proof.
  intros. unfold list_leb, list_le. split; intros.
  - destruct (nat_leb (length_List l1) (length_List l2)) eqn:E1; try discriminate.
    destruct (nat_leb (length_List l2) (length_List l1)) eqn:E2.
    + right. split. apply nat_leb_le in E1. apply nat_leb_le in E2. lia.
      apply list_lex_leb_iff. auto.
    + left. apply nat_leb_le in E1. apply nat_leb_gt in E2. lia.
  - destruct H as [Hlt | [Heq Hlex]].
    + assert (Hle1: nat_leb (length_List l1) (length_List l2) = true) by (apply nat_leb_le; lia).
      rewrite Hle1. assert (Hle2: nat_leb (length_List l2) (length_List l1) = false) by (apply nat_leb_gt; lia).
      rewrite Hle2. auto.
    + assert (Hlen: length_List l1 = length_List l2) by lia.
      rewrite Hlen. 
      rewrite nat_leb_refl.
      simpl. apply list_lex_leb_iff. auto.
Qed.

Lemma list_le_to_leb : forall l1 l2,
  list_le l1 l2 -> list_leb l1 l2 = true.
Proof.
  intros. apply list_leb_iff. exact H.
Qed.

Lemma list_leb_antisym : forall l1 l2,
  list_leb l1 l2 = true -> list_leb l2 l1 = true -> l1 = l2.
Proof.
  intros. apply list_leb_iff in H. apply list_leb_iff in H0.
  unfold list_le in *.
  destruct H as [H | [H H']]; destruct H0 as [H0 | [H0 H0']]; try lia.
  apply list_lex_le_antisym; auto.
Qed.

Lemma list_leb_trans : forall l1 l2 l3,
  list_leb l1 l2 = true -> list_leb l2 l3 = true -> list_leb l1 l3 = true.
Proof.
  intros. apply list_leb_iff in H. apply list_leb_iff in H0.
  apply list_leb_iff. unfold list_le in *.
  destruct H as [H | [H H']]; destruct H0 as [H0 | [H0 H0']].
  - left. lia.
  - left. lia.
  - left. lia.
  - right. split; try lia. eapply list_lex_le_trans; eauto.
Qed.

Lemma list_leb_total : forall l1 l2,
  list_leb l1 l2 = true \/ list_leb l2 l1 = true.
  intros l1 l2.
  unfold list_leb.
  destruct (nat_leb (length_List l1) (length_List l2)) eqn:H1.
  - destruct (nat_leb (length_List l2) (length_List l1)) eqn:H2.
    + (* Equal lengths *)
      destruct (list_lex_leb_total l1 l2) as [H | H].
      * left. rewrite H. reflexivity.
      * right.
        apply nat_leb_le in H1. apply nat_leb_le in H2.
        assert (Hlen: length_List l1 = length_List l2) by lia.
        unfold list_leb.
        rewrite <- Hlen in *.
        replace (nat_leb (length_List l1) (length_List l1)) with true by (symmetry; apply nat_leb_refl).
        rewrite H. reflexivity.
    + (* l1 < l2 *)
      left. reflexivity.
  - (* l1 > l2 *)
    right.
    assert (H2: nat_leb (length_List l2) (length_List l1) = true).
    { apply nat_leb_le. apply nat_leb_gt in H1. lia. }
    unfold list_leb. rewrite H2.
    replace (nat_leb (length_List l1) (length_List l2)) with false by (symmetry; apply H1).
    reflexivity.
Qed.

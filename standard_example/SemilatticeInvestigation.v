From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Classes.RelationClasses.
From Posets Require Import PosetClasses.
Require Import Structure.
Require Import Proofs.

(* 
  Investigation: Is Standard Example S(n,k) a Semilattice?
  
  We check if it satisfies the property that every pair has a Greatest Lower Bound (Meet)
  or Least Upper Bound (Join).
  
  We prove that for any n >= 2 and any k, S(n,k) is neither a meet semilattice nor a join semilattice.
  Consequently, it is not a lattice.
*)

Section GeneralStandardExample.

Variable n : nat.
Variable k : nat.
Hypothesis n_ge_2 : n >= 2.

Definition Rn := StandardExampleRel n k.

(* ========================================================================== *)
(* Definitions of Compatibility                                              *)
(* ========================================================================== *)

Definition MeetSemilatticeCompatible (meet : Element -> Element -> Element) (R : Element -> Element -> Prop) : Prop :=
  forall x y, R x y <-> meet x y = x.

Definition JoinSemilatticeCompatible (join : Element -> Element -> Element) (R : Element -> Element -> Prop) : Prop :=
  forall x y, R x y <-> join x y = y.

(* Lattice compatibility: both meet and join operations *)
Definition LatticeCompatible 
  (meet join : Element -> Element -> Element) 
  (R : Element -> Element -> Prop) : Prop :=
  MeetSemilatticeCompatible meet R /\ JoinSemilatticeCompatible join R.

(* ========================================================================== *)
(* Helper Lemmas: Bounds from Semilattice Properties                         *)
(* ========================================================================== *)

Lemma join_bounds_left (join : Element -> Element -> Element) :
  IsJoinSemilattice Element join ->
  JoinSemilatticeCompatible join Rn ->
  forall x y, Rn x (join x y).
Proof.
  intros [Hassoc Hcomm Hidem] Hcompatible x y.
  apply Hcompatible.
  (* Goal: join x (join x y) = join x y *)
  rewrite <- Hassoc.
  rewrite Hidem.
  reflexivity.
Qed.

Lemma join_bounds_right (join : Element -> Element -> Element) :
  IsJoinSemilattice Element join ->
  JoinSemilatticeCompatible join Rn ->
  forall x y, Rn y (join x y).
Proof.
  intros [Hassoc Hcomm Hidem] Hcompatible x y.
  apply Hcompatible.
  (* Goal: join y (join x y) = join x y *)
  (* Use commutativity to get join (join x y) y *)
  rewrite (Hcomm y (join x y)).
  (* Now we have: join (join x y) y *)
  (* Use associativity: join x (join y y) *)
  rewrite Hassoc.
  (* Use idempotence on inner join: join x y *)
  rewrite Hidem.
  reflexivity.
Qed.

Lemma meet_bounds_left_Rn (meet : Element -> Element -> Element) :
  IsMeetSemilattice Element meet ->
  MeetSemilatticeCompatible meet Rn ->
  forall x y, Rn (meet x y) x.
Proof.
  intros [Hassoc Hcomm Hidem] Hcompatible x y.
  apply Hcompatible.
  (* meet (meet x y) x = meet x y *)
  rewrite Hassoc.
  rewrite (Hcomm y x).
  rewrite <- Hassoc.
  rewrite Hidem.
  reflexivity.
Qed.

Lemma meet_bounds_right_Rn (meet : Element -> Element -> Element) :
  IsMeetSemilattice Element meet ->
  MeetSemilatticeCompatible meet Rn ->
  forall x y, Rn (meet x y) y.
Proof.
  intros [Hassoc Hcomm Hidem] Hcompatible x y.
  apply Hcompatible.
  (* Goal: meet (meet x y) y = meet x y *)
  (* Use commutativity first to get meet y (meet x y) *)
  rewrite (Hcomm (meet x y) y).
  (* Now: meet y (meet x y) *)
  (* Use associativity: meet (meet y x) y *)
  rewrite <- Hassoc.
  (* Now: meet (meet y x) y *)
  (* Use commutativity on inner meet: meet (meet x y) y *)
  rewrite (Hcomm y x).
  (* Now: meet (meet x y) y *)
  (* Use associativity: meet x (meet y y) *)
  rewrite Hassoc.
  (* Use idempotence: meet x y *)
  rewrite Hidem.
  reflexivity.
Qed.

(* ========================================================================== *)
(* Structural Properties of S(n,k)                                           *)
(* ========================================================================== *)

(* Generalized minimality and maximality lemmas *)
Lemma Rn_minimal_A (i : nat) : 
  forall z, Rn z (A i) -> z = A i.
Proof.
  intros z H.
  inversion H; subst; auto; discriminate.
Qed.

Lemma Rn_maximal_B (j : nat) :
  forall z, Rn (B j) z -> z = B j.
Proof.
  intros z H.
  inversion H; subst; auto; discriminate.
Qed.

Lemma A0_neq_A1_gen : A 0 <> A 1.
Proof.
  intro H. inversion H.
Qed.

Lemma B0_neq_B1_gen : B 0 <> B 1.
Proof.
  intro H. inversion H.
Qed.

(* ========================================================================== *)
(* Main Disproofs                                                            *)
(* ========================================================================== *)

(* 
  Theorem: S(n,k) is NOT a Meet Semilattice.
  Proof idea: A_0 and A_1 are minimal elements. Any common lower bound must be equal to both,
  implying A_0 = A_1, which is false.
*)
Lemma Not_Meet_Semilattice_Compatible_General : 
  ~ (exists meet, IsMeetSemilattice Element meet /\ MeetSemilatticeCompatible meet Rn).
Proof.
  intro H. destruct H as [meet [Hsemilattice Hcompatible]].
  
  (* The meet of A 0 and A 1 must be a lower bound of both *)
  set (z := meet (A 0) (A 1)).
  
  (* Use our helper lemmas to establish z <= A 0 and z <= A 1 *)
  assert (Hz0 : Rn z (A 0)).
  { unfold z. apply (meet_bounds_left_Rn meet); assumption. }
  
  assert (Hz1 : Rn z (A 1)).
  { unfold z. apply (meet_bounds_right_Rn meet); assumption. }
  
  (* Since A 0 and A 1 are minimal, z must equal both *)
  apply (Rn_minimal_A 0) in Hz0.
  apply (Rn_minimal_A 1) in Hz1.
  
  (* This gives A 0 = A 1, which is a contradiction *)
  subst z.
  apply A0_neq_A1_gen.
  congruence.
Qed.

(* 
  Theorem: S(n,k) is NOT a Join Semilattice.
  Proof idea: B_0 and B_1 are maximal elements. Any common upper bound must be equal to both,
  implying B_0 = B_1, which is false.
*)
Lemma Not_Join_Semilattice_Compatible_General : 
  ~ (exists join, IsJoinSemilattice Element join /\ JoinSemilatticeCompatible join Rn).
Proof.
  intro H. destruct H as [join [Hsemilattice Hcompatible]].
  
  (* The join of B 0 and B 1 must be an upper bound of both *)
  set (z := join (B 0) (B 1)).
  
  (* Use our helper lemmas to establish B 0 <= z and B 1 <= z *)
  assert (Hz0 : Rn (B 0) z).
  { unfold z. apply (join_bounds_left join Hsemilattice). 
    unfold JoinSemilatticeCompatible in Hcompatible.
    exact Hcompatible. }
  
  assert (Hz1 : Rn (B 1) z).
  { unfold z. apply (join_bounds_right join Hsemilattice).
    unfold JoinSemilatticeCompatible in Hcompatible.
    exact Hcompatible. }
  
  (* Since B 0 and B 1 are maximal, z must equal both *)
  apply (Rn_maximal_B 0) in Hz0.
  apply (Rn_maximal_B 1) in Hz1.
  
  (* This gives B 0 = B 1, which is a contradiction *)
  subst z.
  apply B0_neq_B1_gen.
  congruence.
Qed.

(* 
  ---------------------------------------------------------------------------
  MAIN THEOREM: S(n,k) is NOT a Lattice
  ---------------------------------------------------------------------------
  
  Since S(n,k) fails to be a meet semilattice (and also fails to be a join semilattice),
  it cannot be a lattice.
*)
Theorem StandardExample_Not_Lattice :
  ~ (exists meet join, 
      exists (Hmeet : IsMeetSemilattice Element meet)
             (Hjoin : IsJoinSemilattice Element join),
      @IsLattice Element meet join Hmeet Hjoin /\
      LatticeCompatible meet join Rn).
Proof.
  intro H.
  destruct H as [meet [join [Hmeet [Hjoin [Hlattice Hcompat]]]]].
  destruct Hcompat as [Hcompat_meet Hcompat_join].
  
  (* We have a meet semilattice, which we've proven impossible *)
  apply Not_Meet_Semilattice_Compatible_General.
  exists meet.
  split; assumption.
Qed.

End GeneralStandardExample.

(* 
  Corollary: The Crown Poset S(n, 1) is not a meet semilattice for any n >= 2.
*)
Corollary Crown_Not_Meet_Semilattice (n : nat) (H : n >= 2) :
  ~ (exists meet, IsMeetSemilattice Element meet /\ MeetSemilatticeCompatible meet (CrownPoset n)).
Proof.
  apply (Not_Meet_Semilattice_Compatible_General n 1).
Qed.

(* 
  Corollary: The Crown Poset S(n, 1) is not a join semilattice for any n >= 2.
*)
Corollary Crown_Not_Join_Semilattice (n : nat) (H : n >= 2) :
  ~ (exists join, IsJoinSemilattice Element join /\ JoinSemilatticeCompatible join (CrownPoset n)).
Proof.
  apply (Not_Join_Semilattice_Compatible_General n 1).
Qed.

(* 
  Corollary: The Crown Poset S(n, 1) is not a lattice for any n >= 2.
*)
Corollary Crown_Not_Lattice (n : nat) (H : n >= 2) :
  ~ (exists meet join, 
      exists (Hmeet : IsMeetSemilattice Element meet)
             (Hjoin : IsJoinSemilattice Element join),
      @IsLattice Element meet join Hmeet Hjoin /\
      LatticeCompatible meet join (CrownPoset n)).
Proof.
  apply (StandardExample_Not_Lattice n 1).
Qed.

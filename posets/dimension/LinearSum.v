From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs.

(** The Linear Sum (also known as the Ordinal Sum) of two posets P and Q, 
    denoted P ⊕ Q, is the poset formed by taking the disjoint union of P and Q 
    and declaring every element of P to be less than every element of Q.

    Formally, for x, y ∈ P ∪ Q:
    1. If x, y ∈ P, then x ≤ y in P ⊕ Q iff x ≤ y in P.
    2. If x, y ∈ Q, then x ≤ y in P ⊕ Q iff x ≤ y in Q.
    3. If x ∈ P and y ∈ Q, then x ≤ y in P ⊕ Q.
    
    Intuition: The linear sum "stacks" Q on top of P.
    
    Dimension Property:
    One of the core results for linear sums is that dim(P ⊕ Q) = max(dim(P), dim(Q)).
    This is because no new incomparabilities are created between the summands;
    any incomparable pair in P ⊕ Q must be entirely within P or entirely within Q.
*)

Section LinearSum.
  Context {A B : Type}.
  Context (RA : A -> A -> Prop) `{IsPoset A RA}.
  Context (RB : B -> B -> Prop) `{IsPoset B RB}.

  Inductive LinearSumRel : A + B -> A + B -> Prop :=
    | SumAA : forall x y, RA x y -> LinearSumRel (inl x) (inl y)
    | SumBB : forall x y, RB x y -> LinearSumRel (inr x) (inr y)
    | SumAB : forall x y, LinearSumRel (inl x) (inr y).

  Instance LinearSum_IsPoset : IsPoset (A + B) LinearSumRel.
  Proof.
    constructor.
    - intros [x|x]; constructor; apply poset_refl.
    - intros [x1|x1] [y1|y1] H1 H2; inversion H1; inversion H2; subst; auto;
      f_equal; eapply poset_antisym; eauto.
    - intros [x1|x1] [y1|y1] [z1|z1] H1 H2; inversion H1; inversion H2; subst; constructor;
      eauto; eapply poset_trans; eauto.
  Qed.

  Theorem linear_sum_dimension :
    forall (dA dB dSum : nat),
    PosetDimension RA dA ->
    PosetDimension RB dB ->
    PosetDimension LinearSumRel dSum ->
    dSum = Init.Nat.max dA dB.
  Proof.
  Admitted.

  (** Theorem: Critical pairs of a linear sum
      (x, y) is a critical pair in A + B iff it is a critical pair in A (both in inl)
      or it is a critical pair in B (both in inr). Inter-summand pairs are comparable. *)
  Theorem linear_sum_critical_pairs :
    forall (x y : A + B),
    IsCriticalPair LinearSumRel x y <->
    (exists (a1 a2 : A), x = inl a1 /\ y = inl a2 /\ IsCriticalPair RA a1 a2) \/
    (exists (b1 b2 : B), x = inr b1 /\ y = inr b2 /\ IsCriticalPair RB b1 b2).
  Proof.
  Admitted.

  (** Realizers of a linear sum can be formed by combining linear extensions of A and B. *)
  Theorem linear_sum_realizer_lifting :
    forall (realizerA : Ensemble (A -> A -> Prop)) (realizerB : Ensemble (B -> B -> Prop)) (na nb : nat),
    IsRealizer RA realizerA ->
    IsRealizer RB realizerB ->
    cardinal (A -> A -> Prop) realizerA na ->
    cardinal (B -> B -> Prop) realizerB nb ->
    exists (realizerSum : Ensemble (A + B -> A + B -> Prop)),
    IsRealizer LinearSumRel realizerSum /\
    cardinal (A + B -> A + B -> Prop) realizerSum (Init.Nat.max na nb).
  Admitted.

End LinearSum.

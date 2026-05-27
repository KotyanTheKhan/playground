From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (i) of the second-edge cascade inside the residual handler:
    if the second strict edge is [(q, p)] then antisymmetry against
    [R2 p q] forces [p = q], contradicting [p <> q].  Routes to [False],
    so the residual realizer-existence goal follows by [exfalso]. *)
Lemma n5_dispatcher_microcase_i :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q : B)
    (Hpq_neq : p <> q)
    (HRpq : R2 p q)
    (HRqp : R2 q p),
  False.
Proof.
  intros B R2 HR2 p q Hpq_neq HRpq HRqp.
  apply Hpq_neq.
  exact (HR2.(poset_antisym) p q HRpq HRqp).
Qed.

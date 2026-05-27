(** Shared focused admit and helper imports for the n=5 dispatcher
    micro-cases.

    Extracted from [N5Dispatcher.v] so that each micro-case file can
    [Require Import] this small module instead of pulling in the entire
    dispatcher source.  The focused admit
    [n5_residual_classes_two_realizer] is the single remaining TODO for
    the n=5 non-antichain non-chain residual catch-all. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Focused (refined) admit for the n=5 non-antichain non-chain case
    EXCLUDING the single-strict-edge class.

    Captures all isomorphism classes on 5 elements that are neither
    antichain, chain, nor the one-edge class (the latter is closed by
    [n5_one_edge_two_realizer]).  The hypothesis [Hmulti] asserts that
    in addition to a chosen strict edge [(p, q)], at least one other
    off-diagonal pair is in [R2]. *)
Lemma n5_residual_classes_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 5 ->
  ~ (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, @Incomparable B R2 a b) ->
  (exists p q x y : B,
     p <> q /\ R2 p q /\
     x <> y /\ R2 x y /\ ~ (x = p /\ y = q)) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Admitted.

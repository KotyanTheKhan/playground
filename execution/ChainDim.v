From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.

Lemma chain_dim_1 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)),
    (forall x y, R x y \/ R y x) ->
    (exists a b : A, a <> b) ->
    PosetDimension R 1.
Proof.
  intros A R HR Hfin Htot Hge2.
  (* The singleton {R} is a realizer of cardinality 1. *)
  set (r := Singleton (A -> A -> Prop) R).
  assert (HrReal : IsRealizer R r).
  { constructor.
    - intros L HL. apply Singleton_inv in HL. subst L.
      constructor.
      + constructor. * exact HR. * exact Htot.
      + intros x y Hxy. exact Hxy.
    - intros x y. split.
      + intros Hxy L HL. apply Singleton_inv in HL. subst L. exact Hxy.
      + intros Hall. apply (Hall R). constructor. }
  assert (Hcard1 : cardinal _ r 1).
  { unfold r.
    replace (Singleton (A -> A -> Prop) R) with (Add (A -> A -> Prop) (Empty_set _) R).
    - apply card_add. + apply card_empty. + intro Hbad. destruct Hbad.
    - apply Extensionality_Ensembles. split.
      + intros L HL. destruct HL as [L HL | L HL]. * destruct HL. * exact HL.
      + intros L HL. right. exact HL. }
  (* Build the dimension record directly with witness realizer [r] (d = 1).
     Minimality: any realizer has cardinality >= 1, since a realizer of
     cardinality 0 would be empty and force [R] universal, contradicting the
     existence of two distinct elements. *)
  refine {|
    dimension_realizer    := r;
    dimension_is_realizer := HrReal;
    dimension_cardinality := Hcard1;
    dimension_is_minimum  := _
  |}.
  intros r' n Hr'real Hr'card.
  destruct n as [| n']; [ exfalso | lia ].
  destruct Hge2 as [a [b Hab]].
  assert (Hempty : r' = Empty_set _) by (apply cardinalO_empty; exact Hr'card).
  assert (HRab : R a b).
  { apply (proj2 (realizer_intersection Hr'real a b)).
    intros L HL. rewrite Hempty in HL. destruct HL. }
  assert (HRba : R b a).
  { apply (proj2 (realizer_intersection Hr'real b a)).
    intros L HL. rewrite Hempty in HL. destruct HL. }
  exact (Hab (poset_antisym _ _ HRab HRba)).
Qed.

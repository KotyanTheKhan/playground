(* Finite poset bundling class: IsPoset + cardinality of the full set *)

From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.

Class IsFinitePoset (A : Type) (R : A -> A -> Prop) (n : nat) := {
  fp_is_poset :> IsPoset A R;
  fp_finite   :  cardinal A (Full_set A) n
}.

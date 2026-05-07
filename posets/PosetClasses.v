(* Poset class definition *)

Class IsPoset (A : Type) (R : A -> A -> Prop) := {
  poset_refl : forall x, R x x;
  poset_antisym : forall x y, R x y -> R y x -> x = y;
  poset_trans : forall x y z, R x y -> R y z -> R x z
}.

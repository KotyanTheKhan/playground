(* Poset and Lattice class definitions *)

Class IsPoset (A : Type) (R : A -> A -> Prop) := {
  poset_refl : forall x, R x x;
  poset_antisym : forall x y, R x y -> R y x -> x = y;
  poset_trans : forall x y z, R x y -> R y z -> R x z
}.

(* ------------------------------------------------------------ *)
(* Finite Posets                                                *)
(* ------------------------------------------------------------ *)


From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------ *)
(* Semilattice-based approach only                              *)
(* ------------------------------------------------------------ *)
Class IsMeetSemilattice (A : Type) (meet : A -> A -> A) := {
  meet_assoc : forall x y z, meet (meet x y) z = meet x (meet y z);
  meet_comm  : forall x y, meet x y = meet y x;
  meet_idem  : forall x, meet x x = x
}.

Class IsJoinSemilattice (A : Type) (join : A -> A -> A) := {
  join_assoc : forall x y z, join (join x y) z = join x (join y z);
  join_comm  : forall x y, join x y = join y x;
  join_idem  : forall x, join x x = x
}.

(* Lattice via two semilattices + absorption laws *)
Class IsLattice (A : Type) (meet join : A -> A -> A)
      `{IsMeetSemilattice A meet} `{IsJoinSemilattice A join} := {
  absorption_meet : forall x y, meet x (join x y) = x;
  absorption_join : forall x y, join x (meet x y) = x
}.

Class IsDistributiveLattice (A : Type) (meet join : A -> A -> A)
      `{IsLattice A meet join} := {
  distrib_meet : forall x y z, meet x (join y z) = join (meet x y) (meet x z);
  distrib_join : forall x y z, join x (meet y z) = meet (join x y) (join x z)
}.

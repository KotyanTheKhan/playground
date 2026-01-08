(* Lattice instance for lists *)
Require Import Posets.PosetClasses.
Require Import Structure.
Require Import Operations.
Require Import Helpers.
Require Import PosetInstance.
Require Import MeetSemilatticeInstance.
Require Import JoinSemilatticeInstance.

Instance list_lattice : IsLattice List list_meet list_join.
Proof.
  constructor.
  - (* absorption_meet *)
    intros x y. unfold list_meet, list_join.
    destruct (list_leb x y) eqn:Exy.
    + rewrite Exy. reflexivity.
    + rewrite list_leb_refl. reflexivity.
  - (* absorption_join *)
    intros x y. unfold list_meet, list_join.
    destruct (list_leb x y) eqn:Exy.
    + rewrite list_leb_refl. reflexivity.
    + rewrite Exy. reflexivity.
Qed.

(* Dilworth corollaries for IsFinitePoset and the lattice class hierarchy *)

From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses LatticeClasses LatticeOrder FinitePoset.
From Dilworth Require Import Definitions DilworthTheorem.

(* ------------------------------------------------------------------ *)
(* Corollary B: Dilworth without explicit n — IsFinitePoset carries it *)
(* ------------------------------------------------------------------ *)

Section DilworthFinite.
  Context {A : Type} {R : A -> A -> Prop} {n : nat} `{IsFinitePoset A R n}.

  Corollary Dilworth_finite : forall w k,
    Width R (Full_set A) w ->
    ChainCoverNumber R (Full_set A) k ->
    w = k.
  Proof.
    intros w k Hw Hk.
    pose proof (@fp_is_poset A R n H) as Hposet.
    exact (@Dilworth A R Hposet _ w k fp_finite Hw Hk).
  Qed.
End DilworthFinite.

(* ------------------------------------------------------------------ *)
(* Corollaries A: Dilworth for each level of the lattice hierarchy     *)
(* In all three sections, the order is meet_le meet.                   *)
(* IsPoset A (meet_le meet) is resolved via meet_semilattice_is_poset. *)
(* ------------------------------------------------------------------ *)

Section DilworthMeetSemilattice.
  Context {A : Type} (meet : A -> A -> A) `{IsMeetSemilattice A meet}.

  Corollary Dilworth_meet_semilattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hn Hw Hk.
    exact (Dilworth _ n w k Hn Hw Hk).
  Qed.
End DilworthMeetSemilattice.

Section DilworthLattice.
  Context {A : Type} (meet join : A -> A -> A) `{IsLattice A meet join}.

  Corollary Dilworth_lattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hn Hw Hk.
    exact (Dilworth _ n w k Hn Hw Hk).
  Qed.
End DilworthLattice.

Section DilworthDistributiveLattice.
  Context {A : Type} (meet join : A -> A -> A) `{IsDistributiveLattice A meet join}.

  Corollary Dilworth_distributive_lattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hn Hw Hk.
    exact (Dilworth _ n w k Hn Hw Hk).
  Qed.
End DilworthDistributiveLattice.

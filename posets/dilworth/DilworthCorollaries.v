(* Dilworth corollaries for IsFinitePoset and the lattice class hierarchy *)

From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses LatticeClasses LatticeOrder FinitePoset.
From Dilworth Require Import Definitions DilworthTheorem.

(* ------------------------------------------------------------------ *)
(* Dilworth without explicit n — IsFinitePoset carries the cardinality *)
(* ------------------------------------------------------------------ *)

Section DilworthFinite.
  Context {A : Type} {R : A -> A -> Prop} {n : nat} `{H : IsFinitePoset A R n}.
  #[local] Existing Instance fp_is_poset.

  Corollary Dilworth_finite : forall w k,
    Width R (Full_set A) w ->
    ChainCoverNumber R (Full_set A) k ->
    w = k.
  Proof.
    intros w k Hw Hk.
    exact (Dilworth _ _ w k fp_finite Hw Hk).
  Qed.
End DilworthFinite.

(* Corollaries for each level of the lattice hierarchy.
   All three use meet_le as the order; the extra structure (IsLattice, IsDistributiveLattice)
   is not used by the proof. They are convenience aliases so callers with those typeclasses
   can apply Dilworth without naming the meet component explicitly. *)

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
  Context {A : Type} (meet : A -> A -> A) {join : A -> A -> A} `{IsLattice A meet join}.

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
  Context {A : Type} (meet : A -> A -> A) {join : A -> A -> A} `{IsDistributiveLattice A meet join}.

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

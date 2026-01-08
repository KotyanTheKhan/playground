From Stdlib Require Import Ensembles Finite_sets List.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.

Section CriticalPairs.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Critical Pair: an incomparable pair (x, y) such that adding (x, y) maintains transitivity *)
  Class IsCriticalPair (x y : A) : Prop := {
    critical_incomparable : Incomparable R x y;
    critical_down : forall a, Strict R a x -> R a y;
    critical_up : forall b, Strict R y b -> R x b
  }.

  (** Characterization of realizers via critical pairs *)
  Theorem critical_pair_realizer_iff :
    forall (realizer : Ensemble (A -> A -> Prop)),
    (forall L, Ensembles.In (A -> A -> Prop) realizer L -> IsLinearExtension R L) ->
    (IsRealizer R realizer <->
     (forall x y, IsCriticalPair x y -> exists L, Ensembles.In (A -> A -> Prop) realizer L /\ L y x)).
  Admitted.

  (** Every incomparable pair (x, y) contains a critical pair (x', y') 
      where x' <= x and y' >= y. *)
  Theorem incomparable_lifting_to_critical_pair :
    forall x y, Incomparable R x y ->
    exists x' y', R x' x /\ R y y' /\ IsCriticalPair x' y'.
  Admitted.

  Fixpoint check_alternating_cycle (first_x : A) (last_y : A) (pairs : list (A * A)) : Prop :=
    match pairs with
    | nil => R first_x last_y
    | cons (xi, yi) rest => R xi last_y /\ check_alternating_cycle first_x yi rest
    end.

  Definition IsAlternatingCycle (pairs : list (A * A)) : Prop :=
    match pairs with
    | nil => False
    | cons (x0, y0) rest =>
        (forall p, List.In p pairs -> IsCriticalPair (fst p) (snd p)) /\
        check_alternating_cycle x0 y0 rest
    end.

  (** Theorem: A set of critical pairs is reversible by a linear extension
      iff it contains no alternating cycles. *)
  Theorem critical_pairs_reversible_iff_no_alternating_cycle :
    forall (S : Ensemble (A * A)),
    (forall p, Ensembles.In (A * A) S p -> IsCriticalPair (fst p) (snd p)) ->
    ((exists L, IsLinearExtension R L /\ forall x y, Ensembles.In (A * A) S (x, y) -> L y x) <->
     ~ (exists cycle, (forall p, List.In p cycle -> Ensembles.In (A * A) S p) /\ IsAlternatingCycle cycle)).
  Admitted.

End CriticalPairs.

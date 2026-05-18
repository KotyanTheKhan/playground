From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.

Set Primitive Projections.

Section Definitions.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Definition of a total order *)
  Class IsTotalOrder (L : A -> A -> Prop) := {
    total_is_poset :> IsPoset A L;
    total_comparable : forall x y, L x y \/ L y x
  }.

  (** Definition of a linear extension (linearizer) *)
  Class IsLinearExtension (L : A -> A -> Prop) := {
    linear_is_total :> IsTotalOrder L;
    linear_extends : forall x y, R x y -> L x y
  }.

  (** Alias for linear extension as "Linearizer" *)
  Notation Linearizer := IsLinearExtension.

  (** Notion of Realizer: a set of linear extensions whose intersection is the poset relation *)
  Class IsRealizer (realizer : Ensemble (A -> A -> Prop)) := {
    realizer_linear : forall L, In (A -> A -> Prop) realizer L -> IsLinearExtension L;
    realizer_intersection : forall x y, R x y <-> (forall L, In (A -> A -> Prop) realizer L -> L x y)
  }.

  (** Poset Dimension: the minimum size of a realizer *)
  Class PosetDimension (d : nat) := {
    dimension_realizer : Ensemble (A -> A -> Prop);
    dimension_is_realizer : IsRealizer dimension_realizer;
    dimension_cardinality : cardinal (A -> A -> Prop) dimension_realizer d;
    dimension_is_minimum : forall r n, IsRealizer r -> cardinal (A -> A -> Prop) r n -> d <= n
  }.

  (** Incomparability in the poset *)
  Definition Incomparable (x y : A) := ~ (R x y \/ R y x).

  (** Strict order in the poset *)
  Definition Strict (x y : A) := R x y /\ x <> y.

End Definitions.

(* Make section-explicit [R] implicit on every class projection so that
   Coq 9.x dot notation [x.(field)] still works (it requires exactly one
   explicit parameter — the record value). *)
Arguments linear_is_total      {A R L} _.
Arguments linear_extends       {A R L} _ _ _ _.
Arguments realizer_linear      {A R realizer} _ _ _.
Arguments realizer_intersection {A R realizer} _ _ _.
Arguments dimension_realizer    {A R d} _.
Arguments dimension_is_realizer {A R d} _.
Arguments dimension_cardinality {A R d} _.
Arguments dimension_is_minimum  {A R d} _ _ _ _ _.

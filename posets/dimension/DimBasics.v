(** * Basic dimension facts: well-definedness, and chains have dimension <= 1.

    - [dimension_unique]: the dimension of a poset is unique (so "the dimension"
      is well-defined as a function of the relation).
    - [total_order_is_realizer] / [total_order_dim_le_1]: a total order is its
      own one-element realizer, so a chain has dimension <= 1.

    Supports index entries [dim-def] (well-definedness) and the chain case of
    [dim2-comparability] / [dim-le-width] in docs/references/dimension-index.md. *)
From Stdlib Require Import Ensembles Finite_sets Arith Lia.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs Theorems.

Section DimBasics.
  Context {A : Type}.

  (** Dimension is unique: any two dimensions of the same relation are equal. *)
  Theorem dimension_unique :
    forall (R : A -> A -> Prop) d1 d2,
      PosetDimension R d1 -> PosetDimension R d2 -> d1 = d2.
  Proof.
    intros R d1 d2 H1 H2. apply Nat.le_antisymm.
    - exact (dimension_is_minimum H1 (dimension_realizer H2) d2
               (dimension_is_realizer H2) (dimension_cardinality H2)).
    - exact (dimension_is_minimum H2 (dimension_realizer H1) d1
               (dimension_is_realizer H1) (dimension_cardinality H1)).
  Qed.

  (** A total order is its own realizer (the singleton family {R}). *)
  Lemma total_order_is_realizer :
    forall (R : A -> A -> Prop),
      IsTotalOrder R -> IsRealizer R (Singleton _ R).
  Proof.
    intros R HT.
    refine {| realizer_linear := _; realizer_intersection := _ |}.
    - intros L HL. destruct HL.
      refine {| linear_is_total := HT; linear_extends := _ |}.
      intros x y Hxy. exact Hxy.
    - intros x y. split.
      + intros Hxy L HL. destruct HL. exact Hxy.
      + intros Hall. apply (Hall R). constructor.
  Qed.

  (** A chain (total order) on a finite ground set has dimension <= 1. *)
  Theorem total_order_dim_le_1 :
    forall (R : A -> A -> Prop) `{IsPoset A R} n,
      IsTotalOrder R ->
      cardinal A (Full_set A) n ->
      exists d, inhabited (PosetDimension R d) /\ d <= 1.
  Proof.
    intros R HR n HT Hfull.
    destruct (dushnik_miller_exists R n Hfull) as [d [HD]].
    exists d. split.
    - exact (inhabits HD).
    - exact (dimension_is_minimum HD (Singleton _ R) 1
               (total_order_is_realizer R HT) (singleton_cardinal _ R)).
  Qed.

End DimBasics.

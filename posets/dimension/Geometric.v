(** * Geometric characterization of dimension.

    A realizer of [d] linear extensions is exactly a representation of [R] as the
    coordinatewise intersection of [d] chains (total orders) — i.e. an order
    embedding of [P] into a product of [d] chains. Hence:

      - [dimension_to_chain_intersection]: dim(P) = d gives such a d-chain
        representation (no finiteness needed);
      - [chain_intersection_dimension_le]: any representation of [R] as the
        intersection of [d] chains bounds the dimension, dim(P) <= d (finite P).

    Index entry: [dim-geometric] in docs/references/dimension-index.md. *)
From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs Theorems.
From ZornsLemma Require Import EnsemblesExplicit.

Section Geometric.
  Context {A : Type}.

  (** [R] is the coordinatewise intersection of the family of chains [fam]:
      every member is a total order, and [R x y] holds iff every chain orders
      [x] below [y]. This is the "embedding into a product of chains" data. *)
  Definition ChainIntersection (R : A -> A -> Prop)
                               (fam : Ensemble (A -> A -> Prop)) : Prop :=
    (forall C, In _ fam C -> IsTotalOrder C) /\
    (forall x y, R x y <-> (forall C, In _ fam C -> C x y)).

  (** Forward: a poset of dimension [d] embeds as the intersection of [d]
      chains — its realizer supplies the coordinates. *)
  Theorem dimension_to_chain_intersection :
    forall (R : A -> A -> Prop) d,
      PosetDimension R d ->
      exists fam, cardinal _ fam d /\ ChainIntersection R fam.
  Proof.
    intros R d HD.
    exists (dimension_realizer HD). split.
    - exact (dimension_cardinality HD).
    - split.
      + intros C HC.
        exact (linear_is_total
                 (realizer_linear (dimension_is_realizer HD) C HC)).
      + exact (realizer_intersection (dimension_is_realizer HD)).
  Qed.

  (** A family of chains whose intersection is [R] is a realizer of [R]:
      each chain extends [R] (since [R x y] forces every chain to order x<y). *)
  Lemma chain_intersection_is_realizer :
    forall R fam, ChainIntersection R fam -> IsRealizer R fam.
  Proof.
    intros R fam [Htot Hint].
    refine {| realizer_linear := _; realizer_intersection := Hint |}.
    intros C HC.
    refine {| linear_is_total := Htot C HC; linear_extends := _ |}.
    intros x y Hxy. exact (proj1 (Hint x y) Hxy C HC).
  Qed.

  (** Converse (finite [P]): any representation of [R] as the intersection of
      [d] chains bounds the dimension by [d]. *)
  Theorem chain_intersection_dimension_le :
    forall (R : A -> A -> Prop) `{IsPoset A R} fam d nfull,
      ChainIntersection R fam ->
      cardinal _ fam d ->
      cardinal A (Full_set A) nfull ->
      exists d', inhabited (PosetDimension R d') /\ d' <= d.
  Proof.
    intros R HR fam d nfull HCI Hcard Hfull.
    pose proof (chain_intersection_is_realizer R fam HCI) as Hreal.
    destruct (dushnik_miller_exists R nfull Hfull) as [d' [HD']].
    exists d'. split.
    - exact (inhabits HD').
    - exact (dimension_is_minimum HD' fam d Hreal Hcard).
  Qed.

End Geometric.

From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.

Section DilworthDefinitions.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* ========================================================================= *)
  (* Basic Structures                                                          *)
  (* ========================================================================= *)

  (** A chain is a set where any two elements are comparable *)
  Class IsChain (s : Ensemble A) : Prop := {
    chain_inhabited : Inhabited A s;
    chain_comparable : forall x y, In A s x -> In A s y -> R x y \/ R y x
  }.

  (** An antichain is a set where any two distinct elements are incomparable *)
  Class IsAntichain (s : Ensemble A) : Prop := {
    antichain_inhabited : Inhabited A s;
    antichain_incomparable : forall x y, In A s x -> In A s y -> (R x y \/ R y x) -> x = y
  }.

  (** A chain cover is a collection of disjoint chains that covers all elements *)
  Class IsChainCover (cover : Ensemble (Ensemble A)) : Prop := {
    chain_cover_chains : forall c, In (Ensemble A) cover c -> IsChain c;
    chain_cover_included : forall c, In (Ensemble A) cover c -> Included A c (Full_set A);
    chain_cover_covers : forall x, In A (Full_set A) x -> exists c, In (Ensemble A) cover c /\ In A c x
  }.

  (** An antichain cover is a collection of disjoint antichains that covers all elements *)
  Class IsAntichainCover (cover : Ensemble (Ensemble A)) : Prop := {
    antichain_cover_antichains : forall c, In (Ensemble A) cover c -> IsAntichain c;
    antichain_cover_included : forall c, In (Ensemble A) cover c -> Included A c (Full_set A);
    antichain_cover_covers : forall x, In A (Full_set A) x -> exists c, In (Ensemble A) cover c /\ In A c x
  }.

  (* ========================================================================= *)
  (* Optimality Conditions                                                     *)
  (* ========================================================================= *)

  (** The largest antichain in a poset *)
  Class IsLargestAntichain (la : Ensemble A) (w : nat) : Prop := {
    largest_antichain_is_antichain : IsAntichain la;
    largest_antichain_cardinality : cardinal A la w;
    largest_antichain_is_maximum : forall s n, IsAntichain s -> cardinal A s n -> n <= w
  }.

  (** The smallest chain cover in a poset *)
  Class IsSmallestChainCover (cover : Ensemble (Ensemble A)) (k : nat) : Prop := {
    smallest_cover_is_cover : IsChainCover cover;
    smallest_cover_cardinality : cardinal (Ensemble A) cover k;
    smallest_cover_is_minimum : forall cv n, IsChainCover cv -> cardinal (Ensemble A) cv n -> k <= n
  }.

  (* ========================================================================= *)
  (* Width and Chain Cover Number                                              *)
  (* ========================================================================= *)

  (** Width of a poset - size of the largest antichain *)
  Class Width (w : nat) := {
    width_la : Ensemble A;
    width_is_largest : IsLargestAntichain width_la w
  }.

  (** Chain cover number - size of the smallest chain cover *)
  Class ChainCoverNumber (k : nat) := {
    cover_number_cover : Ensemble (Ensemble A);
    cover_number_is_smallest : IsSmallestChainCover cover_number_cover k
  }.

  (* ========================================================================= *)
  (* Subposet Constructions                                                    *)
  (* ========================================================================= *)

  (** Define the "above" subposet: elements reachable from a given set *)
  Definition Above (s : Ensemble A) : Ensemble A :=
    fun x => exists y, In A s y /\ R y x.

  (** Define the "below" subposet: elements from which a given set is reachable *)
  Definition Below (s : Ensemble A) : Ensemble A :=
    fun x => exists y, In A s y /\ R x y.

End DilworthDefinitions.

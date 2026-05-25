(** * Critical-Pair Digraph Infrastructure

    The critical-pair digraph of a poset [R] has the elements of the
    underlying type as vertices, and a directed edge [x -> y] iff
    [(x, y)] is a critical pair of [R].

    This file provides the basic infrastructure (finiteness of the edge
    set, non-emptiness criterion, classical decidability) needed by
    Trotter's Theorem 6.1 in the n = 5 dispatcher.  See
    [docs/superpowers/plans/2026-05-22-close-remaining-admits.md],
    Track B Phase B1. *)

From Stdlib Require Import List Classical ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs.
(* Re-export the explicit-U Ensemble interface AFTER [CriticalPairs]
   (which itself imports Szpilrajn → implicit U).  Matches the pattern
   used elsewhere in [posets/dimension/]. *)
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section CriticalPairDigraph.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** The critical-pair digraph of [R]: directed edge [x -> y] iff
      [(x, y)] is a critical pair. *)
  Definition CP_digraph : A -> A -> Prop :=
    fun x y => IsCriticalPair R x y.

End CriticalPairDigraph.

(** ** Decidability of critical-pair membership.

    Critical pairs are defined by a [forall a, ...]/[forall b, ...]
    universally quantified body, so decidability is non-constructive.
    We use classical logic to obtain it. *)

Lemma cp_digraph_decidable :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  forall x y : A, IsCriticalPair R x y \/ ~ IsCriticalPair R x y.
Proof.
  intros A R Hpos _ x y.
  apply classic.
Qed.

(** ** Non-emptiness of the CP digraph for a non-chain poset.

    A finite poset has at least one critical pair iff it has at least
    one incomparable pair.  Forward direction: every CP is incomparable
    by definition.  Backward direction: the lifting lemma
    [incomparable_lifting_to_critical_pair]. *)

Lemma cp_digraph_nonempty_iff_incomparable :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  (exists a b : A, Incomparable R a b) <-> (exists x y : A, IsCriticalPair R x y).
Proof.
  intros A R Hpos HfinA. split.
  - (* incomparable pair -> critical pair (lifting). *)
    intros [a [b Hinc]].
    destruct (incomparable_lifting_to_critical_pair R HfinA a b Hinc)
      as [x' [y' [_ [_ Hcp]]]].
    exists x', y'. exact Hcp.
  - (* critical pair -> incomparable (immediate from the class). *)
    intros [x [y Hcp]].
    exists x, y. exact Hcp.(critical_incomparable).
Qed.

(** ** Finiteness of the CP digraph.

    For a finite poset, only finitely many pairs (x, y) exist, so the
    set of critical pairs is a finite list.  We enumerate the Cartesian
    product of the carrier with itself and use classical decidability
    to filter. *)

Section CP_digraph_finite_section.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Cartesian product of two lists, as a single list of pairs. *)
  Fixpoint list_prod (xs : list A) (ys : list A) : list (A * A) :=
    match xs with
    | nil => nil
    | x :: xs' =>
        List.map (fun y => (x, y)) ys ++ list_prod xs' ys
    end.

  Lemma list_prod_in_iff :
    forall xs ys x y,
      List.In (x, y) (list_prod xs ys) <-> List.In x xs /\ List.In y ys.
  Proof.
    induction xs as [| x0 xs IH].
    - intros ys x y. simpl. split.
      + intro Hf. destruct Hf.
      + intros [Hf _]. destruct Hf.
    - intros ys x y. simpl. split.
      + intro Hin.
        apply in_app_or in Hin. destruct Hin as [Hmap | Hrest].
        * apply in_map_iff in Hmap.
          destruct Hmap as [y0 [Heq Hy0]]. inversion Heq. subst x y0.
          split; [left; reflexivity | exact Hy0].
        * apply IH in Hrest. destruct Hrest as [Hx_in Hy_in].
          split; [right; exact Hx_in | exact Hy_in].
      + intros [Hx_in Hy_in].
        destruct Hx_in as [Heq | Hx_in].
        * subst x0. apply in_or_app. left.
          apply in_map_iff. exists y. split; [reflexivity | exact Hy_in].
        * apply in_or_app. right. apply IH. split; assumption.
  Qed.

  (** Filter a list of pairs to keep only the critical pairs.  Uses
      classical [excluded_middle_informative] to make the boolean
      decision. *)
  Fixpoint filter_cp (l : list (A * A)) : list (A * A) :=
    match l with
    | nil => nil
    | p :: rest =>
        if excluded_middle_informative (IsCriticalPair R (fst p) (snd p))
        then p :: filter_cp rest
        else filter_cp rest
    end.

  Lemma filter_cp_in_iff :
    forall l p, List.In p (filter_cp l) <->
                (List.In p l /\ IsCriticalPair R (fst p) (snd p)).
  Proof.
    induction l as [| q rest IH].
    - intro p. simpl. split.
      + intro Hf. destruct Hf.
      + intros [Hf _]. destruct Hf.
    - intro p. simpl.
      destruct (excluded_middle_informative
                  (IsCriticalPair R (fst q) (snd q))) as [Hq_cp | Hq_ncp].
      + split.
        * intro Hin. destruct Hin as [Heq | Hrest].
          { subst q. split; [left; reflexivity | exact Hq_cp]. }
          { apply IH in Hrest. destruct Hrest as [Hpl Hpcp].
            split; [right; exact Hpl | exact Hpcp]. }
        * intros [Hpl Hpcp]. destruct Hpl as [Heq | Hpl].
          { subst p. left. reflexivity. }
          { right. apply IH. split; assumption. }
      + split.
        * intro Hin. apply IH in Hin. destruct Hin as [Hpl Hpcp].
          split; [right; exact Hpl | exact Hpcp].
        * intros [Hpl Hpcp]. destruct Hpl as [Heq | Hpl].
          { subst p. exfalso. apply Hq_ncp. exact Hpcp. }
          { apply IH. split; assumption. }
  Qed.

End CP_digraph_finite_section.

Lemma cp_digraph_finite :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  exists L : list (A * A),
    forall x y, IsCriticalPair R x y <-> List.In (x, y) L.
Proof.
  intros A R Hpos HfinA.
  (* Step 1: enumerate the carrier as a list. *)
  destruct (finite_cardinal _ _ HfinA) as [n Hcard].
  destruct (cardinal_to_list A (Full_set A) n Hcard)
    as [carrier [_ [Hcarrier_iff _]]].
  (* Step 2: build the Cartesian product as a list of pairs. *)
  set (all_pairs := list_prod carrier carrier).
  (* Step 3: filter to keep only critical pairs. *)
  exists (filter_cp R all_pairs).
  intros x y. split.
  - intro Hcp.
    apply filter_cp_in_iff. split; [| simpl; exact Hcp].
    unfold all_pairs. apply list_prod_in_iff. split.
    + apply Hcarrier_iff. apply Full_intro.
    + apply Hcarrier_iff. apply Full_intro.
  - intro Hin.
    apply filter_cp_in_iff in Hin. destruct Hin as [_ Hcp].
    simpl in Hcp. exact Hcp.
Qed.

(** ** (Optional) Extremality predicate — TODO stub.

    A critical pair [(x', y')] of [R] is "extremal" (in Trotter's
    sense) if every other critical pair [(p, q)] that shares an
    endpoint with [(x', y')] in the CP digraph satisfies the
    structural condition required by Trotter's boundary argument.

    The precise structural condition (in terms of CP digraph
    successors/predecessors and boundary reversal sets) is delicate
    and is left for the phase that consumes this infrastructure.
    See [trotter_boundary_existence] in
    [posets/dimension/RemovablePairs.v] for the boundary set obligation
    this predicate is intended to support. *)

Definition IsExtremalCP {A : Type} (R : A -> A -> Prop)
                        `{IsPoset A R} (x' y' : A) : Prop :=
  IsCriticalPair R x' y' /\
  (* TODO: replace [True] with Trotter's full extremality condition. *)
  True.

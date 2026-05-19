(** Removable pairs and Trotter's lemma for the proof of Hiraguchi's theorem.
    See docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section RemovablePairs.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Residual set [Residual x y = Full_set A \ {x, y}]. *)
  Definition Residual (x y : A) : Ensemble A :=
    Setminus A (Setminus A (Full_set A) (Singleton A x)) (Singleton A y).

  Lemma Residual_not_x :
    forall x y a, In A (Residual x y) a -> a <> x.
  Proof.
    intros x y a [[_ Hnx] _] Heq. apply Hnx. rewrite Heq. constructor.
  Qed.

  Lemma Residual_not_y :
    forall x y a, In A (Residual x y) a -> a <> y.
  Proof.
    intros x y a [_ Hny] Heq. apply Hny. rewrite Heq. constructor.
  Qed.

  Lemma Residual_intro :
    forall x y a, a <> x -> a <> y -> In A (Residual x y) a.
  Proof.
    intros x y a Hnx Hny. split; [split |].
    - apply Full_intro.
    - intro Hin. inversion Hin; subst. apply Hnx; reflexivity.
    - intro Hin. inversion Hin; subst. apply Hny; reflexivity.
  Qed.

  (** A pair (x, y) is removable iff for every d'-element realizer of R
      restricted to the residual set, there exists a (d'+1)-element
      realizer of R. This is Trotter's formulation; the hard work of
      producing that extra linear extension is encapsulated in this
      property and proved (existentially) by [removable_pair_exists].

      (The previous "single-L joint-consistency" formulation was
      unsatisfiable in antichains; see git log for details.) *)
  Definition IsRemovablePair (x y : A) : Prop :=
    x <> y /\
    forall (d' : nat)
           (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop)),
      IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                     R (proj1_sig a) (proj1_sig b)) r' ->
      cardinal _ r' d' ->
      exists r : Ensemble (A -> A -> Prop),
        IsRealizer R r /\
        cardinal (A -> A -> Prop) r (d' + 1).

  (** Under the Trotter realizer-existence definition of [IsRemovablePair],
      this lemma is essentially an unfolding. *)
  Lemma removable_pair_dimension_bound :
    forall (x y : A) (d' : nat)
           (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop)),
    IsRemovablePair x y ->
    IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                   R (proj1_sig a) (proj1_sig b)) r' ->
    cardinal _ r' d' ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
  Proof.
    intros x y d' r' [_ Hrem] Hr'_real Hr'_card.
    exact (Hrem d' r' Hr'_real Hr'_card).
  Qed.

  (** When R is the discrete poset (an antichain), every distinct pair (x, y)
      is removable. Provable in principle under the new definition because
      Hiraguchi's bound is loose for antichains: [dim(antichain on n) = 2]
      (for [n ≥ 2]) and the residual realizer [r'] of size [d'] gives plenty
      of "room" — we only need to produce a realizer of [R] of size [d' + 1],
      and one of size 2 is always enough.

      NOTE — left Admitted within the warm-up time budget.

      Math sketch (clear, but Coq construction is fiddly):

        - Lift each [L' ∈ r'] to a linear extension [lift L'] of [R] on the
          full carrier, e.g., by extending [L'] (a total order on the residual
          [S']) via Szpilrajn applied to the union of [L'] (transported by
          [proj1_sig]) with [(y, x)] (and reflexivity). Call this map [lift].
        - [lift] is injective on [r'] (analogous to the argument in the old
          [removable_pair_dimension_bound]), so [Im r' lift] has cardinality
          [d'].
        - Add one further linear extension [L_extra] of [R] in which [x < y]
          (so [L_extra ≠ lift L']  for any [L'], distinguishing the new
          extension from the lifted ones).
        - The resulting [r := Add (Im r' lift) L_extra] has cardinality
          [d' + 1].
        - [r] is a realizer of [R]: for every critical pair [(p, q)] of [R]
          (which, in an antichain, is just any pair with [p ≠ q]),
            * if [p, q ∈ S']: use [r']'s realizer property on [Rsub] (still
              an antichain) to find an [L' ∈ r'] reversing [(p, q)], and the
              lifted [lift L'] reverses it on the full carrier.
            * if [p = x, q = y]: [L_extra] reverses [(x, y)] by construction.
            * if [p = y, q = x]: every [lift L'] reverses [(y, x)] by the
              choice of lift.
            * if exactly one of [p, q] is in [{x, y}]: pick [lift L'] for any
              [L' ∈ r']; the lift can be designed to place [x, y] at
              extremes relative to [S'] so that this critical pair is
              reversed.

      The last sub-case (one endpoint in [{x, y}], one in [S']) is where
      the proof needs care: the lift must be chosen consistently so that
      [x] (or [y]) is at one extreme. A more direct route is to build TWO
      [L_extra]-style extensions (one with [x < y], one with [y < x]) and
      take [Add (Add (Im r' lift) L1) L2] of cardinality [d' + 2]; that
      would give [dim(R) ≤ d' + 2], stronger than needed and easier to
      build. But the [IsRemovablePair] definition requires exactly
      [d' + 1], so we need the injective-lift + one-extra construction.

      This warm-up is left Admitted; the genuine combinatorics is in
      [removable_pair_exists] (Task 5). *)
  Lemma antichain_removable_pair :
    (forall a b : A, R a b -> a = b) ->
    forall x y : A, x <> y -> IsRemovablePair x y.
  Proof.
    intros Hdiscrete x y Hxy_neq.
    split; [exact Hxy_neq |].
    intros d' r' Hr'_real Hr'_card.
  Admitted.

End RemovablePairs.

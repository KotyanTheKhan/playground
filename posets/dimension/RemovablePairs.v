(** Removable pairs and Trotter's lemma for the proof of Hiraguchi's theorem.
    See docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn.
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

  (** A pair (x, y) is removable iff every linear extension L' of R restricted
      to the residual set lifts to a linear extension L of R that also reverses
      every critical pair of R touching {x, y} (other than (x, y) itself).

      The lift L:
        - extends L' (preserves all of L's orderings on the residual)
        - reverses the pair: L y x
        - handles every other critical pair (p, q) of R: either both endpoints
          are in the residual (so r' will handle it), or L itself reverses
          (p, q). This is the JOINT-CONSISTENCY property that the previous
          design's [extremal_critical_pair_exists] tried — and failed — to
          assert with a different (false) formulation. *)
  Definition IsRemovablePair (x y : A) : Prop :=
    x <> y /\
    forall (L' : {a : A | In A (Residual x y) a} ->
                  {a : A | In A (Residual x y) a} -> Prop),
      IsLinearExtension (fun a b => R (proj1_sig a) (proj1_sig b)) L' ->
      exists L : A -> A -> Prop,
        IsLinearExtension R L /\
        (forall (a b : {a : A | In A (Residual x y) a}),
            L' a b -> L (proj1_sig a) (proj1_sig b)) /\
        L y x /\
        (forall p q : A, IsCriticalPair R p q ->
            (p = x /\ q = y) \/
            (In A (Residual x y) p /\ In A (Residual x y) q) \/
            L q p).

End RemovablePairs.

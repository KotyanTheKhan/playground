(** * Supremum of a nat-valued function over a finite set.

    [IsLUB S f m]: m is the least upper bound (maximum; 0 over the empty set) of
    [f : A -> nat] on [S].
    - [finite_lub_exists]: an LUB exists for finite [S] (induction on cardinal).
    - [lub_unique]: the LUB is unique (antisymmetry of <=).
    - [finite_lub_unique]: hence [exists! m, IsLUB S f m] — the form needed to
      define a *deterministic* max via [constructive_definite_description], which
      is what makes the Mirsky rank recursion's step extensional ([Fix_eq]).

    Prerequisite [P1] for the Mirsky upper-bound rank function (see
    docs/superpowers/plans/2026-06-06-mirsky-upper-bound.md). *)
From Stdlib Require Import Ensembles Finite_sets Arith Lia.

Section FiniteMax.
  Context {A : Type}.

  Definition IsLUB (S : Ensemble A) (f : A -> nat) (m : nat) : Prop :=
    (forall x, In A S x -> f x <= m) /\
    (forall u, (forall x, In A S x -> f x <= u) -> m <= u).

  Lemma finite_lub_exists :
    forall (S : Ensemble A) (f : A -> nat) (k : nat),
      cardinal A S k -> exists m, IsLUB S f m.
  Proof.
    intros S f k Hc. induction Hc as [| S' k' Hc' IH x Hxnin].
    - exists 0. split.
      + intros y Hy. destruct Hy.
      + intros u _. apply Nat.le_0_l.
    - destruct IH as [m' [Hub' Hleast']].
      exists (Nat.max (f x) m'). split.
      + intros y Hy. destruct Hy as [y Hy | y Hy].
        * apply Nat.le_trans with m'; [apply Hub'; exact Hy | apply Nat.le_max_r].
        * destruct Hy. apply Nat.le_max_l.
      + intros u Hu. apply Nat.max_lub.
        * apply Hu. right. constructor.
        * apply Hleast'. intros y Hy. apply Hu. left. exact Hy.
  Qed.

  Lemma lub_unique :
    forall (S : Ensemble A) (f : A -> nat) m1 m2,
      IsLUB S f m1 -> IsLUB S f m2 -> m1 = m2.
  Proof.
    intros S f m1 m2 [Hub1 Hl1] [Hub2 Hl2].
    apply Nat.le_antisymm; [apply Hl1; exact Hub2 | apply Hl2; exact Hub1].
  Qed.

  Lemma finite_lub_unique :
    forall (S : Ensemble A) (f : A -> nat) (k : nat),
      cardinal A S k -> exists! m, IsLUB S f m.
  Proof.
    intros S f k Hc.
    destruct (finite_lub_exists S f k Hc) as [m Hm].
    exists m. split; [exact Hm | intros m' Hm'; apply (lub_unique S f m m' Hm Hm')].
  Qed.

End FiniteMax.

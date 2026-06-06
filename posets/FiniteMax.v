(** * Supremum of a nat-valued function over a finite set.

    [finite_lub_exists]: for finite [S] and [f : A -> nat] there is a least upper
    bound [m] of [f] over [S] (the maximum; 0 over the empty set). The
    least-upper-bound formulation self-determines [m] even when [S] is empty
    (leastness forces [m = 0]), avoiding an unconstrained existential witness.

    Prerequisite [P1] for the Mirsky upper-bound rank function (see
    docs/superpowers/plans/2026-06-06-mirsky-upper-bound.md). *)
From Stdlib Require Import Ensembles Finite_sets Arith Lia.

Section FiniteMax.
  Context {A : Type}.

  Lemma finite_lub_exists :
    forall (S : Ensemble A) (f : A -> nat) (k : nat),
      cardinal A S k ->
      exists m,
        (forall x, In A S x -> f x <= m) /\
        (forall u, (forall x, In A S x -> f x <= u) -> m <= u).
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

End FiniteMax.

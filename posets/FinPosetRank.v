(** * Longest-chain rank function on a finite poset (Mirsky-UB P2/L1/L2).

    [rank x] = 1 + max { rank y | y < x }, defined by well-founded recursion on
    the (well-founded) strict order [fin_strict_wf]. The recursion's step uses
    the deterministic [the_lub] over the strict down-set; [the_lub_ext] makes the
    step extensional, so the recurrence [Fix_eq] is provable.

    Delivers: [rank_eq] (the recurrence, L1), [rank_pos] (rank >= 1), and
    [rank_strict_mono] (y < x -> rank y < rank x, L2) — the latter makes the
    rank-levels antichains. See docs/superpowers/plans/2026-06-06-mirsky-upper-bound.md. *)
From Stdlib Require Import Ensembles Finite_sets Arith Lia ClassicalEpsilon.
From Posets Require Import PosetClasses FinitePoset FinPosetWF FiniteMax.

Section FinPosetRank.
  Context {A : Type} (R : A -> A -> Prop) {n : nat} `{IsFinitePoset A R n}.

  (** Recursion step: 1 + max of the recursive values over strict predecessors.
      [rec] is total-ized off the down-set so [the_lub] can consume it. *)
  Definition rank_step (x : A) (rec : forall y, StrictR R y x -> nat) : nat :=
    S (the_lub (DownStrict R x) (downstrict_finite R x)
         (fun y => match excluded_middle_informative (StrictR R y x) with
                   | left p => rec y p
                   | right _ => 0
                   end)).

  (** The step depends on [rec] only through its values on predecessors. *)
  Lemma rank_step_ext :
    forall x f g, (forall y (p : StrictR R y x), f y p = g y p) ->
                  rank_step x f = rank_step x g.
  Proof.
    intros x f g Hfg. unfold rank_step. f_equal.
    apply the_lub_ext. intros y Hy.
    destruct (excluded_middle_informative (StrictR R y x)) as [p | np].
    - apply Hfg.
    - exfalso. apply np. exact Hy.
  Qed.

  Definition rank : A -> nat := Fix (fin_strict_wf R) (fun _ => nat) rank_step.

  (** The defining recurrence (L1). *)
  Theorem rank_eq :
    forall x, rank x = S (the_lub (DownStrict R x) (downstrict_finite R x) rank).
  Proof.
    intro x. unfold rank at 1.
    rewrite (Fix_eq (fin_strict_wf R) (fun _ => nat) rank_step rank_step_ext x).
    unfold rank_step. f_equal. apply the_lub_ext. intros y Hy.
    destruct (excluded_middle_informative (StrictR R y x)) as [p | np].
    - reflexivity.
    - exfalso. apply np. exact Hy.
  Qed.

  Lemma rank_pos : forall x, 1 <= rank x.
  Proof. intro x. rewrite rank_eq. apply le_n_S, Nat.le_0_l. Qed.

  (** Strict monotonicity (L2): rank increases along the strict order. *)
  Theorem rank_strict_mono :
    forall y x, StrictR R y x -> rank y < rank x.
  Proof.
    intros y x Hyx. rewrite (rank_eq x).
    destruct (the_lub_is_lub (DownStrict R x) (downstrict_finite R x) rank) as [Hub _].
    assert (Hle : rank y <= the_lub (DownStrict R x) (downstrict_finite R x) rank)
      by (apply Hub; exact Hyx).
    lia.
  Qed.

  (** L3: comparable elements of equal rank are equal — so a rank level
      [{x | rank x = k}] is an antichain. *)
  Theorem rank_level_antichain :
    forall x y, rank x = rank y -> (R x y \/ R y x) -> x = y.
  Proof.
    intros x y Hrk Hcmp.
    destruct (classic (x = y)) as [He | Hne]; [exact He | exfalso].
    destruct Hcmp as [Hxy | Hyx].
    - pose proof (rank_strict_mono x y (conj Hxy Hne)). lia.
    - assert (Hne' : y <> x) by (intro Hc; apply Hne; symmetry; exact Hc).
      pose proof (rank_strict_mono y x (conj Hyx Hne')). lia.
  Qed.

  (** L4: height := max rank over the whole (finite) poset; every rank is below
      it. (Identifying [height] with the longest-chain length is the remaining
      step toward the full cover.) *)
  Definition height : nat := the_lub (Full_set A) (full_finite R) rank.

  Lemma rank_le_height : forall x, rank x <= height.
  Proof.
    intro x. unfold height.
    destruct (the_lub_is_lub (Full_set A) (full_finite R) rank) as [Hub _].
    apply Hub. constructor.
  Qed.

End FinPosetRank.

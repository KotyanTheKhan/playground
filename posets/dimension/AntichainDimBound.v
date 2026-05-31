(** * Hiraguchi's bound via the antichain-complement inequality

    Direct (admit-free-in-principle) route to Hiraguchi's theorem
    [dim(P) ≤ ⌊n/2⌋], replacing the dead-end removable-pair induction
    (which depends on the OPEN Removable Pair Conjecture; see
    [RemovablePairs.v] and [docs/INDEX.md]).

    Reference: W. T. Trotter, "Inequalities in dimension theory for posets",
    Proc. Amer. Math. Soc. 47 (1975) 311–316 (DOI 10.2307/2039736);
    PDF saved at docs/references/trotter-1975-inequalities-dimension.pdf.
    Survey: Trotter, "Dimension for Posets and Chromatic Number for Graphs",
    Thm 5.2 (= Hiraguchi) follows from Lemma 5.4 (dim ≤ width) + Lemma 5.6
    (dim ≤ max{2, |P − A|} for an antichain A).

    Two ingredients:
      (I)  [dimension_le_width]  — ALREADY PROVEN in [WidthBound.v].
      (II) [dim_le_antichain_complement] — Trotter's Theorem 2; the sole new
           mathematical content (proof outline below; currently admitted as a
           TRUE, bounded lemma — NOT the open conjecture).

    Combination: with [A] a maximum antichain (|A| = w = width, |P−A| = n−w),
      dim ≤ w  and  dim ≤ max{2, n−w},  and since w + (n−w) = n, one of the two
      is ≤ ⌊n/2⌋ and for n ≥ 4 the [max{2,·}] never exceeds ⌊n/2⌋. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Classical Lia.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs CriticalPairs Theorems Szpilrajn WidthBound.

Section AntichainDimBound.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** ** The arithmetic combinator (Lemma 5.4 + Lemma 5.6 ⟹ Hiraguchi).

      Pure nat arithmetic: from [d ≤ w], [d ≤ max{2,m}] and [w + m = n] with
      [n ≥ 4], conclude [d ≤ ⌊n/2⌋].

      - If [m ≥ 2]: [max{2,m} = m], so [d ≤ w] and [d ≤ m] give [2d ≤ w+m = n],
        hence [d ≤ ⌊n/2⌋].
      - If [m ≤ 1]: [max{2,m} = 2], so [d ≤ 2 ≤ ⌊n/2⌋] (as [n ≥ 4]). *)
  Lemma hiraguchi_combine :
    forall d n w m : nat,
      4 <= n -> w + m = n -> d <= w -> d <= Nat.max 2 m -> d <= n / 2.
  Proof.
    intros d n w m Hn Hsum Hdw Hdmax.
    pose proof (Nat.div_mod_eq n 2) as Hdm.
    assert (Hr : n mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
    (* lia handles Nat.max natively; n/2 and n mod 2 are tied by Hdm, Hr. *)
    lia.
  Qed.

  (** The antichain-complement bound itself (Trotter's Theorem 2,
      [dim(P) ≤ max{2, |P − Ach|}]) is proven in [AntichainComplement.v] as
      [antichain_complement_dim_bound]; this file only supplies the arithmetic
      combinator [hiraguchi_combine] used by [HiraguchiDirect.v]. *)

End AntichainDimBound.

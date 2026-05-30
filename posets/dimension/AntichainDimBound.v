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

  (** ** Lemma 5.6 / Trotter's Theorem 2 — the antichain-complement bound.

      For an antichain [Ach] in [P] with [m = |P − Ach|], [dim(P) ≤ max{2, m}].

      STATUS: TRUE, BOUNDED, classical (Trotter 1975, Thm 2; Kimble 1973).
      Currently ADMITTED as the single remaining mathematical input; this is
      NOT the open Removable Pair Conjecture (that was the previous dead end).

      PROOF OUTLINE (to formalize next; see plan
      docs/superpowers/plans/2026-05-30-hiraguchi-direct-proof.md):

      Trotter's elementary argument, by induction on [m = |P − Ach|]:

      * One-point removal  [dim(X) ≤ 1 + dim(X − x)]  for any point [x]:
        given a realizer {L₁,…,L_d} of [X − x], build d+1 linear extensions of
        [X]: keep L₁..L_{d-1} (each extended to X, preserving its order on
        X−x), then replace L_d by TWO block orders
          M_d     = [D(x) in L_d-order] < x < [(X−x)−D(x) in L_d-order]
          M_{d+1} = [(X−x)−U(x) in L_d-order] < x < [U(x) in L_d-order]
        where D(x)/U(x) are the strict down/up sets of x. These reverse every
        incomparable pair: x-vs-y pairs by M_d (x below all non-D(x)) and
        M_{d+1} (x above all non-U(x)); y-vs-y' pairs reversed by L_i (i<d) via
        M_i, and those reversed only by L_d via M_d ∪ M_{d+1} (a short case
        analysis on the D(x)/U(x) blocks — the only crossing case forces an
        R-relation, hence is vacuous).
      * Base case (Trotter Lemma 3): if [Ach] antichain and [|X − Ach| = 2]
        then [dim(X) ≤ 2] (explicit 2-realizer / finite analysis).
      * Induction: remove points of [X − Ach] one at a time (each keeps [Ach]
        an antichain and drops [|X − Ach|] by 1) down to the base case; each
        step adds ≤ 1 by one-point removal, so [dim ≤ 2 + (m − 2) = m] for
        [m ≥ 2]. For [m ≤ 1], [X] is an antichain (or antichain + 1 point),
        [dim ≤ 2]. *)
  Lemma dim_le_antichain_complement :
    forall (Ach : Ensemble A) (d m : nat),
      IsAntichain R Ach ->
      PosetDimension R d ->
      cardinal A (Setminus A (Full_set A) Ach) m ->
      d <= Nat.max 2 m.
  Proof.
  Admitted.

End AntichainDimBound.

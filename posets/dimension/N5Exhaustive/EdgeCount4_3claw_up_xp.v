(** 3-claw-up with extra parent case for [edge_count_5 = 4].

    Class 13: edges (b,a),(b,c),(b,e),(d,c).  Root b has 3 children
    (a, c, e); c has an extra parent d.
    Calls [n5_3claw_up_extra_parent_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount4_3claw_up_xp.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma three_claw_up_xp_closure :
    forall a b c d e alpha beta gamma delta eps,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      alpha <> beta -> alpha <> gamma -> alpha <> delta -> alpha <> eps ->
      beta <> gamma -> beta <> delta -> beta <> eps ->
      gamma <> delta -> gamma <> eps -> delta <> eps ->
      R2 beta alpha -> R2 beta gamma -> R2 beta eps -> R2 delta gamma ->
      forall x y, R2 x y -> x <> y ->
        (x = beta /\ y = alpha) \/
        (x = beta /\ y = gamma) \/
        (x = beta /\ y = eps) \/
        (x = delta /\ y = gamma).
  Proof.
    intros a b c d e alpha beta gamma delta eps
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
           HRba HRbc HRbe HRdc
           x y HRxy Hxy_neq.
    assert (Hsi_ba : strict_indicator R2 beta alpha = 1)
      by (apply strict_indicator_eq_1; [assumption | intro He; apply H1; symmetry; exact He]).
    assert (Hsi_bc : strict_indicator R2 beta gamma = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_be : strict_indicator R2 beta eps = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_dc : strict_indicator R2 delta gamma = 1)
      by (apply strict_indicator_eq_1; [assumption | intro He; apply H8; symmetry; exact He]).
    assert (Hsi_xy : strict_indicator R2 x y = 1)
      by (apply strict_indicator_eq_1; assumption).
    pose proof (strict_indicator_bound R2 a b).
    pose proof (strict_indicator_bound R2 b a).
    pose proof (strict_indicator_bound R2 a c).
    pose proof (strict_indicator_bound R2 c a).
    pose proof (strict_indicator_bound R2 a d).
    pose proof (strict_indicator_bound R2 d a).
    pose proof (strict_indicator_bound R2 a e).
    pose proof (strict_indicator_bound R2 e a).
    pose proof (strict_indicator_bound R2 b c).
    pose proof (strict_indicator_bound R2 c b).
    pose proof (strict_indicator_bound R2 b d).
    pose proof (strict_indicator_bound R2 d b).
    pose proof (strict_indicator_bound R2 b e).
    pose proof (strict_indicator_bound R2 e b).
    pose proof (strict_indicator_bound R2 c d).
    pose proof (strict_indicator_bound R2 d c).
    pose proof (strict_indicator_bound R2 c e).
    pose proof (strict_indicator_bound R2 e c).
    pose proof (strict_indicator_bound R2 d e).
    pose proof (strict_indicator_bound R2 e d).
    unfold edge_count_5 in Hec.
    destruct (Hcov alpha) as [Ha | [Ha | [Ha | [Ha | Ha]]]];
    destruct (Hcov beta)  as [Hb | [Hb | [Hb | [Hb | Hb]]]];
    destruct (Hcov gamma) as [Hg | [Hg | [Hg | [Hg | Hg]]]];
    destruct (Hcov delta) as [Hd | [Hd | [Hd | [Hd | Hd]]]];
    destruct (Hcov eps)   as [He | [He | [He | [He | He]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; left; split; reflexivity);
    try (right; right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_4_3claw_up_xp :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      forall (alpha beta gamma delta eps : B),
        alpha <> beta -> alpha <> gamma -> alpha <> delta -> alpha <> eps ->
        beta <> gamma -> beta <> delta -> beta <> eps ->
        gamma <> delta -> gamma <> eps -> delta <> eps ->
        R2 beta alpha -> R2 beta gamma -> R2 beta eps -> R2 delta gamma ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           alpha beta gamma delta eps
           H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
           HRba HRbc HRbe HRdc.
    apply (@n5_3claw_up_extra_parent_two_realizer B R2 HR2 Hcard).
    exists alpha, beta, gamma, delta, eps.
    repeat split; try assumption.
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (three_claw_up_xp_closure a b c d e alpha beta gamma delta eps
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
                HRba HRbc HRbe HRdc x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]]];
      subst.
    - left. split; reflexivity.
    - right; left. split; reflexivity.
    - right; right; left. split; reflexivity.
    - right; right; right. split; reflexivity.
  Qed.

End EdgeCount4_3claw_up_xp.

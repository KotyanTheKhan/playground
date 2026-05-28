(** 4-claw-up case for [edge_count_5 = 4].

    Class 11: root with 4 leaves below.  Edges r<l1, r<l2, r<l3, r<l4
    (no other edges).  Calls [n5_4claw_up_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount4_4claw_up.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma four_claw_up_closure :
    forall a b c d e r l1 l2 l3 l4,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      r <> l1 -> r <> l2 -> r <> l3 -> r <> l4 ->
      l1 <> l2 -> l1 <> l3 -> l1 <> l4 ->
      l2 <> l3 -> l2 <> l4 -> l3 <> l4 ->
      R2 r l1 -> R2 r l2 -> R2 r l3 -> R2 r l4 ->
      forall x y, R2 x y -> x <> y ->
        (x = r /\ y = l1) \/ (x = r /\ y = l2) \/
        (x = r /\ y = l3) \/ (x = r /\ y = l4).
  Proof.
    intros a b c d e r l1 l2 l3 l4
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hrl1 Hrl2 Hrl3 Hrl4 Hl12 Hl13 Hl14 Hl23 Hl24 Hl34
           HR1 HR2' HR3 HR4
           x y HRxy Hxy_neq.
    assert (Hsi1 : strict_indicator R2 r l1 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi2 : strict_indicator R2 r l2 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi3 : strict_indicator R2 r l3 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi4 : strict_indicator R2 r l4 = 1)
      by (apply strict_indicator_eq_1; assumption).
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
    destruct (Hcov r)  as [Hr | [Hr | [Hr | [Hr | Hr]]]];
    destruct (Hcov l1) as [Hl1 | [Hl1 | [Hl1 | [Hl1 | Hl1]]]];
    destruct (Hcov l2) as [Hl2 | [Hl2 | [Hl2 | [Hl2 | Hl2]]]];
    destruct (Hcov l3) as [Hl3 | [Hl3 | [Hl3 | [Hl3 | Hl3]]]];
    destruct (Hcov l4) as [Hl4 | [Hl4 | [Hl4 | [Hl4 | Hl4]]]];
    destruct (Hcov x)  as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y)  as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; left; split; reflexivity);
    try (right; right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_4_4claw_up :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      forall (r l1 l2 l3 l4 : B),
        r <> l1 -> r <> l2 -> r <> l3 -> r <> l4 ->
        l1 <> l2 -> l1 <> l3 -> l1 <> l4 ->
        l2 <> l3 -> l2 <> l4 -> l3 <> l4 ->
        R2 r l1 -> R2 r l2 -> R2 r l3 -> R2 r l4 ->
        exists rl : Ensemble (B -> B -> Prop),
          IsRealizer R2 rl /\ cardinal (B -> B -> Prop) rl 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           r l1 l2 l3 l4
           Hrl1 Hrl2 Hrl3 Hrl4 Hl12 Hl13 Hl14 Hl23 Hl24 Hl34
           HR1 HR2' HR3 HR4.
    apply (@n5_4claw_up_two_realizer B R2 HR2 Hcard).
    exists r, l1, l2, l3, l4.
    repeat split; try assumption.
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (four_claw_up_closure a b c d e r l1 l2 l3 l4
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                Hrl1 Hrl2 Hrl3 Hrl4 Hl12 Hl13 Hl14 Hl23 Hl24 Hl34
                HR1 HR2' HR3 HR4 x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]]];
      subst.
    - left. split; reflexivity.
    - right; left. split; reflexivity.
    - right; right; left. split; reflexivity.
    - right; right; right. split; reflexivity.
  Qed.

End EdgeCount4_4claw_up.

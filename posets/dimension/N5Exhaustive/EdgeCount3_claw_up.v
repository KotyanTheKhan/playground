(** 3-claw-up case for [edge_count_5 = 3].

    Given [edge_count_5 = 3] and four elements [apex, t1, t2, t3] with
    [R2 apex ti] for i=1,2,3 (all distinct), apply
    [n5_3claw_up_plus_isolated_two_realizer].  Closure: a 5^4 destruct on
    [apex, t1, t2, t3] plus 5^2 on the closure target. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount3_claw_up.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma carrier_5_pick_1_avoiding_4_local :
    forall a b c d e p q u v,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      p <> q -> p <> u -> p <> v -> q <> u -> q <> v -> u <> v ->
      exists r : B,
        r <> p /\ r <> q /\ r <> u /\ r <> v.
  Proof.
    intros a b c d e p q u v
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
           Hpq Hpu Hpv Hqu Hqv Huv.
    pose (notpquv := fun x : B => x <> p /\ x <> q /\ x <> u /\ x <> v).
    assert (Hcase : forall x, x = p \/ x = q \/ x = u \/ x = v \/ notpquv x).
    { intro x.
      destruct (classic (x = p)) as [|Hp]; [left; assumption|].
      destruct (classic (x = q)) as [|Hq]; [right; left; assumption|].
      destruct (classic (x = u)) as [|Hu]; [right; right; left; assumption|].
      destruct (classic (x = v)) as [|Hvv]; [right; right; right; left; assumption|].
      right; right; right; right. unfold notpquv. repeat split; assumption. }
    destruct (Hcase a) as [Ha|[Ha|[Ha|[Ha|Ha]]]];
    destruct (Hcase b) as [Hb|[Hb|[Hb|[Hb|Hb]]]];
    destruct (Hcase c) as [Hc|[Hc|[Hc|[Hc|Hc]]]];
    destruct (Hcase d) as [Hd|[Hd|[Hd|[Hd|Hd]]]];
    destruct (Hcase e) as [He|[He|[He|[He|He]]]];
    try (exfalso; subst; congruence);
    match goal with
    | [ Ha : notpquv ?x1 |- _ ] =>
        exists x1; unfold notpquv in *; intuition congruence
    end.
  Qed.

  Lemma claw_up_closure :
    forall a b c d e apex t1 t2 t3,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      apex <> t1 -> apex <> t2 -> apex <> t3 ->
      t1 <> t2 -> t1 <> t3 -> t2 <> t3 ->
      R2 apex t1 -> R2 apex t2 -> R2 apex t3 ->
      forall x y, R2 x y -> x <> y ->
        (x = apex /\ y = t1) \/
        (x = apex /\ y = t2) \/
        (x = apex /\ y = t3).
  Proof.
    intros a b c d e apex t1 t2 t3
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hat1 Hat2 Hat3 H12 H13 H23 HR1 HR2_ HR3
           x y HRxy Hxy_neq.
    assert (Hsi1 : strict_indicator R2 apex t1 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi2 : strict_indicator R2 apex t2 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi3 : strict_indicator R2 apex t3 = 1)
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
    destruct (Hcov apex) as [Hap | [Hap | [Hap | [Hap | Hap]]]];
    destruct (Hcov t1) as [Ht1 | [Ht1 | [Ht1 | [Ht1 | Ht1]]]];
    destruct (Hcov t2) as [Ht2 | [Ht2 | [Ht2 | [Ht2 | Ht2]]]];
    destruct (Hcov t3) as [Ht3 | [Ht3 | [Ht3 | [Ht3 | Ht3]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_3_claw_up :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      forall (apex t1 t2 t3 : B),
        apex <> t1 -> apex <> t2 -> apex <> t3 ->
        t1 <> t2 -> t1 <> t3 -> t2 <> t3 ->
        R2 apex t1 -> R2 apex t2 -> R2 apex t3 ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           apex t1 t2 t3
           Hat1 Hat2 Hat3 H12 H13 H23 HR1 HR2_ HR3.
    destruct (carrier_5_pick_1_avoiding_4_local a b c d e apex t1 t2 t3
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                Hat1 Hat2 Hat3 H12 H13 H23) as [r4 [Hra [Hrt1 [Hrt2 Hrt3]]]].
    apply (@n5_3claw_up_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists apex, t1, t2, t3, r4.
    repeat split; try assumption;
      try (intro He; symmetry in He;
           first [exact (Hat1 He) | exact (Hat2 He) | exact (Hat3 He)
                 | exact (H12 He) | exact (H13 He) | exact (H23 He)
                 | exact (Hra He) | exact (Hrt1 He) | exact (Hrt2 He)
                 | exact (Hrt3 He)]).
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (claw_up_closure a b c d e apex t1 t2 t3
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                Hat1 Hat2 Hat3 H12 H13 H23 HR1 HR2_ HR3 x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]];
      subst.
    - left. split; reflexivity.
    - right; left. split; reflexivity.
    - right; right. split; reflexivity.
  Qed.

End EdgeCount3_claw_up.

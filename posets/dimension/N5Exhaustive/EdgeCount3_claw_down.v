(** 3-claw-down case for [edge_count_5 = 3].

    Dual of 3-claw-up.  Given four elements [target, s1, s2, s3] with
    [R2 si target] for i=1,2,3 (all distinct), apply
    [n5_3claw_down_plus_isolated_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount3_claw_down.
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

  Lemma claw_down_closure :
    forall a b c d e target s1 s2 s3,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      target <> s1 -> target <> s2 -> target <> s3 ->
      s1 <> s2 -> s1 <> s3 -> s2 <> s3 ->
      R2 s1 target -> R2 s2 target -> R2 s3 target ->
      forall x y, R2 x y -> x <> y ->
        (x = s1 /\ y = target) \/
        (x = s2 /\ y = target) \/
        (x = s3 /\ y = target).
  Proof.
    intros a b c d e target s1 s2 s3
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hts1 Hts2 Hts3 H12 H13 H23 HR1 HR2_ HR3
           x y HRxy Hxy_neq.
    assert (Hsi1 : strict_indicator R2 s1 target = 1)
      by (apply strict_indicator_eq_1; [assumption | intro He; apply Hts1; symmetry; exact He]).
    assert (Hsi2 : strict_indicator R2 s2 target = 1)
      by (apply strict_indicator_eq_1; [assumption | intro He; apply Hts2; symmetry; exact He]).
    assert (Hsi3 : strict_indicator R2 s3 target = 1)
      by (apply strict_indicator_eq_1; [assumption | intro He; apply Hts3; symmetry; exact He]).
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
    destruct (Hcov target) as [Htg | [Htg | [Htg | [Htg | Htg]]]];
    destruct (Hcov s1) as [Hs1 | [Hs1 | [Hs1 | [Hs1 | Hs1]]]];
    destruct (Hcov s2) as [Hs2 | [Hs2 | [Hs2 | [Hs2 | Hs2]]]];
    destruct (Hcov s3) as [Hs3 | [Hs3 | [Hs3 | [Hs3 | Hs3]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_3_claw_down :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      forall (target s1 s2 s3 : B),
        target <> s1 -> target <> s2 -> target <> s3 ->
        s1 <> s2 -> s1 <> s3 -> s2 <> s3 ->
        R2 s1 target -> R2 s2 target -> R2 s3 target ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           target s1 s2 s3
           Hts1 Hts2 Hts3 H12 H13 H23 HR1 HR2_ HR3.
    destruct (carrier_5_pick_1_avoiding_4_local a b c d e s1 s2 s3 target
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                H12 H13 (fun He => Hts1 (eq_sym He))
                H23 (fun He => Hts2 (eq_sym He))
                (fun He => Hts3 (eq_sym He)))
      as [r4 [Hrs1 [Hrs2 [Hrs3 Hrt]]]].
    apply (@n5_3claw_down_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists s1, s2, s3, target, r4.
    repeat split; try assumption;
      try (intro He; symmetry in He;
           first [exact (Hts1 He) | exact (Hts2 He) | exact (Hts3 He)
                 | exact (H12 He) | exact (H13 He) | exact (H23 He)
                 | exact (Hrs1 He) | exact (Hrs2 He) | exact (Hrs3 He)
                 | exact (Hrt He)]).
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (claw_down_closure a b c d e target s1 s2 s3
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                Hts1 Hts2 Hts3 H12 H13 H23 HR1 HR2_ HR3 x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]];
      subst.
    - left. split; reflexivity.
    - right; left. split; reflexivity.
    - right; right. split; reflexivity.
  Qed.

End EdgeCount3_claw_down.

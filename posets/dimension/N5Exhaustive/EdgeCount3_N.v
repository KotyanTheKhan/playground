(** N-shape case for [edge_count_5 = 3].

    Given [edge_count_5 = 3] and four distinct elements [p, q, r, s] with
    [R2 p q], [R2 r q], [R2 r s], apply [n5_N_plus_isolated_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount3_N.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma carrier_5_pick_1_avoiding_4_N :
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

  Lemma N_closure :
    forall a b c d e p q r s,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      p <> q -> p <> r -> p <> s -> q <> r -> q <> s -> r <> s ->
      R2 p q -> R2 r q -> R2 r s ->
      forall x y, R2 x y -> x <> y ->
        (x = p /\ y = q) \/
        (x = r /\ y = q) \/
        (x = r /\ y = s).
  Proof.
    intros a b c d e p q r s
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hpq Hpr Hps Hqr Hqs Hrs HRpq HRrq HRrs
           x y HRxy Hxy_neq.
    assert (Hsi1 : strict_indicator R2 p q = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi2 : strict_indicator R2 r q = 1)
      by (apply strict_indicator_eq_1; [assumption | exact Hqr ||
           (intro He; apply Hqr; symmetry; exact He)]).
    assert (Hsi3 : strict_indicator R2 r s = 1)
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
    destruct (Hcov p) as [Hp | [Hp | [Hp | [Hp | Hp]]]];
    destruct (Hcov q) as [Hq | [Hq | [Hq | [Hq | Hq]]]];
    destruct (Hcov r) as [Hr | [Hr | [Hr | [Hr | Hr]]]];
    destruct (Hcov s) as [Hs | [Hs | [Hs | [Hs | Hs]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_3_N :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      forall (p q r s : B),
        p <> q -> p <> r -> p <> s -> q <> r -> q <> s -> r <> s ->
        R2 p q -> R2 r q -> R2 r s ->
        exists rl : Ensemble (B -> B -> Prop),
          IsRealizer R2 rl /\ cardinal (B -> B -> Prop) rl 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           p q r s
           Hpq Hpr Hps Hqr Hqs Hrs HRpq HRrq HRrs.
    destruct (carrier_5_pick_1_avoiding_4_N a b c d e p q r s
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                Hpq Hpr Hps Hqr Hqs Hrs) as [t [Htp [Htq [Htr Hts]]]].
    apply (@n5_N_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists p, q, r, s, t.
    repeat split; try assumption;
      try (intro He; symmetry in He;
           first [exact (Hpq He) | exact (Hpr He) | exact (Hps He)
                 | exact (Hqr He) | exact (Hqs He) | exact (Hrs He)
                 | exact (Htp He) | exact (Htq He) | exact (Htr He)
                 | exact (Hts He)]).
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (N_closure a b c d e p q r s
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                Hpq Hpr Hps Hqr Hqs Hrs HRpq HRrq HRrs x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]];
      subst.
    - left. split; reflexivity.
    - right; left. split; reflexivity.
    - right; right. split; reflexivity.
  Qed.

End EdgeCount3_N.

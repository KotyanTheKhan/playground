(** V + chain case for [edge_count_5 = 3].

    Given [edge_count_5 = 3] and five distinct elements [p, q, r, u, v]
    with [R2 p q], [R2 p r], [R2 u v], apply
    [n5_V_plus_chain_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount3_V_chain.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma V_chain_closure :
    forall a b c d e p q r u v,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      p <> q -> p <> r -> p <> u -> p <> v ->
      q <> r -> q <> u -> q <> v ->
      r <> u -> r <> v -> u <> v ->
      R2 p q -> R2 p r -> R2 u v ->
      forall x y, R2 x y -> x <> y ->
        (x = p /\ y = q) \/
        (x = p /\ y = r) \/
        (x = u /\ y = v).
  Proof.
    intros a b c d e p q r u v
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hpq Hpr Hpu Hpv Hqr Hqu Hqv Hru Hrv Huv HRpq HRpr HRuv
           x y HRxy Hxy_neq.
    assert (Hsi1 : strict_indicator R2 p q = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi2 : strict_indicator R2 p r = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi3 : strict_indicator R2 u v = 1)
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
    (* 5^7 destruct: 5 elements + (x,y).  Heavy. *)
    destruct (Hcov p) as [Hp | [Hp | [Hp | [Hp | Hp]]]];
    destruct (Hcov q) as [Hq | [Hq | [Hq | [Hq | Hq]]]];
    destruct (Hcov r) as [Hr | [Hr | [Hr | [Hr | Hr]]]];
    destruct (Hcov u) as [Hu | [Hu | [Hu | [Hu | Hu]]]];
    destruct (Hcov v) as [Hv | [Hv | [Hv | [Hv | Hv]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_3_V_chain :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      forall (p q r u v : B),
        p <> q -> p <> r -> p <> u -> p <> v ->
        q <> r -> q <> u -> q <> v ->
        r <> u -> r <> v -> u <> v ->
        R2 p q -> R2 p r -> R2 u v ->
        exists rl : Ensemble (B -> B -> Prop),
          IsRealizer R2 rl /\ cardinal (B -> B -> Prop) rl 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           p q r u v
           Hpq Hpr Hpu Hpv Hqr Hqu Hqv Hru Hrv Huv HRpq HRpr HRuv.
    apply (@n5_V_plus_chain_two_realizer B R2 HR2 Hcard).
    exists p, q, r, u, v.
    repeat split; try assumption;
      try (intro He; symmetry in He;
           first [exact (Hpq He) | exact (Hpr He) | exact (Hpu He) | exact (Hpv He)
                 | exact (Hqr He) | exact (Hqu He) | exact (Hqv He)
                 | exact (Hru He) | exact (Hrv He) | exact (Huv He)]).
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (V_chain_closure a b c d e p q r u v
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                Hpq Hpr Hpu Hpv Hqr Hqu Hqv Hru Hrv Huv HRpq HRpr HRuv
                x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]];
      subst.
    - left. split; reflexivity.
    - right; left. split; reflexivity.
    - right; right. split; reflexivity.
  Qed.

End EdgeCount3_V_chain.

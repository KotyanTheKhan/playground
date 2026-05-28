(** Chain3 + pendant-from-above case for [edge_count_5 = 4].

    Class 14: edges (a,b),(a,c),(b,c),(d,c).  Chain a<b<c with transitively-
    forced (a,c), plus a pendant d<c (vertex c has two parents).  Vertex e
    is isolated.  Calls [n5_chain3_top_pendant_plus_isolated_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount4_chain3_above.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma carrier_5_pick_1_avoiding_4_ca :
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

  Lemma chain3_above_closure :
    forall a b c d e alpha beta gamma delta,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      alpha <> beta -> alpha <> gamma -> alpha <> delta ->
      beta <> gamma -> beta <> delta -> gamma <> delta ->
      R2 alpha beta -> R2 beta gamma -> R2 delta gamma -> R2 alpha gamma ->
      forall x y, R2 x y -> x <> y ->
        (x = alpha /\ y = beta) \/
        (x = beta /\ y = gamma) \/
        (x = delta /\ y = gamma) \/
        (x = alpha /\ y = gamma).
  Proof.
    intros a b c d e alpha beta gamma delta
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hab_n Hag_n Had_n Hbg_n Hbd_n Hgd_n
           HRab HRbg HRdg HRag
           x y HRxy Hxy_neq.
    assert (Hsi_ab : strict_indicator R2 alpha beta = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_bg : strict_indicator R2 beta gamma = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_dg : strict_indicator R2 delta gamma = 1)
      by (apply strict_indicator_eq_1; [assumption | intro Heq; apply Hgd_n; symmetry; exact Heq]).
    assert (Hsi_ag : strict_indicator R2 alpha gamma = 1)
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
    destruct (Hcov alpha) as [Ha | [Ha | [Ha | [Ha | Ha]]]];
    destruct (Hcov beta)  as [Hb | [Hb | [Hb | [Hb | Hb]]]];
    destruct (Hcov gamma) as [Hg | [Hg | [Hg | [Hg | Hg]]]];
    destruct (Hcov delta) as [Hd | [Hd | [Hd | [Hd | Hd]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; left; split; reflexivity);
    try (right; right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_4_chain3_above :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      forall (alpha beta gamma delta : B),
        alpha <> beta -> alpha <> gamma -> alpha <> delta ->
        beta <> gamma -> beta <> delta -> gamma <> delta ->
        R2 alpha beta -> R2 beta gamma -> R2 delta gamma -> R2 alpha gamma ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           alpha beta gamma delta
           Hab_n Hag_n Had_n Hbg_n Hbd_n Hgd_n
           HRab HRbg HRdg HRag.
    destruct (carrier_5_pick_1_avoiding_4_ca a b c d e alpha beta gamma delta
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                Hab_n Hag_n Had_n Hbg_n Hbd_n Hgd_n)
      as [iso [Hi1 [Hi2 [Hi3 Hi4]]]].
    apply (@n5_chain3_top_pendant_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists alpha, beta, gamma, delta, iso.
    repeat split; try assumption.
    - intro He; apply Hi1; symmetry; assumption.
    - intro He; apply Hi2; symmetry; assumption.
    - intro He; apply Hi3; symmetry; assumption.
    - intro He; apply Hi4; symmetry; assumption.
    - intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
      right.
      destruct (chain3_above_closure a b c d e alpha beta gamma delta
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                  Hab_n Hag_n Had_n Hbg_n Hbd_n Hgd_n
                  HRab HRbg HRdg HRag x y HRxy Hxy_neq)
        as [[Hxa Hyb] | [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]]];
        subst.
      + left. split; reflexivity.
      + right; left. split; reflexivity.
      + right; right; left. split; reflexivity.
      + right; right; right. split; reflexivity.
  Qed.

End EdgeCount4_chain3_above.

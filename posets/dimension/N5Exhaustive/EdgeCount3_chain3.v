(** Chain3 case for [edge_count_5 = 3].

    Given [edge_count_5 = 3] and three elements [alpha, beta, gamma] forming
    a chain [alpha < beta < gamma] with the three strict edges [(alpha, beta)],
    [(beta, gamma)], [(alpha, gamma)] all present (as required by transitivity),
    apply [n5_chain3_plus_2isolated_two_realizer].  Closure is proved by a
    5^3 destruct on [alpha, beta, gamma] over {a..e}, followed by a 5^2
    destruct on the closure target. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount3_chain3.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** Pick two elements of {a..e} avoiding 3 distinct given. *)
  Lemma carrier_5_pick_2_avoiding_3_local :
    forall a b c d e p q v,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      p <> q -> p <> v -> q <> v ->
      exists r s : B,
        r <> s /\ r <> p /\ r <> q /\ r <> v /\
                  s <> p /\ s <> q /\ s <> v.
  Proof.
    intros a b c d e p q v
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
           Hpq Hpv Hqv.
    pose (notpqv := fun x : B => x <> p /\ x <> q /\ x <> v).
    assert (Hcase : forall x, x = p \/ x = q \/ x = v \/ notpqv x).
    { intro x.
      destruct (classic (x = p)) as [|Hp]; [left; assumption|].
      destruct (classic (x = q)) as [|Hq]; [right; left; assumption|].
      destruct (classic (x = v)) as [|Hvv]; [right; right; left; assumption|].
      right; right; right. unfold notpqv. repeat split; assumption. }
    destruct (Hcase a) as [Ha|[Ha|[Ha|Ha]]];
    destruct (Hcase b) as [Hb|[Hb|[Hb|Hb]]];
    destruct (Hcase c) as [Hc|[Hc|[Hc|Hc]]];
    destruct (Hcase d) as [Hd|[Hd|[Hd|Hd]]];
    destruct (Hcase e) as [He|[He|[He|He]]];
    try (exfalso; subst; congruence);
    match goal with
    | [ Ha : notpqv ?x1, Hb : notpqv ?x2 |- _ ] =>
        (first
          [ exists x1, x2; unfold notpqv in *;
            split; [|repeat split];
            (intuition congruence) ])
    end.
  Qed.

  (** Closure for chain3 case: edge_count = 3 + chain3 structure
      → no 4th strict edge. *)
  Lemma chain3_closure :
    forall a b c d e alpha beta gamma,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      alpha <> beta -> alpha <> gamma -> beta <> gamma ->
      R2 alpha beta -> R2 beta gamma -> R2 alpha gamma ->
      forall x y, R2 x y -> x <> y ->
        (x = alpha /\ y = beta) \/
        (x = beta /\ y = gamma) \/
        (x = alpha /\ y = gamma).
  Proof.
    intros a b c d e alpha beta gamma
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hab_n Hag_n Hbg_n HRab HRbg HRag
           x y HRxy Hxy_neq.
    assert (Hsi_ab : strict_indicator R2 alpha beta = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_bg : strict_indicator R2 beta gamma = 1)
      by (apply strict_indicator_eq_1; assumption).
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
    (* Destruct positions of alpha, beta, gamma, x, y over {a..e}: 5^5 = 3125 cases. *)
    destruct (Hcov alpha) as [Ha_alpha | [Ha_alpha | [Ha_alpha | [Ha_alpha | Ha_alpha]]]];
    destruct (Hcov beta)  as [Hb_beta  | [Hb_beta  | [Hb_beta  | [Hb_beta  | Hb_beta]]]];
    destruct (Hcov gamma) as [Hg_gamma | [Hg_gamma | [Hg_gamma | [Hg_gamma | Hg_gamma]]]];
    destruct (Hcov x) as [Hx_a | [Hx_b | [Hx_c | [Hx_d | Hx_e]]]];
    destruct (Hcov y) as [Hy_a | [Hy_b | [Hy_c | [Hy_d | Hy_e]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; split; reflexivity);
    try lia.
  Qed.

  (** Chain3 main dispatch. *)
  Lemma n5_edge_count_3_chain3 :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      forall (alpha beta gamma : B),
        alpha <> beta -> alpha <> gamma -> beta <> gamma ->
        R2 alpha beta -> R2 beta gamma -> R2 alpha gamma ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           alpha beta gamma
           Hab_n Hag_n Hbg_n HRab HRbg HRag.
    destruct (carrier_5_pick_2_avoiding_3_local a b c d e alpha beta gamma
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                Hab_n Hag_n Hbg_n)
      as [rr [ss [Hrs [Hra [Hrb [Hrg [Hsa [Hsb Hsg]]]]]]]].
    apply (@n5_chain3_plus_2isolated_two_realizer B R2 HR2 Hcard).
    exists alpha, beta, gamma, rr, ss.
    repeat split; try assumption;
      try (intro He; symmetry in He;
           first [exact (Hab_n He) | exact (Hag_n He) | exact (Hbg_n He)
                 | exact (Hra He) | exact (Hrb He) | exact (Hrg He)
                 | exact (Hsa He) | exact (Hsb He) | exact (Hsg He)
                 | exact (Hrs He)]).
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
    right.
    destruct (chain3_closure a b c d e alpha beta gamma
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                Hab_n Hag_n Hbg_n HRab HRbg HRag x y HRxy Hxy_neq)
      as [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]];
      subst.
    - left. split; reflexivity.
    - right; right. split; reflexivity.
    - right; left. split; reflexivity.
  Qed.

End EdgeCount3_chain3.

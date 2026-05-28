(** Bowtie K_{2,2} + isolated case for [edge_count_5 = 4].

    Given [edge_count_5 = 4] and four distinct elements [p1, p2, q1, q2]
    with edges [p1 < q1, p1 < q2, p2 < q1, p2 < q2] (bowtie), apply
    [n5_bowtie_plus_isolated_two_realizer]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount4_bowtie.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma carrier_5_pick_1_avoiding_4_bw :
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

  (** Bowtie closure: given ec=4 and the 4 bowtie edges, no 5th edge. *)
  Lemma bowtie_closure :
    forall a b c d e p1 p2 q1 q2,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      p1 <> p2 -> p1 <> q1 -> p1 <> q2 -> p2 <> q1 -> p2 <> q2 -> q1 <> q2 ->
      R2 p1 q1 -> R2 p1 q2 -> R2 p2 q1 -> R2 p2 q2 ->
      forall x y, R2 x y -> x <> y ->
        (x = p1 /\ y = q1) \/
        (x = p1 /\ y = q2) \/
        (x = p2 /\ y = q1) \/
        (x = p2 /\ y = q2).
  Proof.
    intros a b c d e p1 p2 q1 q2
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           Hp1p2 Hp1q1 Hp1q2 Hp2q1 Hp2q2 Hq1q2
           HR11 HR12 HR21 HR22
           x y HRxy Hxy_neq.
    assert (Hsi11 : strict_indicator R2 p1 q1 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi12 : strict_indicator R2 p1 q2 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi21 : strict_indicator R2 p2 q1 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi22 : strict_indicator R2 p2 q2 = 1)
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
    destruct (Hcov p1) as [Hp1 | [Hp1 | [Hp1 | [Hp1 | Hp1]]]];
    destruct (Hcov p2) as [Hp2 | [Hp2 | [Hp2 | [Hp2 | Hp2]]]];
    destruct (Hcov q1) as [Hq1 | [Hq1 | [Hq1 | [Hq1 | Hq1]]]];
    destruct (Hcov q2) as [Hq2 | [Hq2 | [Hq2 | [Hq2 | Hq2]]]];
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]];
    subst; try (exfalso; congruence);
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    try (right; right; left; split; reflexivity);
    try (right; right; right; split; reflexivity);
    try lia.
  Qed.

  Lemma n5_edge_count_4_bowtie :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 4 ->
      forall (p1 p2 q1 q2 : B),
        p1 <> p2 -> p1 <> q1 -> p1 <> q2 -> p2 <> q1 -> p2 <> q2 -> q1 <> q2 ->
        R2 p1 q1 -> R2 p1 q2 -> R2 p2 q1 -> R2 p2 q2 ->
        exists r : Ensemble (B -> B -> Prop),
          IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           p1 p2 q1 q2
           Hp1p2 Hp1q1 Hp1q2 Hp2q1 Hp2q2 Hq1q2
           HR11 HR12 HR21 HR22.
    (* Pick isolated element. *)
    destruct (carrier_5_pick_1_avoiding_4_bw a b c d e p1 p2 q1 q2
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                Hp1p2 Hp1q1 Hp1q2 Hp2q1 Hp2q2 Hq1q2)
      as [iso [Hiso1 [Hiso2 [Hiso3 Hiso4]]]].
    (* Apply bowtie_plus_isolated lemma with (a=p1, b=p2, c=q1, d=q2, e=iso). *)
    apply (@n5_bowtie_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists p1, p2, q1, q2, iso.
    repeat split; try assumption.
    - intro He; apply Hiso1; symmetry; assumption.
    - intro He; apply Hiso2; symmetry; assumption.
    - intro He; apply Hiso3; symmetry; assumption.
    - intro He; apply Hiso4; symmetry; assumption.
    - intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hxy_neq]; [left; exact Heq |].
      right.
      destruct (bowtie_closure a b c d e p1 p2 q1 q2
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                  Hp1p2 Hp1q1 Hp1q2 Hp2q1 Hp2q2 Hq1q2
                  HR11 HR12 HR21 HR22 x y HRxy Hxy_neq)
        as [[Hxa Hyb] | [[Hxa Hyb] | [[Hxa Hyb] | [Hxa Hyb]]]];
        subst.
      + left. split; reflexivity.
      + right; left. split; reflexivity.
      + right; right; left. split; reflexivity.
      + right; right; right. split; reflexivity.
  Qed.

End EdgeCount4_bowtie.

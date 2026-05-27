(** Helper: three pairwise distinct strict edges in a 5-element carrier
    imply [edge_count_5 >= 3].  This lemma is large (the destruct tree
    has 5^6 leaves) so it lives in its own file. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount.

Section EdgeCount2_ge3.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma edge_count_5_ge_3_three_edges :
    forall a b c d e x1 y1 x2 y2 x3 y3,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall z : B, z = a \/ z = b \/ z = c \/ z = d \/ z = e) ->
      R2 x1 y1 -> x1 <> y1 ->
      R2 x2 y2 -> x2 <> y2 ->
      R2 x3 y3 -> x3 <> y3 ->
      (x1 <> x2 \/ y1 <> y2) ->
      (x1 <> x3 \/ y1 <> y3) ->
      (x2 <> x3 \/ y2 <> y3) ->
      edge_count_5 R2 a b c d e >= 3.
  Proof.
    intros a b c d e x1 y1 x2 y2 x3 y3
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
           HR1 Hxy1 HR2' Hxy2 HR3 Hxy3 Hd12 Hd13 Hd23.
    assert (Hsi1 : strict_indicator R2 x1 y1 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi2 : strict_indicator R2 x2 y2 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi3 : strict_indicator R2 x3 y3 = 1)
      by (apply strict_indicator_eq_1; assumption).
    unfold edge_count_5.
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
    destruct (Hcov x1) as [Hx1a | [Hx1b | [Hx1c | [Hx1d | Hx1e]]]];
    destruct (Hcov y1) as [Hy1a | [Hy1b | [Hy1c | [Hy1d | Hy1e]]]];
    destruct (Hcov x2) as [Hx2a | [Hx2b | [Hx2c | [Hx2d | Hx2e]]]];
    destruct (Hcov y2) as [Hy2a | [Hy2b | [Hy2c | [Hy2d | Hy2e]]]];
    destruct (Hcov x3) as [Hx3a | [Hx3b | [Hx3c | [Hx3d | Hx3e]]]];
    destruct (Hcov y3) as [Hy3a | [Hy3b | [Hy3c | [Hy3d | Hy3e]]]];
    subst; try (exfalso; congruence);
    try (destruct Hd12 as [Hd | Hd]; exfalso; apply Hd; reflexivity);
    try (destruct Hd13 as [Hd | Hd]; exfalso; apply Hd; reflexivity);
    try (destruct Hd23 as [Hd | Hd]; exfalso; apply Hd; reflexivity);
    try lia.
  Qed.

End EdgeCount2_ge3.

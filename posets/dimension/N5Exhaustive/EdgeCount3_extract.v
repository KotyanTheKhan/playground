(** Extract 3 distinct strict edges from [edge_count_5 = 3].

    Follows the recipe from [EdgeCount2.edge_count_2_two_edges]:
    extract one strict edge at a time, using the "all-other-edges-equal-
    these" forcing on [edge_count_5] to peel them off. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount EdgeCount2_ge3.

Section EdgeCount3_extract.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** Step 1: from [edge_count_5 = 3] and two distinct strict edges
      [(p, q), (u, v)], extract a THIRD strict edge distinct from both. *)
  Lemma edge_count_3_third_edge :
    forall a b c d e p q u v,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      R2 p q -> p <> q ->
      R2 u v -> u <> v ->
      (p <> u \/ q <> v) ->
      exists x y : B,
        R2 x y /\ x <> y /\
        (x <> p \/ y <> q) /\
        (x <> u \/ y <> v).
  Proof.
    intros a b c d e p q u v
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           HRpq Hpq_neq HRuv Huv_neq Hdiff_pu.
    apply NNPP. intro Hno.
    (* No third distinct edge: every strict edge is (p,q) or (u,v). *)
    assert (Honly : forall x y, R2 x y -> x <> y ->
              (x = p /\ y = q) \/ (x = u /\ y = v)).
    { intros x y HRxy Hxy_neq.
      apply NNPP. intro Hno_match.
      apply Hno. exists x, y.
      apply not_or_and in Hno_match.
      destruct Hno_match as [Hno_pq Hno_uv].
      split; [exact HRxy | split; [exact Hxy_neq | split]].
      - apply not_and_or in Hno_pq. exact Hno_pq.
      - apply not_and_or in Hno_uv. exact Hno_uv. }
    (* Each of the 20 summands is one of the {(p,q), (u,v)} or
       contributes 0.  Bound the sum by 2 to contradict Hec = 3. *)
    assert (Hsi_pq : strict_indicator R2 p q = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_uv : strict_indicator R2 u v = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi_off : forall x y : B,
              ~ (x = p /\ y = q) -> ~ (x = u /\ y = v) ->
              strict_indicator R2 x y = 0).
    { intros x y Hne_pq Hne_uv. apply strict_indicator_eq_0.
      intros [HRxy Hxy_neq].
      destruct (Honly x y HRxy Hxy_neq) as [Hmpq | Hmuv].
      - apply Hne_pq. exact Hmpq.
      - apply Hne_uv. exact Hmuv. }
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
    (* Place (p, q) and (u, v) within {a..e}^2 to determine which
       summands they occupy.  Then [Hsi_off] zeros the remaining 18. *)
    assert (Hec2 : edge_count_5 R2 a b c d e <= 2).
    { unfold edge_count_5.
      destruct (Hcov p) as [Hpa | [Hpb | [Hpc | [Hpd | Hpe]]]];
      destruct (Hcov q) as [Hqa | [Hqb | [Hqc | [Hqd | Hqe]]]];
      destruct (Hcov u) as [Hua | [Hub | [Huc | [Hud | Hue]]]];
      destruct (Hcov v) as [Hva | [Hvb | [Hvc | [Hvd | Hve]]]];
      subst; try (exfalso; congruence);
      try (rewrite !Hsi_pq);
      try (rewrite !Hsi_uv);
      repeat (rewrite Hsi_off by (intros [He1 He2]; congruence));
      lia. }
    lia.
  Qed.

  (** Step 2: from [edge_count_5 = 3], extract THREE pairwise distinct
      strict edges. *)
  Lemma edge_count_3_three_edges :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      exists x1 y1 x2 y2 x3 y3 : B,
        R2 x1 y1 /\ x1 <> y1 /\
        R2 x2 y2 /\ x2 <> y2 /\
        R2 x3 y3 /\ x3 <> y3 /\
        (x1 <> x2 \/ y1 <> y2) /\
        (x1 <> x3 \/ y1 <> y3) /\
        (x2 <> x3 \/ y2 <> y3).
  Proof.
    intros a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Step A: count >= 1 gives a first edge (p1, q1). *)
    assert (Hpos : edge_count_5 R2 a b c d e >= 1) by lia.
    assert (Hnonanti : ~ (forall x y : B, R2 x y -> x = y)).
    { apply (non_antichain_iff_edge_count_pos R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov).
      exact Hpos. }
    apply not_all_ex_not in Hnonanti. destruct Hnonanti as [p Hnp].
    apply not_all_ex_not in Hnp. destruct Hnp as [q Hnq].
    assert (HRpq : R2 p q).
    { apply NNPP. intro HnR. apply Hnq. intro HR. exfalso; auto. }
    assert (Hpq_neq : p <> q).
    { intro Heq. apply Hnq. intros _. exact Heq. }
    (* Step B: from count = 3 and 1 known edge, extract a second
       distinct edge.  We adapt [edge_count_2_second_edge]: if every
       strict edge equals (p, q), then [edge_count_5] = 1.  Since we
       have count = 3 here, no such collapse occurs. *)
    assert (Hsecond : exists u v : B,
                       R2 u v /\ u <> v /\ (u <> p \/ v <> q)).
    { apply NNPP. intro Hno.
      assert (Honly : forall u v, R2 u v -> u <> v -> u = p /\ v = q).
      { intros u v HRuv Huv_neq.
        apply NNPP. intro Hno_eq.
        apply Hno. exists u, v. split; [exact HRuv | split; [exact Huv_neq |]].
        apply not_and_or in Hno_eq. destruct Hno_eq as [Hu|Hv].
        - left; exact Hu.
        - right; exact Hv. }
      assert (Hsi_pq : strict_indicator R2 p q = 1)
        by (apply strict_indicator_eq_1; assumption).
      assert (Hsi_off : forall u v : B,
                ~ (u = p /\ v = q) -> strict_indicator R2 u v = 0).
      { intros u v Hne. apply strict_indicator_eq_0.
        intros [HRuv Huv_neq]. apply Hne. apply Honly; assumption. }
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
      assert (Hec1 : edge_count_5 R2 a b c d e = 1).
      { unfold edge_count_5.
        destruct (Hcov p) as [Hpa | [Hpb | [Hpc | [Hpd | Hpe]]]];
        destruct (Hcov q) as [Hqa | [Hqb | [Hqc | [Hqd | Hqe]]]];
        subst; try (exfalso; congruence);
        rewrite Hsi_pq;
        repeat (rewrite Hsi_off by (intros [He1 He2]; congruence));
        lia. }
      lia. }
    destruct Hsecond as [u [v [HRuv [Huv_neq Hdiff_up]]]].
    assert (Hdiff_pu : p <> u \/ q <> v).
    { destruct Hdiff_up as [Hd|Hd]; [left|right]; intro He; congruence. }
    (* Step C: extract a third edge distinct from (p, q) and (u, v). *)
    destruct (edge_count_3_third_edge a b c d e p q u v
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                HRpq Hpq_neq HRuv Huv_neq Hdiff_pu)
      as [x [y [HRxy [Hxy_neq [Hdpq Hduv]]]]].
    exists p, q, u, v, x, y.
    repeat split; try assumption.
    - destruct Hdpq as [Hd|Hd]; [left|right]; intro He; congruence.
    - destruct Hduv as [Hd|Hd]; [left|right]; intro He; congruence.
  Qed.

End EdgeCount3_extract.

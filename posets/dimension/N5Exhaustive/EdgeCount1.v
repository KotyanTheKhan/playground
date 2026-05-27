(** edge_count_5 = 1 case for n=5 dispatcher.

    When [edge_count_5 R2 a b c d e = 1] over 5 pairwise distinct
    elements covering the carrier, there is exactly one strict edge
    [(p, q)] in [R2].  Apply [n5_one_edge_two_realizer] to obtain a
    2-realizer. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.

Section EdgeCount1.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** If a strict edge exists, [edge_count_5] is at least 1 on the
      summand corresponding to that ordered pair.  This is the "single
      summand pick" that lets us turn equality to 1 into uniqueness. *)
  Lemma edge_count_5_ge_pair :
    forall a b c d e x y,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall z : B, z = a \/ z = b \/ z = c \/ z = d \/ z = e) ->
      R2 x y -> x <> y ->
      strict_indicator R2 x y = 1 /\
      strict_indicator R2 x y <= edge_count_5 R2 a b c d e.
  Proof.
    intros a b c d e x y Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov HRxy Hxy_neq.
    assert (Hsi : strict_indicator R2 x y = 1)
      by (apply strict_indicator_eq_1; assumption).
    split; [exact Hsi |].
    (* Every other summand is >= 0. *)
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
    (* x and y each equal one of a, b, c, d, e; the pair (x,y) is one
       of the 20 summands.  In each branch, [Hsi] gives that summand
       equals 1, all others are >= 0, so the sum is >= 1. *)
    destruct (Hcov x) as [Hxa | [Hxb | [Hxc | [Hxd | Hxe]]]];
    destruct (Hcov y) as [Hya | [Hyb | [Hyc | [Hyd | Hye]]]];
    subst; try (exfalso; congruence); lia.
  Qed.

  (** If two distinct ordered pairs are both strict edges over a
      5-element carrier, [edge_count_5 >= 2]. *)
  Lemma edge_count_5_ge_2_two_edges :
    forall a b c d e x1 y1 x2 y2,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall z : B, z = a \/ z = b \/ z = c \/ z = d \/ z = e) ->
      R2 x1 y1 -> x1 <> y1 ->
      R2 x2 y2 -> x2 <> y2 ->
      (x1 <> x2 \/ y1 <> y2) ->
      edge_count_5 R2 a b c d e >= 2.
  Proof.
    intros a b c d e x1 y1 x2 y2
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
           HR1 Hxy1 HR2' Hxy2 Hdiff.
    assert (Hsi1 : strict_indicator R2 x1 y1 = 1)
      by (apply strict_indicator_eq_1; assumption).
    assert (Hsi2 : strict_indicator R2 x2 y2 = 1)
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
    subst; try (exfalso; congruence);
    try (destruct Hdiff as [Hd | Hd]; exfalso; apply Hd; reflexivity);
    try lia.
  Qed.

  (** Main lemma: edge count = 1 yields a 2-realizer. *)
  Lemma n5_edge_count_1_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 1 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Step 1: count >= 1 implies a strict edge exists (non-antichain). *)
    assert (Hpos : edge_count_5 R2 a b c d e >= 1) by lia.
    assert (Hnonanti : ~ (forall x y : B, R2 x y -> x = y)).
    { apply (non_antichain_iff_edge_count_pos R2 a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov).
      exact Hpos. }
    (* Extract a strict edge (p, q). *)
    apply not_all_ex_not in Hnonanti. destruct Hnonanti as [p Hnp].
    apply not_all_ex_not in Hnp. destruct Hnp as [q Hnq].
    assert (HRpq : R2 p q).
    { apply NNPP. intro HnR. apply Hnq. intro HR. exfalso; auto. }
    assert (Hpq_neq : p <> q).
    { intro Heq. apply Hnq. intros _. exact Heq. }
    (* Step 2: apply the one-edge two-realizer with witness (p, q). *)
    apply (@n5_one_edge_two_realizer B R2 HR2 Hcard).
    exists p, q.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hpq_match | Hnot_pq].
    + exact Hpq_match.
    + (* Two distinct strict edges -> edge_count >= 2, contradicting = 1. *)
      exfalso.
      assert (Hge2 : edge_count_5 R2 a b c d e >= 2).
      { apply (edge_count_5_ge_2_two_edges a b c d e p q u v
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                 HRpq Hpq_neq HRuv Hneq).
        (* (p, q) <> (u, v) as ordered pairs *)
        apply not_and_or in Hnot_pq.
        destruct Hnot_pq as [Hup | Hvq].
        - left. intro He. apply Hup. symmetry. exact He.
        - right. intro He. apply Hvq. symmetry. exact He. }
      lia.
  Qed.

End EdgeCount1.

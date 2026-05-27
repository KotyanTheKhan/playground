(** edge_count_5 = 2 case for n=5 dispatcher.

    When [edge_count_5 R2 a b c d e = 2] over 5 pairwise distinct
    elements covering the carrier, there are exactly two strict
    edges.  We classify the two edges by structure:
      - share source -> V-shape           (n5_V_plus_2isolated)
      - share target -> inverse-V (∧)     (n5_inv_V_plus_2isolated)
      - disjoint endpoints -> two 2-chains (n5_disjoint_chains_plus_isolated)
      - 2-chain (y1 = x2 or y2 = x1) -> transitivity forces a third
        strict edge, contradicting count = 2.
*)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount EdgeCount1 EdgeCount2_ge3.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount2.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** Step 1: from edge_count = 2 and an existing strict edge (p, q),
      extract a SECOND strict edge that is distinct from (p, q). *)
  Lemma edge_count_2_second_edge :
    forall a b c d e p q,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 2 ->
      R2 p q -> p <> q ->
      exists u v : B,
        R2 u v /\ u <> v /\ (u <> p \/ v <> q).
  Proof.
    intros a b c d e p q
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec HRpq Hpq_neq.
    (* Suppose every strict edge equals (p, q).  Then strict_indicator
       is 0 everywhere except at (p, q), so the edge_count is 1. *)
    apply NNPP. intro Hno.
    assert (Honly : forall u v, R2 u v -> u <> v -> u = p /\ v = q).
    { intros u v HRuv Huv_neq.
      apply NNPP. intro Hno_eq.
      apply Hno. exists u, v. split; [exact HRuv | split; [exact Huv_neq |]].
      apply not_and_or in Hno_eq. destruct Hno_eq as [Hu|Hv].
      - left; exact Hu.
      - right; exact Hv. }
    (* Build a one-edge characterization and use edge_count = 1 forcing. *)
    assert (Hsi_pq : strict_indicator R2 p q = 1)
      by (apply strict_indicator_eq_1; assumption).
    (* All summands besides the one matching (p, q) are zero. *)
    assert (Hsi_off : forall u v : B,
              ~ (u = p /\ v = q) -> strict_indicator R2 u v = 0).
    { intros u v Hne. apply strict_indicator_eq_0.
      intros [HRuv Huv_neq]. apply Hne. apply Honly; assumption. }
    (* (p, q) is exactly one of the 20 ordered pairs.  Sum = 1, but
       hypothesis says edge_count = 2. *)
    (* Bound every summand by 1 and use Hsi_off to zero out non-(p,q)
       summands.  Every summand's pair index is built from {a,b,c,d,e},
       and at most one matches (p, q). *)
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
    (* Discriminate (p, q) over {a,b,c,d,e}^2.  Once specialized,
       Hsi_pq gives the matching summand value 1; for the other 19
       summands, [Hsi_off] applies because the index pair differs. *)
    assert (Hec1 : edge_count_5 R2 a b c d e = 1).
    { unfold edge_count_5.
      destruct (Hcov p) as [Hpa | [Hpb | [Hpc | [Hpd | Hpe]]]];
      destruct (Hcov q) as [Hqa | [Hqb | [Hqc | [Hqd | Hqe]]]];
      subst; try (exfalso; congruence);
      (* In each branch, rewrite the matching summand via Hsi_pq, and
         zero out every other summand via Hsi_off.  The order matters:
         do Hsi_pq first to consume the matching pair, then Hsi_off. *)
      rewrite Hsi_pq;
      repeat (rewrite Hsi_off by (intros [He1 He2]; congruence));
      lia. }
    lia.
  Qed.

  (** Step 2: from edge_count = 2, extract TWO distinct strict edges. *)
  Lemma edge_count_2_two_edges :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 2 ->
      exists x1 y1 x2 y2 : B,
        R2 x1 y1 /\ x1 <> y1 /\
        R2 x2 y2 /\ x2 <> y2 /\
        (x1 <> x2 \/ y1 <> y2).
  Proof.
    intros a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Step 1: edge_count >= 1 -> a strict edge exists. *)
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
    destruct (edge_count_2_second_edge a b c d e p q
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                HRpq Hpq_neq)
      as [u [v [HRuv [Huv_neq Hdiff]]]].
    exists p, q, u, v.
    repeat split; try assumption.
    destruct Hdiff as [Hu|Hv]; [left|right]; intro He; congruence.
  Qed.

  (** Step 3: with edge_count = 2 and two strict edges (p,q), (u,v),
      EVERY strict edge equals (p,q) or (u,v). *)
  Lemma edge_count_2_only_two :
    forall a b c d e p q u v,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 2 ->
      R2 p q -> p <> q ->
      R2 u v -> u <> v ->
      (p <> u \/ q <> v) ->
      forall x y, R2 x y -> x <> y ->
        (x = p /\ y = q) \/ (x = u /\ y = v).
  Proof.
    intros a b c d e p q u v
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           HRpq Hpq_neq HRuv Huv_neq Hdiff_pu x y HRxy Hxy_neq.
    apply NNPP. intro Hno.
    apply not_or_and in Hno. destruct Hno as [Hno1 Hno2].
    (* x, y is a third distinct edge from (p,q) and (u,v). *)
    assert (Hd_xp_pq : p <> x \/ q <> y).
    { apply not_and_or in Hno1. destruct Hno1 as [Hn|Hn];
        [left; intro He; apply Hn; symmetry; exact He
        |right; intro He; apply Hn; symmetry; exact He]. }
    assert (Hd_xu_uv : u <> x \/ v <> y).
    { apply not_and_or in Hno2. destruct Hno2 as [Hn|Hn];
        [left; intro He; apply Hn; symmetry; exact He
        |right; intro He; apply Hn; symmetry; exact He]. }
    assert (Hge3 : edge_count_5 R2 a b c d e >= 3).
    { apply (edge_count_5_ge_3_three_edges R2 a b c d e p q u v x y
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
               HRpq Hpq_neq HRuv Huv_neq HRxy Hxy_neq
               Hdiff_pu Hd_xp_pq Hd_xu_uv). }
    lia.
  Qed.

  (** Pick two distinct elements of a 5-element carrier that are all
      distinct from three given (distinct) elements. *)
  Lemma carrier_5_pick_2_avoiding_3 :
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
    (* For each element of {a, b, c, d, e}, determine whether it
       equals p, q, or v.  At most 3 of the 5 elements can match
       p, q, v (since p, q, v are pairwise distinct), so at least
       2 are different from all three. *)
    (* Enumerate.  For each element x of {a,b,c,d,e}, define a
       "category" 0..3 (0 = matches p, 1 = matches q, 2 = matches v,
       3 = matches none).  By pigeonhole, two have category 3. *)
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
    (* If three or more elements share the same {p,q,v} category, two
       of them are equal -> contradiction. *)
    try (exfalso; subst; congruence);
    (* Pick the two "category 3" (notpqv) elements. *)
    match goal with
    | [ Ha : notpqv ?x1, Hb : notpqv ?x2 |- _ ] =>
        (first
          [ exists x1, x2; unfold notpqv in *;
            split; [|repeat split];
            (intuition congruence) ])
    end.
  Qed.

  (** Pick one element of a 5-element carrier that is distinct from
      four given (pairwise distinct) elements. *)
  Lemma carrier_5_pick_1_avoiding_4 :
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

  (** Main lemma: edge_count = 2 yields a 2-realizer. *)
  Lemma n5_edge_count_2_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 2 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    (* Extract two distinct strict edges. *)
    destruct (edge_count_2_two_edges a b c d e
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec)
      as [p [q [u [v [HRpq [Hpq_neq [HRuv [Huv_neq Hdiff]]]]]]]].
    (* Closure: every strict edge is (p,q) or (u,v). *)
    assert (Hdiff_pu : p <> u \/ q <> v).
    { destruct Hdiff as [Hxx|Hyy]; [left|right]; exact Hxx || exact Hyy. }
    assert (Honly : forall x y, R2 x y -> x <> y ->
              (x = p /\ y = q) \/ (x = u /\ y = v))
      by exact (edge_count_2_only_two a b c d e p q u v
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                  HRpq Hpq_neq HRuv Huv_neq Hdiff_pu).
    (* Case-split on structure of the 2 edges. *)
    destruct (classic (p = u)) as [Hpu_eq | Hpu_neq].
    { (* V-shape: edges (p, q) and (p, v). *)
      subst u.
      assert (Hqv_neq : q <> v).
      { intro He. apply Hpq_neq. (* p=u (now u=p), q=v, but (p,q)<>(u,v)=(p,v) requires q<>v *)
        destruct Hdiff_pu as [Hd|Hd]; [contradiction Hd; reflexivity| contradiction Hd; assumption]. }
      assert (Hpv_neq : p <> v) by assumption.
      (* Pick 2 elements r, s avoiding {p, q, v}. *)
      destruct (carrier_5_pick_2_avoiding_3 a b c d e p q v
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                  Hpq_neq Hpv_neq Hqv_neq)
        as [r [s [Hrs_neq [Hrp [Hrq [Hrv [Hsp [Hsq Hsv]]]]]]]].
      apply (@n5_V_plus_2isolated_two_realizer B R2 HR2 Hcard).
      exists p, q, v, r, s.
      repeat split; try assumption.
      - intro He; apply Hrp; symmetry; assumption.
      - intro He; apply Hsp; symmetry; assumption.
      - intro He; apply Hrq; symmetry; assumption.
      - intro He; apply Hsq; symmetry; assumption.
      - intro He; apply Hrv; symmetry; assumption.
      - intro He; apply Hsv; symmetry; assumption.
      - (* uniqueness clause *)
        intros x y HRxy.
        destruct (classic (x = y)) as [|Hxy_neq]; [left; assumption|].
        right.
        destruct (Honly x y HRxy Hxy_neq) as [[Hxp Hyq]|[Hxp Hyv]];
          subst; [left|right]; split; reflexivity. }
    destruct (classic (q = v)) as [Hqv_eq | Hqv_neq].
    { (* Inverse-V (∧): edges (p, q) and (u, q). *)
      subst v.
      assert (Hpq_neq' : p <> q) by assumption.
      assert (Huq_neq : u <> q) by assumption.
      destruct (carrier_5_pick_2_avoiding_3 a b c d e p u q
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                  Hpu_neq Hpq_neq' Huq_neq)
        as [r [s [Hrs_neq [Hrp [Hru [Hrq [Hsp [Hsu Hsq]]]]]]]].
      apply (@n5_inv_V_plus_2isolated_two_realizer B R2 HR2 Hcard).
      exists p, u, q, r, s.
      repeat split; try assumption.
      - intro He; apply Hrp; symmetry; assumption.
      - intro He; apply Hsp; symmetry; assumption.
      - intro He; apply Hru; symmetry; assumption.
      - intro He; apply Hsu; symmetry; assumption.
      - intro He; apply Hrq; symmetry; assumption.
      - intro He; apply Hsq; symmetry; assumption.
      - intros x y HRxy.
        destruct (classic (x = y)) as [|Hxy_neq]; [left; assumption|].
        right.
        destruct (Honly x y HRxy Hxy_neq) as [[Hxp Hyq]|[Hxu Hyq]];
          subst; [left|right]; split; reflexivity. }
    destruct (classic (q = u)) as [Hqu_eq | Hqu_neq].
    { (* Forward 2-chain: R2 p q, R2 q v -> R2 p v.  Yields 3rd edge. *)
      exfalso.
      subst u.
      assert (HRpv : R2 p v).
      { apply (poset_trans p q v); assumption. }
      assert (Hpv_neq : p <> v).
      { intro Heq. subst v.
        (* Now R2 p q and R2 q p, so p = q by antisym. *)
        apply Hpq_neq. apply (poset_antisym _ _ HRpq HRuv). }
      (* (p, v) is a strict edge.  By Honly, it equals (p, q) or (q, v). *)
      destruct (Honly p v HRpv Hpv_neq) as [[_ Hvq]|[Hpq2 _]].
      - (* v = q contradicts q <> v *)
        apply Hqv_neq. symmetry. assumption.
      - (* p = q contradicts p <> q *)
        apply Hpq_neq. assumption. }
    destruct (classic (p = v)) as [Hpv_eq | Hpv_neq].
    { (* Backward 2-chain: R2 u p, R2 p q -> R2 u q. *)
      exfalso.
      subst v.
      assert (HRuq : R2 u q).
      { apply (poset_trans u p q); assumption. }
      assert (Huq_neq : u <> q).
      { intro Heq. subst q.
        apply Huv_neq. apply (poset_antisym _ _ HRuv HRpq). }
      destruct (Honly u q HRuq Huq_neq) as [[Hup _]|[_ Hqp]].
      - apply Hpu_neq. symmetry. assumption.
      - apply Hqv_neq. assumption. }
    (* Otherwise: all 4 elements distinct.  Disjoint chains. *)
    (* p, q, u, v pairwise distinct: p<>q, u<>v, p<>u, q<>v, q<>u, p<>v. *)
    destruct (carrier_5_pick_1_avoiding_4 a b c d e p q u v
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov
                Hpq_neq Hpu_neq Hpv_neq Hqu_neq Hqv_neq Huv_neq)
      as [w [Hwp [Hwq [Hwu Hwv]]]].
    apply (@n5_disjoint_chains_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists p, q, u, v, w.
    repeat split; try assumption.
    - intro He; apply Hwp; symmetry; assumption.
    - intro He; apply Hwq; symmetry; assumption.
    - intro He; apply Hwu; symmetry; assumption.
    - intro He; apply Hwv; symmetry; assumption.
    - intros x y HRxy.
      destruct (classic (x = y)) as [|Hxy_neq]; [left; assumption|].
      right.
      destruct (Honly x y HRxy Hxy_neq) as [[Hxp Hyq]|[Hxu Hyv]];
        subst; [left|right]; split; reflexivity.
  Qed.

End EdgeCount2.

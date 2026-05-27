(* Edge counter for 5-element posets.

   Defines a boolean strict_indicator and a count of strict edges
   over the 20 ordered pairs of 5 (distinct) elements. Establishes
   the basic bounds:
     - strict_indicator x y <= 1
     - edge_count_5 ... <= 20
     - strict_indicator x y + strict_indicator y x <= 1 (when x <> y)
     - edge_count_5 ... <= 10 (when all 5 elements distinct)
     - non-antichain <-> edge_count_5 >= 1
*)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.

Section EdgeCount.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{IsPoset B R2}.

  (** Boolean indicator for "(x, y) is a strict edge". *)
  Definition strict_indicator (x y : B) : nat :=
    if excluded_middle_informative (R2 x y /\ x <> y) then 1 else 0.

  (** Count strict edges among 20 ordered pairs of 5 distinct elements. *)
  Definition edge_count_5 (a b c d e : B) : nat :=
    strict_indicator a b + strict_indicator b a +
    strict_indicator a c + strict_indicator c a +
    strict_indicator a d + strict_indicator d a +
    strict_indicator a e + strict_indicator e a +
    strict_indicator b c + strict_indicator c b +
    strict_indicator b d + strict_indicator d b +
    strict_indicator b e + strict_indicator e b +
    strict_indicator c d + strict_indicator d c +
    strict_indicator c e + strict_indicator e c +
    strict_indicator d e + strict_indicator e d.

  (** [strict_indicator] is in [{0, 1}]. *)
  Lemma strict_indicator_bound :
    forall x y, strict_indicator x y <= 1.
  Proof.
    intros x y. unfold strict_indicator.
    destruct (excluded_middle_informative (R2 x y /\ x <> y)); lia.
  Qed.

  (** Edge count is bounded by 20. *)
  Lemma edge_count_5_le_20 :
    forall a b c d e, edge_count_5 a b c d e <= 20.
  Proof.
    intros a b c d e. unfold edge_count_5.
    pose proof (strict_indicator_bound a b).
    pose proof (strict_indicator_bound b a).
    pose proof (strict_indicator_bound a c).
    pose proof (strict_indicator_bound c a).
    pose proof (strict_indicator_bound a d).
    pose proof (strict_indicator_bound d a).
    pose proof (strict_indicator_bound a e).
    pose proof (strict_indicator_bound e a).
    pose proof (strict_indicator_bound b c).
    pose proof (strict_indicator_bound c b).
    pose proof (strict_indicator_bound b d).
    pose proof (strict_indicator_bound d b).
    pose proof (strict_indicator_bound b e).
    pose proof (strict_indicator_bound e b).
    pose proof (strict_indicator_bound c d).
    pose proof (strict_indicator_bound d c).
    pose proof (strict_indicator_bound c e).
    pose proof (strict_indicator_bound e c).
    pose proof (strict_indicator_bound d e).
    pose proof (strict_indicator_bound e d).
    lia.
  Qed.

  (** Antisymmetry: a strict edge in one direction excludes the other. *)
  Lemma strict_indicator_antisym :
    forall x y, x <> y -> strict_indicator x y + strict_indicator y x <= 1.
  Proof.
    intros x y Hxy. unfold strict_indicator.
    destruct (excluded_middle_informative (R2 x y /\ x <> y)) as [Hxy_strict|];
    destruct (excluded_middle_informative (R2 y x /\ y <> x)) as [Hyx_strict|];
    try lia.
    (* both directions are strict edges — contradiction via antisym *)
    destruct Hxy_strict as [HRxy _].
    destruct Hyx_strict as [HRyx _].
    exfalso. apply Hxy. apply (poset_antisym _ _ HRxy HRyx).
  Qed.

  (** With antisymmetry, edge count <= 10 (all 5 elements distinct). *)
  Lemma edge_count_5_le_10 :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
    edge_count_5 a b c d e <= 10.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde.
    unfold edge_count_5.
    pose proof (strict_indicator_antisym a b Hab).
    pose proof (strict_indicator_antisym a c Hac).
    pose proof (strict_indicator_antisym a d Had).
    pose proof (strict_indicator_antisym a e Hae).
    pose proof (strict_indicator_antisym b c Hbc).
    pose proof (strict_indicator_antisym b d Hbd).
    pose proof (strict_indicator_antisym b e Hbe).
    pose proof (strict_indicator_antisym c d Hcd).
    pose proof (strict_indicator_antisym c e Hce).
    pose proof (strict_indicator_antisym d e Hde).
    lia.
  Qed.

  (** Helper: an "is-strict-edge" predicate matches strict_indicator = 1. *)
  Lemma strict_indicator_eq_1 :
    forall x y, R2 x y -> x <> y -> strict_indicator x y = 1.
  Proof.
    intros x y HR Hneq. unfold strict_indicator.
    destruct (excluded_middle_informative (R2 x y /\ x <> y)) as [|Hno].
    - reflexivity.
    - exfalso. apply Hno. split; assumption.
  Qed.

  Lemma strict_indicator_eq_0 :
    forall x y, ~ (R2 x y /\ x <> y) -> strict_indicator x y = 0.
  Proof.
    intros x y Hno. unfold strict_indicator.
    destruct (excluded_middle_informative (R2 x y /\ x <> y)) as [Hyes|].
    - exfalso. apply Hno. exact Hyes.
    - reflexivity.
  Qed.

  (** Non-antichain -> edge count >= 1. *)
  Lemma non_antichain_iff_edge_count_pos :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      (~ (forall x y : B, R2 x y -> x = y)) <-> edge_count_5 a b c d e >= 1.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov.
    split.
    - (* non-antichain -> some strict edge -> count >= 1 *)
      intros Hna.
      apply not_all_ex_not in Hna. destruct Hna as [x Hnx].
      apply not_all_ex_not in Hnx. destruct Hnx as [y Hny].
      (* From Hny : ~ (R2 x y -> x = y), get R2 x y /\ x <> y *)
      assert (HRxy : R2 x y).
      { apply NNPP. intro HnR. apply Hny. intro HR. exfalso; auto. }
      assert (Hxy_neq : x <> y).
      { intro Heq. apply Hny. intros _. exact Heq. }
      (* x, y in {a, b, c, d, e}: show some strict_indicator is 1. *)
      assert (Hsi : strict_indicator x y = 1) by (apply strict_indicator_eq_1; assumption).
      unfold edge_count_5.
      destruct (Hcov x) as [Hxa | [Hxb | [Hxc | [Hxd | Hxe]]]];
      destruct (Hcov y) as [Hya | [Hyb | [Hyc | [Hyd | Hye]]]];
      subst; try (exfalso; congruence);
      (* now rewrite the matching strict_indicator with Hsi and bound the rest *)
      pose proof (strict_indicator_bound a b) as Hsab;
      pose proof (strict_indicator_bound b a) as Hsba;
      pose proof (strict_indicator_bound a c) as Hsac;
      pose proof (strict_indicator_bound c a) as Hsca;
      pose proof (strict_indicator_bound a d) as Hsad;
      pose proof (strict_indicator_bound d a) as Hsda;
      pose proof (strict_indicator_bound a e) as Hsae;
      pose proof (strict_indicator_bound e a) as Hsea;
      pose proof (strict_indicator_bound b c) as Hsbc;
      pose proof (strict_indicator_bound c b) as Hscb;
      pose proof (strict_indicator_bound b d) as Hsbd;
      pose proof (strict_indicator_bound d b) as Hsdb;
      pose proof (strict_indicator_bound b e) as Hsbe;
      pose proof (strict_indicator_bound e b) as Hseb;
      pose proof (strict_indicator_bound c d) as Hscd;
      pose proof (strict_indicator_bound d c) as Hsdc;
      pose proof (strict_indicator_bound c e) as Hsce;
      pose proof (strict_indicator_bound e c) as Hsec;
      pose proof (strict_indicator_bound d e) as Hsde;
      pose proof (strict_indicator_bound e d) as Hsed;
      lia.
    - (* count >= 1 -> some strict_indicator is 1 -> some R2 x y with x <> y *)
      intros Hpos Hanti.
      (* Goal: derive contradiction. Every strict_indicator must be 0 under Hanti. *)
      assert (Hall0 : forall u v, strict_indicator u v = 0).
      { intros u v. apply strict_indicator_eq_0.
        intros [HR Hneq]. apply Hneq. apply Hanti. exact HR. }
      unfold edge_count_5 in Hpos.
      rewrite !Hall0 in Hpos. lia.
  Qed.

End EdgeCount.

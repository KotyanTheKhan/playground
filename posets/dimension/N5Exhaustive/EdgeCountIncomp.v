(** Edge-count / comparability identities shared by the higher edge-count
    cases (counts 5-9) of the n=5 dispatcher.

    Kept in a SEPARATE file from [EdgeCount] so that adding these lemmas does
    not invalidate the heavy [EdgeCount4_*] cascade caches that depend on
    [EdgeCount]. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount.

Section EdgeCountIncomp.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** A comparable pair of distinct elements contributes exactly 1 to the
      edge count (one direction is a strict edge, the other is not). *)
  Lemma comparable_indicator_sum :
    forall x y, x <> y -> (R2 x y \/ R2 y x) ->
      strict_indicator R2 x y + strict_indicator R2 y x = 1.
  Proof.
    intros x y Hxy [HR | HR].
    - rewrite (strict_indicator_eq_1 R2 x y HR Hxy).
      assert (strict_indicator R2 y x = 0) as ->.
      { apply strict_indicator_eq_0. intros [HRyx _].
        apply Hxy. exact (poset_antisym x y HR HRyx). }
      lia.
    - assert (Hyx : y <> x) by (intro Heq; apply Hxy; symmetry; exact Heq).
      rewrite (strict_indicator_eq_1 R2 y x HR Hyx).
      assert (strict_indicator R2 x y = 0) as ->.
      { apply strict_indicator_eq_0. intros [HRxy _].
        apply Hxy. exact (poset_antisym x y HRxy HR). }
      lia.
  Qed.

  (** If the edge count is at most 9 then some pair is incomparable
      (otherwise every one of the 10 pairs would contribute 1, forcing the
      count to be 10).  Witnesses are carrier elements via the cover. *)
  Lemma incomp_carrier_exists :
    forall a b c d e,
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e <= 9 ->
      exists x y : B, @Incomparable B R2 x y.
  Proof.
    intros a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hle.
    apply NNPP. intro Hno.
    assert (Hcomp : forall x y, x <> y -> R2 x y \/ R2 y x).
    { intros x y Hxy. apply NNPP. intro Hnc.
      apply Hno. exists x, y. exact Hnc. }
    pose proof (comparable_indicator_sum a b Hab (Hcomp a b Hab)).
    pose proof (comparable_indicator_sum a c Hac (Hcomp a c Hac)).
    pose proof (comparable_indicator_sum a d Had (Hcomp a d Had)).
    pose proof (comparable_indicator_sum a e Hae (Hcomp a e Hae)).
    pose proof (comparable_indicator_sum b c Hbc (Hcomp b c Hbc)).
    pose proof (comparable_indicator_sum b d Hbd (Hcomp b d Hbd)).
    pose proof (comparable_indicator_sum b e Hbe (Hcomp b e Hbe)).
    pose proof (comparable_indicator_sum c d Hcd (Hcomp c d Hcd)).
    pose proof (comparable_indicator_sum c e Hce (Hcomp c e Hce)).
    pose proof (comparable_indicator_sum d e Hde (Hcomp d e Hde)).
    unfold edge_count_5 in Hle. lia.
  Qed.

End EdgeCountIncomp.

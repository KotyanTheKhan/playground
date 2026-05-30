(** * Lemma 5.6 / Trotter Theorem 2:  dim(X) ≤ max{2, |X − A|}  (A antichain)

    The induction step of the direct Hiraguchi proof, built on
    [OnePointRemoval.one_point_removal].  Polymorphic over the carrier so the
    inductive call lands on the subtype X − p as a fresh poset. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia.
From Stdlib Require Import Classical ClassicalDescription ProofIrrelevance.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs Theorems OnePointRemoval.

(** Cardinality of a complement: |Full − Sub| = |Full| − |Sub|. *)
Lemma cardinal_setminus :
  forall (U : Type) (Sub : Ensemble U) (k : nat),
    cardinal U Sub k ->
    forall (Full : Ensemble U) (N : nat),
      cardinal U Full N -> Included U Sub Full ->
      cardinal U (Setminus U Full Sub) (N - k).
Proof.
  intros U Sub k Hcard. induction Hcard as [| A n Hsub IH x Hxni]; intros Full N HF Hincl.
  - (* Sub = ∅ *)
    replace (Setminus U Full (Empty_set U)) with Full.
    + rewrite Nat.sub_0_r. exact HF.
    + apply Extensionality_Ensembles. split.
      * intros y Hy. split; [ exact Hy | intro Hbot; destruct Hbot ].
      * intros y [Hy _]. exact Hy.
  - (* Sub = Add A x, x ∉ A *)
    assert (HinclA : Included U A Full).
    { intros y Hy. apply Hincl. left; exact Hy. }
    assert (Hx_full : In U Full x) by (apply Hincl; right; constructor).
    pose proof (IH Full N HF HinclA) as Hca.
    (* Setminus Full (Add A x) = Subtract (Setminus Full A) x *)
    replace (Setminus U Full (Add U A x))
       with (Subtract U (Setminus U Full A) x).
    + assert (Hx_in : In U (Setminus U Full A) x) by (split; [ exact Hx_full | exact Hxni ]).
      pose proof (card_soustr_1 U (Setminus U Full A) (N - n) Hca x Hx_in) as Hcs.
      replace (N - S n) with (Nat.pred (N - n)) by lia.
      exact Hcs.
    + apply Extensionality_Ensembles. split.
      * intros y [[Hyf Hyna] Hynx]. split; [ exact Hyf |].
        intro Hyadd. destruct Hyadd as [y Hy | y Hy].
        -- apply Hyna; exact Hy.
        -- apply Hynx; exact Hy.
      * intros y [Hyf Hyn]. split.
        -- split; [ exact Hyf | intro Hya; apply Hyn; left; exact Hya ].
        -- intro Hyx. apply Hyn. destruct Hyx. right; constructor.
Qed.

Section AntichainComplement.
  Context {B : Type}.
  Context (R : B -> B -> Prop) `{IsPoset B R}.

  (** A poset with two distinct elements has dimension ≥ 1
      (the empty realizer would force the relation to be universal). *)
  Lemma dim_ge_1_of_two :
    forall d, PosetDimension R d -> (exists a b : B, a <> b) -> 1 <= d.
  Proof.
    intros d Hdim [a [b Hab]].
    destruct d as [| d']; [| lia]. exfalso.
    pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    (* cardinal realizer 0 ⟹ realizer is empty *)
    assert (Hre : dimension_realizer Hdim = Empty_set _)
      by (apply cardinalO_empty; exact Hcard).
    assert (Hempty : forall L, ~ In _ (dimension_realizer Hdim) L).
    { intros L HL. rewrite Hre in HL. destruct HL. }
    assert (HRab : R a b).
    { apply (proj2 (realizer_intersection Hreal a b)).
      intros L HL. exfalso. exact (Hempty L HL). }
    assert (HRba : R b a).
    { apply (proj2 (realizer_intersection Hreal b a)).
      intros L HL. exfalso. exact (Hempty L HL). }
    exact (Hab (poset_antisym _ _ HRab HRba)).
  Qed.

End AntichainComplement.

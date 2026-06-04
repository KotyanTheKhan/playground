(* Generic dim-2 toolkit: incomparable pair => dim >= 2, and a 2-linear-extension
   realizer => dim = 2. Off-ExecPoset generalization of DimBridge's two lemmas. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import FinPosetDimSurgery.

Lemma dim_ge_2_of_incomparable :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (x y : A),
    Incomparable R x y ->
    forall d, PosetDimension R d -> 2 <= d.
Proof.
  intros A R HR x y Hinc d Hdim.
  assert (Hne : x <> y).
  { intro Heq. apply Hinc. left. subst y. apply poset_refl. }
  destruct d as [| [| d']]; [ exfalso | exfalso | lia ].
  - pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    assert (Hre : dimension_realizer Hdim = Empty_set _)
      by (apply cardinalO_empty; exact Hcard).
    assert (Hempty : forall L, ~ In _ (dimension_realizer Hdim) L).
    { intros L HL. rewrite Hre in HL. destruct HL. }
    assert (HRxy : R x y).
    { apply (proj2 (realizer_intersection Hreal x y)).
      intros L HL. exfalso. exact (Hempty L HL). }
    apply Hinc. left. exact HRxy.
  - pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    destruct (cardinal_invert _ _ _ Hcard) as [A' [L [Heq [Hnin Hcard0]]]].
    assert (HA' : A' = Empty_set _) by (apply cardinalO_empty; exact Hcard0).
    subst A'.
    assert (HinL : In _ (dimension_realizer Hdim) L).
    { rewrite Heq. apply Add_intro2. }
    assert (Hmem : forall L', In _ (dimension_realizer Hdim) L' -> L' = L).
    { intros L' HL'. rewrite Heq in HL'.
      destruct HL' as [L' Hbad | L' Hsing].
      - destruct Hbad.
      - apply Singleton_inv in Hsing. symmetry. exact Hsing. }
    pose proof (realizer_linear Hreal L HinL) as HLlin.
    pose proof (linear_is_total HLlin) as HLtot.
    pose proof (total_comparable (IsTotalOrder := HLtot) x y) as Hcomp.
    assert (Hback : forall u v, L u v -> R u v).
    { intros u v Huv. apply (proj2 (realizer_intersection Hreal u v)).
      intros L' HL'. rewrite (Hmem L' HL'). exact Huv. }
    destruct Hcomp as [HLxy | HLyx].
    + apply Hinc. left. apply Hback. exact HLxy.
    + apply Hinc. right. apply Hback. exact HLyx.
Qed.

Lemma dim_eq_2_of_realizer :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)),
    (exists L1 L2,
       IsLinearExtension R L1 /\ IsLinearExtension R L2 /\
       (forall x y, R x y <-> (L1 x y /\ L2 x y))) ->
    (exists x y, Incomparable R x y) ->
    inhabited (PosetDimension R 2).
Proof.
  intros A R HR Hfin [L1 [L2 [Hlin1 [Hlin2 Hcap]]]] [x0 [y0 Hinc]].
  set (realizer := fun L : A -> A -> Prop => L = L1 \/ L = L2).
  assert (HrealizerIsRealizer : IsRealizer R realizer).
  { constructor.
    - intros L [-> | ->]; assumption.
    - intros x y. split.
      + intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HL1 HL2].
        intros L [-> | ->]; assumption.
      + intro Hall. apply (proj2 (Hcap x y)). split.
        * apply (Hall L1). left. reflexivity.
        * apply (Hall L2). right. reflexivity. }
  assert (HL12 : L1 <> L2).
  { intro HeqL.
    pose proof (linear_is_total Hlin1) as Htot1.
    pose proof (total_comparable (IsTotalOrder := Htot1) x0 y0) as Hc1.
    destruct Hc1 as [H1xy | H1yx].
    - apply Hinc. left. apply (proj2 (Hcap x0 y0)).
      split; [ exact H1xy | rewrite <- HeqL; exact H1xy ].
    - apply Hinc. right. apply (proj2 (Hcap y0 x0)).
      split; [ exact H1yx | rewrite <- HeqL; exact H1yx ]. }
  assert (Hreq : realizer = Add _ (Add _ (Empty_set _) L1) L2).
  { apply Extensionality_Ensembles. split.
    - intros L HL. destruct HL as [-> | ->].
      + left. right. constructor.
      + right. constructor.
    - intros L HL. destruct HL as [L HL | L HL].
      + destruct HL as [L HL | L HL].
        * destruct HL.
        * apply Singleton_inv in HL. left. symmetry. exact HL.
      + apply Singleton_inv in HL. right. symmetry. exact HL. }
  assert (Hcard2 : cardinal _ realizer 2).
  { rewrite Hreq. apply card_add.
    - apply card_add.
      + apply card_empty.
      + intro Hbad. destruct Hbad.
    - intro Hbad. destruct Hbad as [L Hbad | L Hbad].
      + destruct Hbad.
      + apply Singleton_inv in Hbad. apply HL12. exact Hbad. }
  destruct (fin_dim_exists R Hfin) as [d [Hd]].
  pose proof (dimension_is_minimum Hd realizer 2 HrealizerIsRealizer Hcard2) as Hle.
  pose proof (dim_ge_2_of_incomparable R x0 y0 Hinc d Hd) as Hge.
  assert (Hd2 : d = 2) by lia. subst d. constructor. exact Hd.
Qed.

(* bare PosetDimension record (Type), for callers that need the record itself
   (e.g. dimension_iso transport / fin_barrier_dimension_full): explicit L1 L2 x0 y0
   so there is no Prop-existential to eliminate into the Type goal. *)
Lemma dim2_record :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (L1 L2 : A -> A -> Prop) (x0 y0 : A),
    IsLinearExtension R L1 -> IsLinearExtension R L2 ->
    (forall x y, R x y <-> (L1 x y /\ L2 x y)) ->
    Incomparable R x0 y0 ->
    PosetDimension R 2.
Proof.
  intros A R HR L1 L2 x0 y0 Hlin1 Hlin2 Hcap Hinc.
  refine {| dimension_realizer := (fun L => L = L1 \/ L = L2);
            dimension_is_realizer := _;
            dimension_cardinality := _;
            dimension_is_minimum := _ |}.
  - (* IsRealizer *) constructor.
    + intros L [-> | ->]; assumption.
    + intros x y. split.
      * intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HL1 HL2].
        intros L [-> | ->]; assumption.
      * intro Hall. apply (proj2 (Hcap x y)). split.
        -- apply (Hall L1). left. reflexivity.
        -- apply (Hall L2). right. reflexivity.
  - (* cardinality 2 *)
    assert (HL12 : L1 <> L2).
    { intro HeqL.
      pose proof (linear_is_total Hlin1) as Htot1.
      pose proof (total_comparable (IsTotalOrder := Htot1) x0 y0) as Hc1.
      destruct Hc1 as [H1xy | H1yx].
      - apply Hinc. left. apply (proj2 (Hcap x0 y0)).
        split; [ exact H1xy | rewrite <- HeqL; exact H1xy ].
      - apply Hinc. right. apply (proj2 (Hcap y0 x0)).
        split; [ exact H1yx | rewrite <- HeqL; exact H1yx ]. }
    assert (Hreq : (fun L => L = L1 \/ L = L2) = Add _ (Add _ (Empty_set _) L1) L2).
    { apply Extensionality_Ensembles. split.
      - intros L HL. destruct HL as [-> | ->].
        + left. right. constructor.
        + right. constructor.
      - intros L HL. destruct HL as [L HL | L HL].
        + destruct HL as [L HL | L HL].
          * destruct HL.
          * apply Singleton_inv in HL. left. symmetry. exact HL.
        + apply Singleton_inv in HL. right. symmetry. exact HL. }
    rewrite Hreq. apply card_add.
    + apply card_add.
      * apply card_empty.
      * intro Hbad. destruct Hbad.
    + intro Hbad. destruct Hbad as [L Hbad | L Hbad].
      * destruct Hbad.
      * apply Singleton_inv in Hbad. apply HL12. exact Hbad.
  - (* minimality: every realizer has >= 2 elements *)
    intros r n Hr Hcard.
    assert (Hne : x0 <> y0).
    { intro Heq. apply Hinc. left. subst y0. apply poset_refl. }
    destruct n as [| [| n']]; [ exfalso | exfalso | lia ].
    + assert (Hre : r = Empty_set _) by (apply cardinalO_empty; exact Hcard).
      assert (HRxy : R x0 y0).
      { apply (proj2 (realizer_intersection Hr x0 y0)).
        intros L HL. rewrite Hre in HL. destruct HL. }
      apply Hinc. left. exact HRxy.
    + destruct (cardinal_invert _ _ _ Hcard) as [A' [L [Heq [Hnin Hcard0]]]].
      assert (HA' : A' = Empty_set _) by (apply cardinalO_empty; exact Hcard0).
      subst A'.
      assert (HinL : In _ r L). { rewrite Heq. apply Add_intro2. }
      assert (Hmem : forall L', In _ r L' -> L' = L).
      { intros L' HL'. rewrite Heq in HL'.
        destruct HL' as [L' Hbad | L' Hsing].
        - destruct Hbad.
        - apply Singleton_inv in Hsing. symmetry. exact Hsing. }
      pose proof (realizer_linear Hr L HinL) as HLlin.
      pose proof (linear_is_total HLlin) as HLtot.
      pose proof (total_comparable (IsTotalOrder := HLtot) x0 y0) as Hcomp.
      assert (Hback : forall u v, L u v -> R u v).
      { intros u v Huv. apply (proj2 (realizer_intersection Hr u v)).
        intros L' HL'. rewrite (Hmem L' HL'). exact Huv. }
      destruct Hcomp as [HLxy | HLyx].
      * apply Hinc. left. apply Hback. exact HLxy.
      * apply Hinc. right. apply Hback. exact HLyx.
Qed.

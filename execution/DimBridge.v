(* execution dimension bridge — DimBridge *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition exec_has_dimension (E : ExecPoset) (d : nat) : Prop :=
  inhabited (PosetDimension (ep_order E) d).

(** Every execution poset has a (Dushnik–Miller) dimension. *)
Lemma exec_dimension_exists :
  forall E, exists d, exec_has_dimension E d.
Proof.
  intro E. unfold exec_has_dimension.
  unfold ep_carrier, ep_order in *.
  apply (dushnik_miller_exists (hb (ep_ranked E)) (ep_size E)).
  exact (ep_size_ok E).
Qed.

(** Two incomparable elements force dimension at least 2. *)
Lemma exec_dim_ge_2 :
  forall E (x y : ep_carrier E),
    Incomparable (ep_order E) x y ->
    forall d, PosetDimension (ep_order E) d -> 2 <= d.
Proof.
  intros E x y Hinc d Hdim.
  (* x <> y, otherwise reflexivity contradicts incomparability *)
  assert (Hne : x <> y).
  { intro Heq. apply Hinc. left. subst y. apply poset_refl. }
  destruct d as [| [| d']]; [ exfalso | exfalso | lia ].
  - (* d = 0 : empty realizer forces the order to be universal *)
    pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    assert (Hre : dimension_realizer Hdim = Empty_set _)
      by (apply cardinalO_empty; exact Hcard).
    assert (Hempty : forall L, ~ In _ (dimension_realizer Hdim) L).
    { intros L HL. rewrite Hre in HL. destruct HL. }
    assert (HRxy : ep_order E x y).
    { apply (proj2 (realizer_intersection Hreal x y)).
      intros L HL. exfalso. exact (Hempty L HL). }
    apply Hinc. left. exact HRxy.
  - (* d = 1 : a single linear extension makes the order total *)
    pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    destruct (cardinal_invert _ _ _ Hcard) as [A' [L [Heq [Hnin Hcard0]]]].
    assert (HA' : A' = Empty_set _) by (apply cardinalO_empty; exact Hcard0).
    subst A'.
    (* realizer = Add (Empty_set _) L : its only member is L *)
    assert (HinL : In _ (dimension_realizer Hdim) L).
    { rewrite Heq. apply Add_intro2. }
    assert (Hmem : forall L', In _ (dimension_realizer Hdim) L' -> L' = L).
    { intros L' HL'. rewrite Heq in HL'.
      destruct HL' as [L' Hbad | L' Hsing].
      - destruct Hbad.
      - apply Singleton_inv in Hsing. symmetry. exact Hsing. }
    (* L is a linear extension, hence total *)
    pose proof (realizer_linear Hreal L HinL) as HLlin.
    pose proof (linear_is_total HLlin) as HLtot.
    pose proof (total_comparable (IsTotalOrder := HLtot) x y) as Hcomp.
    (* L u v <-> ep_order E u v for the singleton realizer *)
    assert (Hback : forall u v, L u v -> ep_order E u v).
    { intros u v Huv. apply (proj2 (realizer_intersection Hreal u v)).
      intros L' HL'. rewrite (Hmem L' HL'). exact Huv. }
    destruct Hcomp as [HLxy | HLyx].
    + apply Hinc. left. apply Hback. exact HLxy.
    + apply Hinc. right. apply Hback. exact HLyx.
Qed.

(** If the execution order is exactly the intersection of two linear extensions
    and admits an incomparable pair, its dimension is exactly 2. *)
Lemma exec_dim_eq_2_of_realizer :
  forall E,
    (exists L1 L2,
       IsLinearExtension (ep_order E) L1 /\
       IsLinearExtension (ep_order E) L2 /\
       (forall x y, ep_order E x y <-> (L1 x y /\ L2 x y))) ->
    (exists x y, Incomparable (ep_order E) x y) ->
    exec_has_dimension E 2.
Proof.
  intros E [L1 [L2 [Hlin1 [Hlin2 Hcap]]]] [x0 [y0 Hinc]].
  set (realizer := fun L : ep_carrier E -> ep_carrier E -> Prop => L = L1 \/ L = L2).
  (* realizer realizes the order *)
  assert (HrealizerIsRealizer : IsRealizer (ep_order E) realizer).
  { constructor.
    - intros L [-> | ->]; assumption.
    - intros x y. split.
      + intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HL1 HL2].
        intros L [-> | ->]; assumption.
      + intro Hall. apply (proj2 (Hcap x y)). split.
        * apply (Hall L1). left. reflexivity.
        * apply (Hall L2). right. reflexivity. }
  (* L1 <> L2 : otherwise the incomparable pair would be comparable *)
  assert (HL12 : L1 <> L2).
  { intro HeqL.
    pose proof (linear_is_total Hlin1) as Htot1.
    pose proof (total_comparable (IsTotalOrder := Htot1) x0 y0) as Hc1.
    destruct Hc1 as [H1xy | H1yx].
    - apply Hinc. left. apply (proj2 (Hcap x0 y0)).
      split; [ exact H1xy | rewrite <- HeqL; exact H1xy ].
    - apply Hinc. right. apply (proj2 (Hcap y0 x0)).
      split; [ exact H1yx | rewrite <- HeqL; exact H1yx ]. }
  (* realizer has cardinality 2 *)
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
  (* combine the minimality bound with the dim>=2 lower bound *)
  unfold exec_has_dimension.
  destruct (exec_dimension_exists E) as [d [Hd]].
  pose proof (dimension_is_minimum Hd realizer 2 HrealizerIsRealizer Hcard2) as Hle.
  pose proof (exec_dim_ge_2 E x0 y0 Hinc d Hd) as Hge.
  assert (Hd2 : d = 2) by lia.
  subst d. constructor. exact Hd.
Qed.

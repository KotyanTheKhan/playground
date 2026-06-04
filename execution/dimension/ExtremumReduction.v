(* removing a global extremum preserves dim<=2 (realizer surgery) *)
(* MAX side: lift_max surgery.  MIN side lives in ExtremumReductionAux. *)

From Stdlib Require Import Ensembles Finite_sets Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Reduction.
From Execution Require Export ExtremumReductionAux.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* ================================================================== *)
(*  MAX side: lift a linear extension of the block to one of E,        *)
(*  with m at the top.                                                 *)
(* ================================================================== *)

Definition lift_max (E : ExecPoset) (m : ep_carrier E)
   (LB : {z | z <> m} -> {z | z <> m} -> Prop) (a b : ep_carrier E) : Prop :=
   b = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).

Lemma lift_max_is_linext :
  forall E m (LB : {z | z <> m} -> {z | z <> m} -> Prop),
    IsGlobalMax E m ->
    IsLinearExtension (sub_order E (fun x => x <> m)) LB ->
    IsLinearExtension (ep_order E) (lift_max E m LB).
Proof.
  intros E m LB Hmax HLB.
  pose proof (HLB.(linear_is_total)) as HBtot.
  pose proof (HBtot.(total_is_poset)) as HBpos.
  refine {| linear_is_total := _ ; linear_extends := _ |}.
  - refine {| total_is_poset := _ ; total_comparable := _ |}.
    + constructor.
      * (* refl *)
        intro a. destruct (classic (a = m)) as [Ham | Ham].
        -- left. exact Ham.
        -- right. exists Ham, Ham.
           exact (HBpos.(poset_refl) (exist _ a Ham)).
      * (* antisym *)
        intros a b Hab Hba.
        destruct Hab as [Hbm | [Ha [Hb HLab]]].
        -- (* b = m *)
           destruct Hba as [Ham | [Hb' [Ha' HLba]]].
           ++ subst b. exact Ham.
           ++ (* Hba inner Hb' : b <> m, but b = m *)
              exfalso. apply Hb'. exact Hbm.
        -- (* b <> m, with HLab *)
           destruct Hba as [Ham | [Hb' [Ha' HLba]]].
           ++ (* a = m, but Ha : a <> m *)
              exfalso. apply Ha. exact Ham.
           ++ assert (Heq : exist (fun z => z <> m) a Ha
                          = exist (fun z => z <> m) b Hb).
              { apply (HBpos.(poset_antisym)).
                - exact HLab.
                - rewrite (proof_irrelevance _ Hb Hb').
                  rewrite (proof_irrelevance _ Ha Ha').
                  exact HLba. }
              exact (f_equal (@proj1_sig _ _) Heq).
      * (* trans *)
        intros a b c Hab Hbc.
        destruct Hbc as [Hcm | [Hb' [Hc HLbc]]].
        -- (* c = m -> lift_max a c by left *)
           left. exact Hcm.
        -- (* c <> m *)
           destruct Hab as [Hbm | [Ha [Hb HLab]]].
           ++ (* b = m, but Hb' : b <> m *)
              exfalso. apply Hb'. exact Hbm.
           ++ right. exists Ha, Hc.
              rewrite (proof_irrelevance _ Hb' Hb) in HLbc.
              exact (HBpos.(poset_trans) _ _ _ HLab HLbc).
    + (* total_comparable *)
      intros a b.
      destruct (classic (b = m)) as [Hbm | Hbm].
      * left. left. exact Hbm.
      * destruct (classic (a = m)) as [Ham | Ham].
        -- right. left. exact Ham.
        -- destruct (HBtot.(total_comparable)
                       (exist _ a Ham) (exist _ b Hbm)) as [Hc | Hc].
           ++ left. right. exists Ham, Hbm. exact Hc.
           ++ right. right. exists Hbm, Ham. exact Hc.
  - (* linear_extends *)
    intros a b Hab.
    destruct (classic (b = m)) as [Hbm | Hbm].
    + left. exact Hbm.
    + (* b <> m; show a <> m *)
      assert (Ham : a <> m).
      { intro Heq. subst a.
        pose proof (Hmax b) as Hbm'.
        pose proof (poset_antisym (R := ep_order E) m b Hab Hbm') as Heq.
        apply Hbm. symmetry. exact Heq. }
      right. exists Ham, Hbm.
      apply (HLB.(linear_extends) (exist _ a Ham) (exist _ b Hbm)).
      unfold sub_order. simpl. exact Hab.
Qed.

Lemma lift_max_inj :
  forall E m (LB1 LB2 : {z | z <> m} -> {z | z <> m} -> Prop),
    lift_max E m LB1 = lift_max E m LB2 -> LB1 = LB2.
Proof.
  intros E m LB1 LB2 Heq.
  apply functional_extensionality; intros [a Ha].
  apply functional_extensionality; intros [b Hb].
  pose proof (equal_f (equal_f Heq a) b) as Hpt.
  unfold lift_max in Hpt.
  apply propositional_extensionality.
  assert (Hiff : (b = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB1 (exist _ a Ha0) (exist _ b Hb0)))
             <-> (b = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB2 (exist _ a Ha0) (exist _ b Hb0)))).
  { rewrite Hpt. reflexivity. }
  split.
  - intro H1.
    assert (Hd1 : b = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB1 (exist _ a Ha0) (exist _ b Hb0))).
    { right. exists Ha, Hb. exact H1. }
    apply Hiff in Hd1.
    destruct Hd1 as [Hbm | [Ha0 [Hb0 HL]]].
    + exfalso. apply Hb. exact Hbm.
    + rewrite (proof_irrelevance _ Ha0 Ha) in HL.
      rewrite (proof_irrelevance _ Hb0 Hb) in HL.
      exact HL.
  - intro H2.
    assert (Hd2 : b = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB2 (exist _ a Ha0) (exist _ b Hb0))).
    { right. exists Ha, Hb. exact H2. }
    apply Hiff in Hd2.
    destruct Hd2 as [Hbm | [Ha0 [Hb0 HL]]].
    + exfalso. apply Hb. exact Hbm.
    + rewrite (proof_irrelevance _ Ha0 Ha) in HL.
      rewrite (proof_irrelevance _ Hb0 Hb) in HL.
      exact HL.
Qed.

Lemma remove_max_preserves_dim2 :
  forall E m, IsGlobalMax E m ->
    ((exists d, inhabited (PosetDimension (sub_order E (fun x => x <> m)) d) /\ d <= 2)
     <->
     (exists d, exec_has_dimension E d /\ d <= 2)).
Proof.
  intros E m Hmax. split.
  - (* HARD: block dim2 -> E dim2 *)
    intros [d [[RBdim] Hled]].
    destruct d as [| d'].
    + (* d = 0 *)
      apply small_E_dim_le_2.
      pose proof (dimension_is_realizer RBdim) as HBreal.
      pose proof (dimension_cardinality RBdim) as HBcard.
      assert (HBempty : dimension_realizer RBdim = Empty_set _)
        by (apply cardinalO_empty; exact HBcard).
      assert (Hblock_eq :
        forall (x y : {z : ep_carrier E | z <> m}),
          proj1_sig x = proj1_sig y).
      { intros x y.
        assert (Hxy : sub_order E (fun z => z <> m) x y).
        { apply (proj2 (realizer_intersection HBreal x y)).
          intros L HL. rewrite HBempty in HL. destruct HL. }
        assert (Hyx : sub_order E (fun z => z <> m) y x).
        { apply (proj2 (realizer_intersection HBreal y x)).
          intros L HL. rewrite HBempty in HL. destruct HL. }
        pose proof (sub_order_poset E (fun z => z <> m)) as Hsp.
        assert (Heqxy : x = y) by exact (Hsp.(poset_antisym) x y Hxy Hyx).
        f_equal. exact Heqxy. }
      intros a b.
      destruct (classic (a = m)) as [Ham | Ham].
      * right. subst a. exact (Hmax b).
      * destruct (classic (b = m)) as [Hbm | Hbm].
        -- left. subst b. exact (Hmax a).
        -- assert (Heqab : a = b)
             by exact (Hblock_eq (exist _ a Ham) (exist _ b Hbm)).
           left. subst b. apply (poset_refl (R := ep_order E)).
    + (* d = S d' *)
      set (RB := dimension_realizer RBdim).
      pose proof (dimension_is_realizer RBdim) as HBreal.
      pose proof (dimension_cardinality RBdim) as HBcard.
      set (RE := Im _ _ RB (lift_max E m)).
      destruct (cardinal_invert _ _ _ HBcard) as [RB0 [LB0 [HRBeq [HLB0nin _]]]].
      assert (HLB0in : In _ RB LB0) by (unfold RB; rewrite HRBeq; apply Add_intro2).
      assert (HRE_real : IsRealizer (ep_order E) RE).
      { constructor.
        - intros M HM.
          inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
          apply lift_max_is_linext.
          + exact Hmax.
          + exact (realizer_linear HBreal LB HLBin).
        - intros a b. split.
          + intros Hab M HM.
            inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
            destruct (classic (b = m)) as [Hbm | Hbm].
            * left. exact Hbm.
            * assert (Ham : a <> m).
              { intro Heq. subst a.
                pose proof (Hmax b) as Hbm'.
                apply Hbm. symmetry.
                exact (poset_antisym (R := ep_order E) m b Hab Hbm'). }
              right. exists Ham, Hbm.
              apply (linear_extends (realizer_linear HBreal LB HLBin)
                       (exist _ a Ham) (exist _ b Hbm)).
              unfold sub_order. simpl. exact Hab.
          + intros Hall.
            destruct (classic (b = m)) as [Hbm | Hbm].
            * subst b. exact (Hmax a).
            * assert (HM0in : In _ RE (lift_max E m LB0)).
              { unfold RE. apply Im_intro with (x := LB0).
                - exact HLB0in.
                - reflexivity. }
              pose proof (Hall (lift_max E m LB0) HM0in) as HliftLB0.
              assert (Ham : a <> m).
              { intro Heq. subst a.
                destruct HliftLB0 as [Hbm' | [Ha0 [Hb0 _]]].
                - apply Hbm. exact Hbm'.
                - apply Ha0. reflexivity. }
              assert (Hblock : sub_order E (fun z => z <> m)
                                 (exist _ a Ham) (exist _ b Hbm)).
              { apply (proj2 (realizer_intersection HBreal
                               (exist _ a Ham) (exist _ b Hbm))).
                intros LB HLBin.
                assert (HMin : In _ RE (lift_max E m LB)).
                { unfold RE. apply Im_intro with (x := LB).
                  - exact HLBin.
                  - reflexivity. }
                pose proof (Hall (lift_max E m LB) HMin) as Hlift.
                destruct Hlift as [Hbm' | [Ha0 [Hb0 HL]]].
                - exfalso. apply Hbm. exact Hbm'.
                - rewrite (proof_irrelevance _ Ha0 Ham) in HL.
                  rewrite (proof_irrelevance _ Hb0 Hbm) in HL.
                  exact HL. }
              unfold sub_order in Hblock. simpl in Hblock. exact Hblock. }
      assert (HRE_card : cardinal _ RE (S d')).
      { unfold RE.
        apply (cardinal_Im_injective _ _ RB (lift_max E m) (S d')).
        - exact HBcard.
        - intros LB1 LB2 _ _ Heq.
          exact (lift_max_inj E m LB1 LB2 Heq). }
      destruct (exec_dimension_exists E) as [dE [HdE]].
      pose proof (dimension_is_minimum HdE RE (S d') HRE_real HRE_card) as Hle.
      exists dE. split.
      * exact (inhabits HdE).
      * lia.
  - (* EASY: E dim2 -> block dim2 *)
    intros HE.
    destruct HE as [dE [[HdE] HledE]].
    destruct (subposet_dimension_le (ep_order E) (fun x => x <> m) dE HdE)
      as [dB [[HdB] HleB]].
    exists dB. split.
    + exact (inhabits HdB).
    + lia.
Qed.

(* generic finite-poset extremum-removal surgery

   Carrier-abstracted port of execution/ExtremumReduction.v: the same
   realizer-surgery proofs that an [ExecPoset]'s extremum removal preserves
   dim<=2, reproduced on a bare finite poset (A, R) with [IsPoset A R] and
   [Finite A (Full_set A)].  No new mathematics; only the carrier/wrapper
   names change. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Export FinPosetDimSurgeryAux.

Section FinPosetMax.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  (* Re-bind names from the closed FinPoset section so proof bodies
     in this section can use them without explicit R/Hfin arguments. *)
  #[local] Notation fin_sub_order     := (fin_sub_order R).
  #[local] Notation fin_sub_order_poset := (fin_sub_order_poset R).
  #[local] Notation fin_global_max    := (fin_global_max R).
  #[local] Notation fin_dim_exists    := (fin_dim_exists R Hfin).
  #[local] Notation fin_small_dim_le_2 := (fin_small_dim_le_2 R Hfin).

  (* ================================================================== *)
  (*  MAX side: lift a linear extension of the block to one of (A,R),    *)
  (*  with m at the top.                                                 *)
  (* ================================================================== *)

  Definition fin_lift_max (m : A) (LB : {z | z <> m} -> {z | z <> m} -> Prop)
     (a b : A) : Prop :=
     b = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).

  Lemma fin_lift_max_is_linext :
    forall m (LB : {z | z <> m} -> {z | z <> m} -> Prop),
      fin_global_max m ->
      IsLinearExtension (fin_sub_order (fun x => x <> m)) LB ->
      IsLinearExtension R (fin_lift_max m LB).
  Proof.
    intros m LB Hmax HLB.
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
          -- (* c = m -> fin_lift_max a c by left *)
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
          pose proof (poset_antisym (R := R) m b Hab Hbm') as Heq.
          apply Hbm. symmetry. exact Heq. }
        right. exists Ham, Hbm.
        apply (HLB.(linear_extends) (exist _ a Ham) (exist _ b Hbm)).
        unfold fin_sub_order. simpl. exact Hab.
  Qed.

  Lemma fin_lift_max_inj :
    forall m (LB1 LB2 : {z | z <> m} -> {z | z <> m} -> Prop),
      fin_lift_max m LB1 = fin_lift_max m LB2 -> LB1 = LB2.
  Proof.
    intros m LB1 LB2 Heq.
    apply functional_extensionality; intros [a Ha].
    apply functional_extensionality; intros [b Hb].
    pose proof (equal_f (equal_f Heq a) b) as Hpt.
    unfold fin_lift_max in Hpt.
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

  Lemma fin_remove_max_dim2 :
    forall m, fin_global_max m ->
      ((exists d, inhabited (PosetDimension (fin_sub_order (fun x => x <> m)) d) /\ d <= 2)
       <-> (exists d, inhabited (PosetDimension R d) /\ d <= 2)).
  Proof.
    intros m Hmax. split.
    - (* HARD: block dim2 -> (A,R) dim2 *)
      intros [d [[RBdim] Hled]].
      destruct d as [| d'].
      + (* d = 0 *)
        apply fin_small_dim_le_2.
        pose proof (dimension_is_realizer RBdim) as HBreal.
        pose proof (dimension_cardinality RBdim) as HBcard.
        assert (HBempty : dimension_realizer RBdim = Empty_set _)
          by (apply cardinalO_empty; exact HBcard).
        assert (Hblock_eq :
          forall (x y : {z : A | z <> m}),
            proj1_sig x = proj1_sig y).
        { intros x y.
          assert (Hxy : fin_sub_order (fun z => z <> m) x y).
          { apply (proj2 (realizer_intersection HBreal x y)).
            intros L HL. rewrite HBempty in HL. destruct HL. }
          assert (Hyx : fin_sub_order (fun z => z <> m) y x).
          { apply (proj2 (realizer_intersection HBreal y x)).
            intros L HL. rewrite HBempty in HL. destruct HL. }
          pose proof (fin_sub_order_poset (fun z => z <> m)) as Hsp.
          assert (Heqxy : x = y) by exact (Hsp.(poset_antisym) x y Hxy Hyx).
          f_equal. exact Heqxy. }
        intros a b.
        destruct (classic (a = m)) as [Ham | Ham].
        * right. subst a. exact (Hmax b).
        * destruct (classic (b = m)) as [Hbm | Hbm].
          -- left. subst b. exact (Hmax a).
          -- assert (Heqab : a = b)
               by exact (Hblock_eq (exist _ a Ham) (exist _ b Hbm)).
             left. subst b. apply (poset_refl (R := R)).
      + (* d = S d' *)
        set (RB := dimension_realizer RBdim).
        pose proof (dimension_is_realizer RBdim) as HBreal.
        pose proof (dimension_cardinality RBdim) as HBcard.
        set (RE := Im _ _ RB (fin_lift_max m)).
        destruct (cardinal_invert _ _ _ HBcard) as [RB0 [LB0 [HRBeq [HLB0nin _]]]].
        assert (HLB0in : In _ RB LB0) by (unfold RB; rewrite HRBeq; apply Add_intro2).
        assert (HRE_real : IsRealizer R RE).
        { constructor.
          - intros M HM.
            inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
            apply fin_lift_max_is_linext.
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
                  exact (poset_antisym (R := R) m b Hab Hbm'). }
                right. exists Ham, Hbm.
                apply (linear_extends (realizer_linear HBreal LB HLBin)
                         (exist _ a Ham) (exist _ b Hbm)).
                unfold fin_sub_order. simpl. exact Hab.
            + intros Hall.
              destruct (classic (b = m)) as [Hbm | Hbm].
              * subst b. exact (Hmax a).
              * assert (HM0in : In _ RE (fin_lift_max m LB0)).
                { unfold RE. apply Im_intro with (x := LB0).
                  - exact HLB0in.
                  - reflexivity. }
                pose proof (Hall (fin_lift_max m LB0) HM0in) as HliftLB0.
                assert (Ham : a <> m).
                { intro Heq. subst a.
                  destruct HliftLB0 as [Hbm' | [Ha0 [Hb0 _]]].
                  - apply Hbm. exact Hbm'.
                  - apply Ha0. reflexivity. }
                assert (Hblock : fin_sub_order (fun z => z <> m)
                                   (exist _ a Ham) (exist _ b Hbm)).
                { apply (proj2 (realizer_intersection HBreal
                                 (exist _ a Ham) (exist _ b Hbm))).
                  intros LB HLBin.
                  assert (HMin : In _ RE (fin_lift_max m LB)).
                  { unfold RE. apply Im_intro with (x := LB).
                    - exact HLBin.
                    - reflexivity. }
                  pose proof (Hall (fin_lift_max m LB) HMin) as Hlift.
                  destruct Hlift as [Hbm' | [Ha0 [Hb0 HL]]].
                  - exfalso. apply Hbm. exact Hbm'.
                  - rewrite (proof_irrelevance _ Ha0 Ham) in HL.
                    rewrite (proof_irrelevance _ Hb0 Hbm) in HL.
                    exact HL. }
                unfold fin_sub_order in Hblock. simpl in Hblock. exact Hblock. }
        assert (HRE_card : cardinal _ RE (S d')).
        { unfold RE.
          apply (cardinal_Im_injective _ _ RB (fin_lift_max m) (S d')).
          - exact HBcard.
          - intros LB1 LB2 _ _ Heq.
            exact (fin_lift_max_inj m LB1 LB2 Heq). }
        destruct fin_dim_exists as [dE [HdE]].
        pose proof (dimension_is_minimum HdE RE (S d') HRE_real HRE_card) as Hle.
        exists dE. split.
        * exact (inhabits HdE).
        * lia.
    - (* EASY: (A,R) dim2 -> block dim2 *)
      intros HE.
      destruct HE as [dE [[HdE] HledE]].
      destruct (subposet_dimension_le R (fun x => x <> m) dE HdE)
        as [dB [[HdB] HleB]].
      exists dB. split.
      + exact (inhabits HdB).
      + lia.
  Qed.

End FinPosetMax.

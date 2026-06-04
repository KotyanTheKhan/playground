(* removing a global extremum preserves dim<=2 (realizer surgery) *)
(* Auxiliary file: MIN side + shared definitions used by the MAX side. *)

From Stdlib Require Import Ensembles Finite_sets Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Reduction.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition IsGlobalMin (E : ExecPoset) (m : ep_carrier E) : Prop := forall x, ep_order E m x.
Definition IsGlobalMax (E : ExecPoset) (m : ep_carrier E) : Prop := forall x, ep_order E x m.

(* ------------------------------------------------------------------ *)
(* A poset whose order is total has dimension <= 1 (a singleton realizer). *)
(* ------------------------------------------------------------------ *)

Lemma small_E_dim_le_2 :
  forall E,
    (forall a b : ep_carrier E, ep_order E a b \/ ep_order E b a) ->
    exists d, exec_has_dimension E d /\ d <= 2.
Proof.
  intros E Htot.
  (* The singleton realizer { ep_order E } realizes the (total) order. *)
  set (r := Singleton (ep_carrier E -> ep_carrier E -> Prop) (ep_order E)).
  assert (HrReal : IsRealizer (ep_order E) r).
  { constructor.
    - (* every member is a linear extension; the only member is ep_order E *)
      intros L HL. apply Singleton_inv in HL. subst L.
      constructor.
      + (* IsTotalOrder (ep_order E) *)
        constructor.
        * exact (hb_IsPoset (ep_ranked E)).
        * exact Htot.
      + intros x y Hxy. exact Hxy.
    - intros x y. split.
      + intros Hxy L HL. apply Singleton_inv in HL. subst L. exact Hxy.
      + intros Hall. apply (Hall (ep_order E)). constructor. }
  assert (Hcard1 : cardinal _ r 1).
  { unfold r.
    replace (Singleton (ep_carrier E -> ep_carrier E -> Prop) (ep_order E))
      with (Add (ep_carrier E -> ep_carrier E -> Prop)
              (Empty_set _) (ep_order E)).
    - apply card_add.
      + apply card_empty.
      + intro Hbad. destruct Hbad.
    - apply Extensionality_Ensembles. split.
      + intros L HL. destruct HL as [L HL | L HL].
        * destruct HL.
        * exact HL.
      + intros L HL. right. exact HL. }
  destruct (exec_dimension_exists E) as [d [Hd]].
  pose proof (dimension_is_minimum Hd r 1 HrReal Hcard1) as Hle.
  exists d. split.
  - exact (inhabits Hd).
  - lia.
Qed.

(* ================================================================== *)
(*  MIN side: lift a linear extension of the block to one of E,        *)
(*  with m at the bottom.                                              *)
(* ================================================================== *)

Definition lift_min (E : ExecPoset) (m : ep_carrier E)
   (LB : {z | z <> m} -> {z | z <> m} -> Prop) (a b : ep_carrier E) : Prop :=
   a = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).

Lemma lift_min_is_linext :
  forall E m (LB : {z | z <> m} -> {z | z <> m} -> Prop),
    IsGlobalMin E m ->
    IsLinearExtension (sub_order E (fun x => x <> m)) LB ->
    IsLinearExtension (ep_order E) (lift_min E m LB).
Proof.
  intros E m LB Hmin HLB.
  pose proof (HLB.(linear_is_total)) as HBtot.
  pose proof (HBtot.(total_is_poset)) as HBpos.
  refine {| linear_is_total := _ ; linear_extends := _ |}.
  - (* IsTotalOrder (lift_min ...) *)
    refine {| total_is_poset := _ ; total_comparable := _ |}.
    + (* IsPoset (lift_min ...) *)
      constructor.
      * (* refl *)
        intro a. destruct (classic (a = m)) as [Ham | Ham].
        -- left. exact Ham.
        -- right. exists Ham, Ham.
           exact (HBpos.(poset_refl) (exist _ a Ham)).
      * (* antisym *)
        intros a b Hab Hba.
        destruct Hab as [Ham | [Ha [Hb HLab]]].
        -- (* a = m *)
           destruct Hba as [Hbm | [Hb' [Ha' HLba]]].
           ++ subst a. symmetry. exact Hbm.
           ++ (* Hba's inner witness Ha' : a <> m, but a = m *)
              exfalso. apply Ha'. exact Ham.
        -- (* a <> m, with HLab *)
           destruct Hba as [Hbm | [Hb' [Ha' HLba]]].
           ++ (* b = m, but Hb : b <> m *)
              exfalso. apply Hb. exact Hbm.
           ++ (* both off m: use block antisym *)
              assert (Heq : exist (fun z => z <> m) a Ha
                          = exist (fun z => z <> m) b Hb).
              { apply (HBpos.(poset_antisym)).
                - exact HLab.
                - rewrite (proof_irrelevance _ Hb Hb').
                  rewrite (proof_irrelevance _ Ha Ha').
                  exact HLba. }
              exact (f_equal (@proj1_sig _ _) Heq).
      * (* trans *)
        intros a b c Hab Hbc.
        destruct Hab as [Ham | [Ha [Hb HLab]]].
        -- (* a = m -> lift_min a c by left *)
           left. exact Ham.
        -- (* a <> m *)
           destruct Hbc as [Hbm | [Hb' [Hc HLbc]]].
           ++ (* b = m, but Hb : b <> m *)
              exfalso. apply Hb. exact Hbm.
           ++ (* all off m: block trans *)
              right. exists Ha, Hc.
              rewrite (proof_irrelevance _ Hb' Hb) in HLbc.
              exact (HBpos.(poset_trans) _ _ _ HLab HLbc).
    + (* total_comparable *)
      intros a b.
      destruct (classic (a = m)) as [Ham | Ham].
      * left. left. exact Ham.
      * destruct (classic (b = m)) as [Hbm | Hbm].
        -- right. left. exact Hbm.
        -- destruct (HBtot.(total_comparable)
                       (exist _ a Ham) (exist _ b Hbm)) as [Hc | Hc].
           ++ left. right. exists Ham, Hbm. exact Hc.
           ++ right. right. exists Hbm, Ham. exact Hc.
  - (* linear_extends *)
    intros a b Hab.
    destruct (classic (a = m)) as [Ham | Ham].
    + left. exact Ham.
    + (* a <> m; show b <> m *)
      assert (Hbm : b <> m).
      { intro Heq. subst b.
        (* ep_order E a m and ep_order E m a -> a = m *)
        pose proof (Hmin a) as Hma.
        pose proof (poset_antisym (R := ep_order E) a m Hab Hma) as Heq.
        apply Ham. exact Heq. }
      right. exists Ham, Hbm.
      (* goal: LB (exist a Ham)(exist b Hbm); use block linear_extends *)
      apply (HLB.(linear_extends) (exist _ a Ham) (exist _ b Hbm)).
      unfold sub_order. simpl. exact Hab.
Qed.

Lemma lift_min_inj :
  forall E m (LB1 LB2 : {z | z <> m} -> {z | z <> m} -> Prop),
    lift_min E m LB1 = lift_min E m LB2 -> LB1 = LB2.
Proof.
  intros E m LB1 LB2 Heq.
  apply functional_extensionality; intros [a Ha].
  apply functional_extensionality; intros [b Hb].
  (* pointwise equality of the lifted relations at a b *)
  pose proof (equal_f (equal_f Heq a) b) as Hpt.
  unfold lift_min in Hpt.
  (* Hpt : (a = m \/ exists ..., LB1 ...) = (a = m \/ exists ..., LB2 ...) *)
  apply propositional_extensionality.
  (* turn the Prop-equality into an iff *)
  assert (Hiff : (a = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB1 (exist _ a Ha0) (exist _ b Hb0)))
             <-> (a = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB2 (exist _ a Ha0) (exist _ b Hb0)))).
  { rewrite Hpt. reflexivity. }
  split.
  - intro H1.
    assert (Hd1 : a = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB1 (exist _ a Ha0) (exist _ b Hb0))).
    { right. exists Ha, Hb. exact H1. }
    apply Hiff in Hd1.
    destruct Hd1 as [Ham | [Ha0 [Hb0 HL]]].
    + exfalso. apply Ha. exact Ham.
    + rewrite (proof_irrelevance _ Ha0 Ha) in HL.
      rewrite (proof_irrelevance _ Hb0 Hb) in HL.
      exact HL.
  - intro H2.
    assert (Hd2 : a = m \/ (exists (Ha0 : a <> m) (Hb0 : b <> m),
                              LB2 (exist _ a Ha0) (exist _ b Hb0))).
    { right. exists Ha, Hb. exact H2. }
    apply Hiff in Hd2.
    destruct Hd2 as [Ham | [Ha0 [Hb0 HL]]].
    + exfalso. apply Ha. exact Ham.
    + rewrite (proof_irrelevance _ Ha0 Ha) in HL.
      rewrite (proof_irrelevance _ Hb0 Hb) in HL.
      exact HL.
Qed.

Lemma remove_min_preserves_dim2 :
  forall E m, IsGlobalMin E m ->
    ((exists d, inhabited (PosetDimension (sub_order E (fun x => x <> m)) d) /\ d <= 2)
     <->
     (exists d, exec_has_dimension E d /\ d <= 2)).
Proof.
  intros E m Hmin. split.
  - (* HARD: block dim2 -> E dim2 (realizer surgery) *)
    intros [d [[RBdim] Hled]].
    destruct d as [| d'].
    + (* d = 0: block realizer empty => block has <=1 element => E has <=2 *)
      (* Show ep_order E is total, then apply small_E_dim_le_2. *)
      apply small_E_dim_le_2.
      (* the block sub_order: any two block elements are equal *)
      pose proof (dimension_is_realizer RBdim) as HBreal.
      pose proof (dimension_cardinality RBdim) as HBcard.
      assert (HBempty : dimension_realizer RBdim = Empty_set _)
        by (apply cardinalO_empty; exact HBcard).
      (* any two block elements x,y satisfy sub_order both ways => equal *)
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
      (* now: any two elements of E are comparable *)
      intros a b.
      destruct (classic (a = m)) as [Ham | Ham].
      * left. subst a. exact (Hmin b).
      * destruct (classic (b = m)) as [Hbm | Hbm].
        -- right. subst b. exact (Hmin a).
        -- (* a<>m, b<>m : both in block, so a = b *)
           assert (Heqab : a = b)
             by exact (Hblock_eq (exist _ a Ham) (exist _ b Hbm)).
           left. subst b. apply (poset_refl (R := ep_order E)).
    + (* d = S d' : genuine realizer surgery *)
      set (RB := dimension_realizer RBdim).
      pose proof (dimension_is_realizer RBdim) as HBreal.
      pose proof (dimension_cardinality RBdim) as HBcard.
      set (RE := Im _ _ RB (lift_min E m)).
      (* RB is nonempty (cardinal S d' > 0) *)
      destruct (cardinal_invert _ _ _ HBcard) as [RB0 [LB0 [HRBeq [HLB0nin _]]]].
      assert (HLB0in : In _ RB LB0) by (unfold RB; rewrite HRBeq; apply Add_intro2).
      (* RE is a realizer of ep_order E *)
      assert (HRE_real : IsRealizer (ep_order E) RE).
      { constructor.
        - (* every member is a linear extension *)
          intros M HM.
          inversion HM as [LB HLBin M' HMeq]; subst M'.
          subst M.
          apply lift_min_is_linext.
          + exact Hmin.
          + exact (realizer_linear HBreal LB HLBin).
        - (* intersection *)
          intros a b. split.
          + (* ep_order E a b -> forall M in RE, M a b *)
            intros Hab M HM.
            inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
            (* show lift_min E m LB a b *)
            destruct (classic (a = m)) as [Ham | Ham].
            * left. exact Ham.
            * assert (Hbm : b <> m).
              { intro Heq. subst b.
                pose proof (Hmin a) as Hma.
                apply Ham. exact (poset_antisym (R := ep_order E) a m Hab Hma). }
              right. exists Ham, Hbm.
              apply (linear_extends (realizer_linear HBreal LB HLBin)
                       (exist _ a Ham) (exist _ b Hbm)).
              unfold sub_order. simpl. exact Hab.
          + (* (forall M in RE, M a b) -> ep_order E a b *)
            intros Hall.
            destruct (classic (a = m)) as [Ham | Ham].
            * subst a. exact (Hmin b).
            * (* a <> m; first show b <> m using LB0 *)
              assert (HM0in : In _ RE (lift_min E m LB0)).
              { unfold RE. apply Im_intro with (x := LB0).
                - exact HLB0in.
                - reflexivity. }
              pose proof (Hall (lift_min E m LB0) HM0in) as HliftLB0.
              assert (Hbm : b <> m).
              { intro Heq. subst b.
                destruct HliftLB0 as [Ham' | [Ha0 [Hb0 _]]].
                - apply Ham. exact Ham'.
                - apply Hb0. reflexivity. }
              (* now get the block order from every LB in RB *)
              assert (Hblock : sub_order E (fun z => z <> m)
                                 (exist _ a Ham) (exist _ b Hbm)).
              { apply (proj2 (realizer_intersection HBreal
                               (exist _ a Ham) (exist _ b Hbm))).
                intros LB HLBin.
                assert (HMin : In _ RE (lift_min E m LB)).
                { unfold RE. apply Im_intro with (x := LB).
                  - exact HLBin.
                  - reflexivity. }
                pose proof (Hall (lift_min E m LB) HMin) as Hlift.
                destruct Hlift as [Ham' | [Ha0 [Hb0 HL]]].
                - exfalso. apply Ham. exact Ham'.
                - rewrite (proof_irrelevance _ Ha0 Ham) in HL.
                  rewrite (proof_irrelevance _ Hb0 Hbm) in HL.
                  exact HL. }
              unfold sub_order in Hblock. simpl in Hblock. exact Hblock. }
      (* RE has cardinality S d' *)
      assert (HRE_card : cardinal _ RE (S d')).
      { unfold RE.
        apply (cardinal_Im_injective _ _ RB (lift_min E m) (S d')).
        - exact HBcard.
        - intros LB1 LB2 _ _ Heq.
          exact (lift_min_inj E m LB1 LB2 Heq). }
      destruct (exec_dimension_exists E) as [dE [HdE]].
      pose proof (dimension_is_minimum HdE RE (S d') HRE_real HRE_card) as Hle.
      exists dE. split.
      * exact (inhabits HdE).
      * lia.
  - (* EASY: E dim2 -> block dim2 *)
    intros HE.
    pose proof (subposet_reduces_dim (ep_carrier E) (ep_order E)
                  (fun x => x <> m)) as Hred.
    destruct HE as [dE [[HdE] HledE]].
    (* block has a dimension via subposet_dimension_le *)
    destruct (subposet_dimension_le (ep_order E) (fun x => x <> m) dE HdE)
      as [dB [[HdB] HleB]].
    (* dB <= dE <= 2 *)
    exists dB. split.
    + exact (inhabits HdB).
    + lia.
Qed.

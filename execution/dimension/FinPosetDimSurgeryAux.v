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

Section FinPoset.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  (* The subtype order on a subset S of A. *)
  Definition fin_sub_order (S : Ensemble A)
    : {z | Ensembles.In _ S z} -> {z | Ensembles.In _ S z} -> Prop :=
    fun x y => R (proj1_sig x) (proj1_sig y).

  Instance fin_sub_order_poset (S : Ensemble A) : IsPoset _ (fin_sub_order S) :=
    subtype_is_poset R S.

  Definition fin_global_min (m : A) : Prop := forall x, R m x.
  Definition fin_global_max (m : A) : Prop := forall x, R x m.

  (* ---------------------------------------------------------------- *)
  (* A dimension exists (Dushnik-Miller, via the explicit finiteness). *)
  (* ---------------------------------------------------------------- *)

  Lemma fin_dim_exists : exists d, inhabited (PosetDimension R d).
  Proof.
    destruct (finite_cardinal _ _ Hfin) as [n Hn].
    exact (dushnik_miller_exists R n Hn).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* A poset whose order is total has dimension <= 1 (singleton realizer). *)
  (* ---------------------------------------------------------------- *)

  Lemma fin_small_dim_le_2 :
    (forall a b : A, R a b \/ R b a) ->
      exists d, inhabited (PosetDimension R d) /\ d <= 2.
  Proof.
    intros Htot.
    (* The singleton realizer { R } realizes the (total) order. *)
    set (r := Singleton (A -> A -> Prop) R).
    assert (HrReal : IsRealizer R r).
    { constructor.
      - (* every member is a linear extension; the only member is R *)
        intros L HL. apply Singleton_inv in HL. subst L.
        constructor.
        + (* IsTotalOrder R *)
          constructor.
          * exact HR.
          * exact Htot.
        + intros x y Hxy. exact Hxy.
      - intros x y. split.
        + intros Hxy L HL. apply Singleton_inv in HL. subst L. exact Hxy.
        + intros Hall. apply (Hall R). constructor. }
    assert (Hcard1 : cardinal _ r 1).
    { unfold r.
      replace (Singleton (A -> A -> Prop) R)
        with (Add (A -> A -> Prop) (Empty_set _) R).
      - apply card_add.
        + apply card_empty.
        + intro Hbad. destruct Hbad.
      - apply Extensionality_Ensembles. split.
        + intros L HL. destruct HL as [L HL | L HL].
          * destruct HL.
          * exact HL.
        + intros L HL. right. exact HL. }
    destruct fin_dim_exists as [d [Hd]].
    pose proof (dimension_is_minimum Hd r 1 HrReal Hcard1) as Hle.
    exists d. split.
    - exact (inhabits Hd).
    - lia.
  Qed.

  (* ================================================================== *)
  (*  MIN side: lift a linear extension of the block to one of (A,R),    *)
  (*  with m at the bottom.                                              *)
  (* ================================================================== *)

  Definition fin_lift_min (m : A) (LB : {z | z <> m} -> {z | z <> m} -> Prop)
     (a b : A) : Prop :=
     a = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).

  Lemma fin_lift_min_is_linext :
    forall m (LB : {z | z <> m} -> {z | z <> m} -> Prop),
      fin_global_min m ->
      IsLinearExtension (fin_sub_order (fun x => x <> m)) LB ->
      IsLinearExtension R (fin_lift_min m LB).
  Proof.
    intros m LB Hmin HLB.
    pose proof (HLB.(linear_is_total)) as HBtot.
    pose proof (HBtot.(total_is_poset)) as HBpos.
    refine {| linear_is_total := _ ; linear_extends := _ |}.
    - (* IsTotalOrder (fin_lift_min ...) *)
      refine {| total_is_poset := _ ; total_comparable := _ |}.
      + (* IsPoset (fin_lift_min ...) *)
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
          -- (* a = m -> fin_lift_min a c by left *)
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
          (* R a m and R m a -> a = m *)
          pose proof (Hmin a) as Hma.
          pose proof (poset_antisym (R := R) a m Hab Hma) as Heq.
          apply Ham. exact Heq. }
        right. exists Ham, Hbm.
        (* goal: LB (exist a Ham)(exist b Hbm); use block linear_extends *)
        apply (HLB.(linear_extends) (exist _ a Ham) (exist _ b Hbm)).
        unfold fin_sub_order. simpl. exact Hab.
  Qed.

  Lemma fin_lift_min_inj :
    forall m (LB1 LB2 : {z | z <> m} -> {z | z <> m} -> Prop),
      fin_lift_min m LB1 = fin_lift_min m LB2 -> LB1 = LB2.
  Proof.
    intros m LB1 LB2 Heq.
    apply functional_extensionality; intros [a Ha].
    apply functional_extensionality; intros [b Hb].
    (* pointwise equality of the lifted relations at a b *)
    pose proof (equal_f (equal_f Heq a) b) as Hpt.
    unfold fin_lift_min in Hpt.
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

  Lemma fin_remove_min_dim2 :
    forall m, fin_global_min m ->
      ((exists d, inhabited (PosetDimension (fin_sub_order (fun x => x <> m)) d) /\ d <= 2)
       <-> (exists d, inhabited (PosetDimension R d) /\ d <= 2)).
  Proof.
    intros m Hmin. split.
    - (* HARD: block dim2 -> (A,R) dim2 (realizer surgery) *)
      intros [d [[RBdim] Hled]].
      destruct d as [| d'].
      + (* d = 0: block realizer empty => block has <=1 element => A has <=2 *)
        apply fin_small_dim_le_2.
        pose proof (dimension_is_realizer RBdim) as HBreal.
        pose proof (dimension_cardinality RBdim) as HBcard.
        assert (HBempty : dimension_realizer RBdim = Empty_set _)
          by (apply cardinalO_empty; exact HBcard).
        (* any two block elements x,y satisfy fin_sub_order both ways => equal *)
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
        (* now: any two elements of A are comparable *)
        intros a b.
        destruct (classic (a = m)) as [Ham | Ham].
        * left. subst a. exact (Hmin b).
        * destruct (classic (b = m)) as [Hbm | Hbm].
          -- right. subst b. exact (Hmin a).
          -- (* a<>m, b<>m : both in block, so a = b *)
             assert (Heqab : a = b)
               by exact (Hblock_eq (exist _ a Ham) (exist _ b Hbm)).
             left. subst b. apply (poset_refl (R := R)).
      + (* d = S d' : genuine realizer surgery *)
        set (RB := dimension_realizer RBdim).
        pose proof (dimension_is_realizer RBdim) as HBreal.
        pose proof (dimension_cardinality RBdim) as HBcard.
        set (RE := Im _ _ RB (fin_lift_min m)).
        (* RB is nonempty (cardinal S d' > 0) *)
        destruct (cardinal_invert _ _ _ HBcard) as [RB0 [LB0 [HRBeq [HLB0nin _]]]].
        assert (HLB0in : In _ RB LB0) by (unfold RB; rewrite HRBeq; apply Add_intro2).
        (* RE is a realizer of R *)
        assert (HRE_real : IsRealizer R RE).
        { constructor.
          - (* every member is a linear extension *)
            intros M HM.
            inversion HM as [LB HLBin M' HMeq]; subst M'.
            subst M.
            apply fin_lift_min_is_linext.
            + exact Hmin.
            + exact (realizer_linear HBreal LB HLBin).
          - (* intersection *)
            intros a b. split.
            + (* R a b -> forall M in RE, M a b *)
              intros Hab M HM.
              inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
              (* show fin_lift_min m LB a b *)
              destruct (classic (a = m)) as [Ham | Ham].
              * left. exact Ham.
              * assert (Hbm : b <> m).
                { intro Heq. subst b.
                  pose proof (Hmin a) as Hma.
                  apply Ham. exact (poset_antisym (R := R) a m Hab Hma). }
                right. exists Ham, Hbm.
                apply (linear_extends (realizer_linear HBreal LB HLBin)
                         (exist _ a Ham) (exist _ b Hbm)).
                unfold fin_sub_order. simpl. exact Hab.
            + (* (forall M in RE, M a b) -> R a b *)
              intros Hall.
              destruct (classic (a = m)) as [Ham | Ham].
              * subst a. exact (Hmin b).
              * (* a <> m; first show b <> m using LB0 *)
                assert (HM0in : In _ RE (fin_lift_min m LB0)).
                { unfold RE. apply Im_intro with (x := LB0).
                  - exact HLB0in.
                  - reflexivity. }
                pose proof (Hall (fin_lift_min m LB0) HM0in) as HliftLB0.
                assert (Hbm : b <> m).
                { intro Heq. subst b.
                  destruct HliftLB0 as [Ham' | [Ha0 [Hb0 _]]].
                  - apply Ham. exact Ham'.
                  - apply Hb0. reflexivity. }
                (* now get the block order from every LB in RB *)
                assert (Hblock : fin_sub_order (fun z => z <> m)
                                   (exist _ a Ham) (exist _ b Hbm)).
                { apply (proj2 (realizer_intersection HBreal
                                 (exist _ a Ham) (exist _ b Hbm))).
                  intros LB HLBin.
                  assert (HMin : In _ RE (fin_lift_min m LB)).
                  { unfold RE. apply Im_intro with (x := LB).
                    - exact HLBin.
                    - reflexivity. }
                  pose proof (Hall (fin_lift_min m LB) HMin) as Hlift.
                  destruct Hlift as [Ham' | [Ha0 [Hb0 HL]]].
                  - exfalso. apply Ham. exact Ham'.
                  - rewrite (proof_irrelevance _ Ha0 Ham) in HL.
                    rewrite (proof_irrelevance _ Hb0 Hbm) in HL.
                    exact HL. }
                unfold fin_sub_order in Hblock. simpl in Hblock. exact Hblock. }
        (* RE has cardinality S d' *)
        assert (HRE_card : cardinal _ RE (S d')).
        { unfold RE.
          apply (cardinal_Im_injective _ _ RB (fin_lift_min m) (S d')).
          - exact HBcard.
          - intros LB1 LB2 _ _ Heq.
            exact (fin_lift_min_inj m LB1 LB2 Heq). }
        destruct fin_dim_exists as [dE [HdE]].
        pose proof (dimension_is_minimum HdE RE (S d') HRE_real HRE_card) as Hle.
        exists dE. split.
        * exact (inhabits HdE).
        * lia.
    - (* EASY: (A,R) dim2 -> block dim2 (subposet_dimension_le; no uniqueness needed) *)
      intros HE.
      destruct HE as [dE [[HdE] HledE]].
      destruct (subposet_dimension_le R (fun x => x <> m) dE HdE)
        as [dB [[HdB] HleB]].
      (* dB <= dE <= 2 *)
      exists dB. split.
      + exact (inhabits HdB).
      + lia.
  Qed.

End FinPoset.

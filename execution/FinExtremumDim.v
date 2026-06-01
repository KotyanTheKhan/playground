(* exact dimension of adding a global extremum; binary exact barrier dimension

   Part 1: a singleton-dimension helper [fin_singleton_dim0] and the exact
   "adding a global minimum" lemma [fin_add_min_dim].  The hard direction
   (dW <= max d 1) PORTS the realizer-surgery of [fin_remove_min_dim2] from
   FinPosetDimSurgery.v, but keeps the EXACT block cardinality (no chaining to
   <= 2).  No new mathematics. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim.

Section FinExtremumDim.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  (* A poset with at most one element has dimension 0 (empty realizer). *)
  Lemma fin_singleton_dim0 :
    (forall x y : A, x = y) -> PosetDimension R 0.
  Proof.
    intro Hall.
    refine {| dimension_realizer := Empty_set _;
              dimension_is_realizer := _;
              dimension_cardinality := _;
              dimension_is_minimum := _ |}.
    - (* IsRealizer R (Empty_set _) *)
      constructor.
      + (* realizer_linear: vacuous *)
        intros L HL. destruct HL.
      + (* realizer_intersection *)
        intros x y. split.
        * (* R x y -> forall L in empty, L x y : vacuous *)
          intros _ L HL. destruct HL.
        * (* (forall L in empty, L x y) -> R x y *)
          intros _. rewrite (Hall x y). apply poset_refl.
    - (* cardinal _ (Empty_set _) 0 *)
      apply card_empty.
    - (* dimension_is_minimum: 0 <= n *)
      intros r n _ _. lia.
  Qed.

End FinExtremumDim.

(* The exact dimension of adding a global minimum to a finite poset: if the
   block (A minus m) has dimension d and there is some element distinct from m,
   then (A,R) has dimension exactly max d 1. *)
Lemma fin_add_min_dim :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (m : A),
    fin_global_min R m ->
    (exists x, x <> m) ->
    forall d, PosetDimension (fin_sub_order R (fun x => x <> m)) d ->
      forall dW, PosetDimension R dW -> dW = Nat.max d 1.
Proof.
  intros A R HR Hfin m Hmin Hex d Hd_block dW HdW.
  apply Nat.le_antisymm.
  - (* dW <= Nat.max d 1 *)
    destruct d as [| d'].
    + (* d = 0 : R is total; singleton realizer gives dW <= 1 *)
      pose proof (dimension_is_realizer Hd_block) as HBreal.
      pose proof (dimension_cardinality Hd_block) as HBcard.
      assert (HBempty : dimension_realizer Hd_block = Empty_set _)
        by (apply cardinalO_empty; exact HBcard).
      (* any two block elements are equal *)
      assert (Hblock_eq :
        forall (x y : {z : A | z <> m}), proj1_sig x = proj1_sig y).
      { intros x y.
        assert (Hxy : fin_sub_order R (fun z => z <> m) x y).
        { apply (proj2 (realizer_intersection HBreal x y)).
          intros L HL. rewrite HBempty in HL. destruct HL. }
        assert (Hyx : fin_sub_order R (fun z => z <> m) y x).
        { apply (proj2 (realizer_intersection HBreal y x)).
          intros L HL. rewrite HBempty in HL. destruct HL. }
        pose proof (fin_sub_order_poset R (fun z => z <> m)) as Hsp.
        assert (Heqxy : x = y) by exact (Hsp.(poset_antisym) x y Hxy Hyx).
        f_equal. exact Heqxy. }
      (* R is total *)
      assert (Htot : forall a b : A, R a b \/ R b a).
      { intros a b.
        destruct (classic (a = m)) as [Ham | Ham].
        - left. subst a. exact (Hmin b).
        - destruct (classic (b = m)) as [Hbm | Hbm].
          + right. subst b. exact (Hmin a).
          + assert (Heqab : a = b)
              by exact (Hblock_eq (exist _ a Ham) (exist _ b Hbm)).
            left. subst b. apply (poset_refl (R := R)). }
      (* singleton realizer { R } : dW <= 1 *)
      set (r := Singleton (A -> A -> Prop) R).
      assert (HrReal : IsRealizer R r).
      { constructor.
        - intros L HL. apply Singleton_inv in HL. subst L.
          constructor.
          + constructor.
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
      pose proof (dimension_is_minimum HdW r 1 HrReal Hcard1) as Hle.
      lia.
    + (* d = S d' : realizer surgery, exact cardinality S d' *)
      set (RB := dimension_realizer Hd_block).
      pose proof (dimension_is_realizer Hd_block) as HBreal.
      pose proof (dimension_cardinality Hd_block) as HBcard.
      set (RE := Im _ _ RB (fin_lift_min m)).
      destruct (cardinal_invert _ _ _ HBcard) as [RB0 [LB0 [HRBeq [HLB0nin _]]]].
      assert (HLB0in : In _ RB LB0) by (unfold RB; rewrite HRBeq; apply Add_intro2).
      (* RE is a realizer of R *)
      assert (HRE_real : IsRealizer R RE).
      { constructor.
        - intros M HM.
          inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
          apply (@fin_lift_min_is_linext A R HR m LB).
          + exact Hmin.
          + exact (realizer_linear HBreal LB HLBin).
        - intros a b. split.
          + intros Hab M HM.
            inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
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
          + intros Hall.
            destruct (classic (a = m)) as [Ham | Ham].
            * subst a. exact (Hmin b).
            * assert (HM0in : In _ RE (fin_lift_min m LB0)).
              { unfold RE. apply Im_intro with (x := LB0).
                - exact HLB0in.
                - reflexivity. }
              pose proof (Hall (fin_lift_min m LB0) HM0in) as HliftLB0.
              assert (Hbm : b <> m).
              { intro Heq. subst b.
                destruct HliftLB0 as [Ham' | [Ha0 [Hb0 _]]].
                - apply Ham. exact Ham'.
                - apply Hb0. reflexivity. }
              assert (Hblock : fin_sub_order R (fun z => z <> m)
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
      pose proof (dimension_is_minimum HdW RE (S d') HRE_real HRE_card) as Hle.
      lia.
  - (* Nat.max d 1 <= dW *)
    apply Nat.max_lub.
    + (* d <= dW *)
      destruct (subposet_dimension_le R (fun x => x <> m) dW HdW)
        as [dq [Hinh Hle]].
      destruct Hinh as [Hq].
      pose proof (@fin_posdim_unique _ (fin_sub_order R (fun x => x <> m))
                    (fin_sub_order_poset R (fun x => x <> m)) d dq
                    Hd_block Hq) as Heq.
      rewrite Heq. exact Hle.
    + (* 1 <= dW *)
      destruct Hex as [x Hxm].
      apply (dim_ge_1_of_two R dW HdW).
      exists x, m. exact Hxm.
Qed.

(* The exact dimension of adding a global maximum to a finite poset: if the
   block (A minus m) has dimension d and there is some element distinct from m,
   then (A,R) has dimension exactly max d 1.  Dual of [fin_add_min_dim]. *)
Lemma fin_add_max_dim :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (m : A),
    fin_global_max R m ->
    (exists x, x <> m) ->
    forall d, PosetDimension (fin_sub_order R (fun x => x <> m)) d ->
      forall dW, PosetDimension R dW -> dW = Nat.max d 1.
Proof.
  intros A R HR Hfin m Hmax Hex d Hd_block dW HdW.
  apply Nat.le_antisymm.
  - (* dW <= Nat.max d 1 *)
    destruct d as [| d'].
    + (* d = 0 : R is total; singleton realizer gives dW <= 1 *)
      pose proof (dimension_is_realizer Hd_block) as HBreal.
      pose proof (dimension_cardinality Hd_block) as HBcard.
      assert (HBempty : dimension_realizer Hd_block = Empty_set _)
        by (apply cardinalO_empty; exact HBcard).
      (* any two block elements are equal *)
      assert (Hblock_eq :
        forall (x y : {z : A | z <> m}), proj1_sig x = proj1_sig y).
      { intros x y.
        assert (Hxy : fin_sub_order R (fun z => z <> m) x y).
        { apply (proj2 (realizer_intersection HBreal x y)).
          intros L HL. rewrite HBempty in HL. destruct HL. }
        assert (Hyx : fin_sub_order R (fun z => z <> m) y x).
        { apply (proj2 (realizer_intersection HBreal y x)).
          intros L HL. rewrite HBempty in HL. destruct HL. }
        pose proof (fin_sub_order_poset R (fun z => z <> m)) as Hsp.
        assert (Heqxy : x = y) by exact (Hsp.(poset_antisym) x y Hxy Hyx).
        f_equal. exact Heqxy. }
      (* R is total *)
      assert (Htot : forall a b : A, R a b \/ R b a).
      { intros a b.
        destruct (classic (a = m)) as [Ham | Ham].
        - right. subst a. exact (Hmax b).
        - destruct (classic (b = m)) as [Hbm | Hbm].
          + left. subst b. exact (Hmax a).
          + assert (Heqab : a = b)
              by exact (Hblock_eq (exist _ a Ham) (exist _ b Hbm)).
            left. subst b. apply (poset_refl (R := R)). }
      (* singleton realizer { R } : dW <= 1 *)
      set (r := Singleton (A -> A -> Prop) R).
      assert (HrReal : IsRealizer R r).
      { constructor.
        - intros L HL. apply Singleton_inv in HL. subst L.
          constructor.
          + constructor.
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
      pose proof (dimension_is_minimum HdW r 1 HrReal Hcard1) as Hle.
      lia.
    + (* d = S d' : realizer surgery, exact cardinality S d' *)
      set (RB := dimension_realizer Hd_block).
      pose proof (dimension_is_realizer Hd_block) as HBreal.
      pose proof (dimension_cardinality Hd_block) as HBcard.
      set (RE := Im _ _ RB (fin_lift_max m)).
      destruct (cardinal_invert _ _ _ HBcard) as [RB0 [LB0 [HRBeq [HLB0nin _]]]].
      assert (HLB0in : In _ RB LB0) by (unfold RB; rewrite HRBeq; apply Add_intro2).
      (* RE is a realizer of R *)
      assert (HRE_real : IsRealizer R RE).
      { constructor.
        - intros M HM.
          inversion HM as [LB HLBin M' HMeq]; subst M'. subst M.
          apply (@fin_lift_max_is_linext A R HR m LB).
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
              assert (Hblock : fin_sub_order R (fun z => z <> m)
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
      (* RE has cardinality S d' *)
      assert (HRE_card : cardinal _ RE (S d')).
      { unfold RE.
        apply (cardinal_Im_injective _ _ RB (fin_lift_max m) (S d')).
        - exact HBcard.
        - intros LB1 LB2 _ _ Heq.
          exact (fin_lift_max_inj m LB1 LB2 Heq). }
      pose proof (dimension_is_minimum HdW RE (S d') HRE_real HRE_card) as Hle.
      lia.
  - (* Nat.max d 1 <= dW *)
    apply Nat.max_lub.
    + (* d <= dW *)
      destruct (subposet_dimension_le R (fun x => x <> m) dW HdW)
        as [dq [Hinh Hle]].
      destruct Hinh as [Hq].
      pose proof (@fin_posdim_unique _ (fin_sub_order R (fun x => x <> m))
                    (fin_sub_order_poset R (fun x => x <> m)) d dq
                    Hd_block Hq) as Heq.
      rewrite Heq. exact Hle.
    + (* 1 <= dW *)
      destruct Hex as [x Hxm].
      apply (dim_ge_1_of_two R dW HdW).
      exists x, m. exact Hxm.
Qed.

(* The all-cases binary exact barrier dimension.  Combines the two exact
   "add a global extremum" lemmas (handling the degenerate dim-0 blocks, which
   force a global min / global max) with the both-blocks-positive max-formula
   [fin_barrier_dimension].  The +1 in the formula accounts for the dim-0
   degenerate blocks, whose whole-poset dimension is exactly 1, not 0. *)
Lemma fin_barrier_dimension_full :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (L U : Ensemble A),
    fin_is_barrier R L U ->
    forall dL dU dW,
      PosetDimension (fin_sub_order R L) dL ->
      PosetDimension (fin_sub_order R U) dU ->
      PosetDimension R dW ->
      dW = Nat.max 1 (Nat.max dL dU).
Proof.
  intros A R HR Hfin L U HB dL dU dW HdL HdU HdW.
  destruct dL as [| dL'].
  - (* dL = 0 : lower block singleton -> global min m, U = complement of {m} *)
    destruct (fin_block_dim0_global_min R L U HB HdL) as [m [Hmin HUeq]].
    assert (HUfun : U = (fun x => x <> m)).
    { apply functional_extensionality. intro x.
      apply propositional_extensionality. exact (HUeq x). }
    rewrite HUfun in HdU.
    (* U is inhabited (4th conjunct of fin_is_barrier) -> some x <> m *)
    destruct HB as [_ [_ [_ [[y HyU] _]]]].
    pose proof (ex_intro (fun x => x <> m) y (proj1 (HUeq y) HyU)) as Hex.
    pose proof (fin_add_min_dim R Hfin m Hmin Hex dU HdU dW HdW) as HdWeq.
    rewrite HdWeq. lia.
  - destruct dU as [| dU'].
    + (* dU = 0 : upper block singleton -> global max m, L = complement of {m} *)
      destruct (fin_block_dim0_global_max R L U HB HdU) as [m [Hmax HLeq]].
      assert (HLfun : L = (fun x => x <> m)).
      { apply functional_extensionality. intro x.
        apply propositional_extensionality. exact (HLeq x). }
      rewrite HLfun in HdL.
      (* L is inhabited (3rd conjunct of fin_is_barrier) -> some x <> m *)
      destruct HB as [_ [_ [[y HyL] _]]].
      pose proof (ex_intro (fun x => x <> m) y (proj1 (HLeq y) HyL)) as Hex.
      pose proof (fin_add_max_dim R Hfin m Hmax Hex (S dL') HdL dW HdW) as HdWeq.
      rewrite HdWeq. lia.
    + (* both blocks positive: max formula *)
      pose proof (fin_barrier_dimension R L U HB (S dL') (S dU') dW
                    HdL HdU HdW (Nat.lt_0_succ dL') (Nat.lt_0_succ dU')) as Hmaxeq.
      rewrite Hmaxeq. lia.
Qed.

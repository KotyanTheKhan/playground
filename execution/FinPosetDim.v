(* generic finite-poset barrier dim<=2 levers

   Carrier-generic ports of execution/BarrierDim2.v and the barrier_dimension
   theorem from execution/Ordinal.v, on a bare finite poset (A, R) with
   [IsPoset A R] and [Finite A (Full_set A)].  No new mathematics; only the
   carrier / wrapper names change. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems LinearSum.
From Execution Require Import DimIso FinPosetDimSurgery.

Section FinPosetDimBarrier.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  #[local] Existing Instance fin_sub_order_poset.

  (* ---------------------------------------------------------------- *)
  (* Generic barrier definition                                        *)
  (* ---------------------------------------------------------------- *)

  Definition fin_is_barrier (L U : Ensemble A) : Prop :=
    (forall x, Ensembles.In _ L x \/ Ensembles.In _ U x) /\
    (forall x, ~ (Ensembles.In _ L x /\ Ensembles.In _ U x)) /\
    (exists x, Ensembles.In _ L x) /\ (exists y, Ensembles.In _ U y) /\
    (forall x y, Ensembles.In _ L x -> Ensembles.In _ U y -> R x y).

  (* ---------------------------------------------------------------- *)
  (* Helper: U-element above L means no U→L edge                      *)
  (* ---------------------------------------------------------------- *)

  Lemma fin_barrier_upper_above :
    forall L U, fin_is_barrier L U ->
      forall x y, Ensembles.In _ U x -> Ensembles.In _ L y -> ~ R x y.
  Proof.
    intros L U HB x y HxU HyL Hxy.
    destruct HB as [_ [Hdisj [_ [_ Hbelow]]]].
    assert (Hyx : R y x) by (apply Hbelow; assumption).
    assert (Heq : x = y) by
      (apply (poset_antisym (R := R)); assumption).
    apply (Hdisj x).
    split.
    - rewrite Heq. exact HyL.
    - exact HxU.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Generic barrier sub-poset uniqueness                             *)
  (* ---------------------------------------------------------------- *)

  Lemma fin_posdim_unique :
    forall (B : Type) (S : B -> B -> Prop) `{IsPoset B S} d d',
      PosetDimension S d -> PosetDimension S d' -> d = d'.
  Proof.
    intros B S HBS d d' Hd Hd'.
    apply Nat.le_antisymm.
    - apply (dimension_is_minimum Hd (dimension_realizer Hd')
               d' (dimension_is_realizer Hd') (dimension_cardinality Hd')).
    - apply (dimension_is_minimum Hd' (dimension_realizer Hd)
               d (dimension_is_realizer Hd) (dimension_cardinality Hd)).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* dim-0 block = singleton = global extremum                        *)
  (* ---------------------------------------------------------------- *)

  Lemma fin_block_dim0_global_min :
    forall L U, fin_is_barrier L U ->
      PosetDimension (fin_sub_order R L) 0 ->
      exists m, fin_global_min R m /\ (forall x, Ensembles.In _ U x <-> x <> m).
  Proof.
    intros L U HB Hdim0.
    destruct HB as [Hcov [Hdisj [HinhL [HinhU Hbelow]]]].
    destruct HinhL as [m Hm].
    exists m.
    pose proof (dimension_cardinality Hdim0) as Hcard.
    pose proof (cardinalO_empty _ _ Hcard) as Hemp.
    pose proof (dimension_is_realizer Hdim0) as Hreal.
    (* Every pair in the L-sub-poset is related (vacuous realizer). *)
    assert (Huniv : forall a b : {z | Ensembles.In _ L z},
                      fin_sub_order R L a b).
    { intros a b.
      apply (realizer_intersection Hreal a b).
      intros L' HL'.
      rewrite Hemp in HL'.
      destruct HL'. }
    (* Hence every element of L equals m. *)
    assert (HallL : forall x (Hx : Ensembles.In _ L x), x = m).
    { intros x Hx.
      pose (a := exist (fun z => Ensembles.In _ L z) x Hx).
      pose (b := exist (fun z => Ensembles.In _ L z) m Hm).
      assert (Hab : a = b).
      { apply (poset_antisym a b).
        - exact (Huniv a b).
        - exact (Huniv b a). }
      change x with (proj1_sig a).
      rewrite Hab. reflexivity. }
    split.
    - (* fin_global_min R m: every x satisfies R m x *)
      intro x.
      destruct (Hcov x) as [HxL | HxU].
      + rewrite (HallL x HxL). apply poset_refl.
      + exact (Hbelow m x Hm HxU).
    - (* U = complement of {m} *)
      intro x; split.
      + intro HxU. intro Heq. subst x.
        exact (Hdisj m (conj Hm HxU)).
      + intro Hne.
        destruct (Hcov x) as [HxL | HxU].
        * exfalso. apply Hne. exact (HallL x HxL).
        * exact HxU.
  Qed.

  Lemma fin_block_dim0_global_max :
    forall L U, fin_is_barrier L U ->
      PosetDimension (fin_sub_order R U) 0 ->
      exists m, fin_global_max R m /\ (forall x, Ensembles.In _ L x <-> x <> m).
  Proof.
    intros L U HB Hdim0.
    destruct HB as [Hcov [Hdisj [HinhL [HinhU Hbelow]]]].
    destruct HinhU as [m Hm].
    exists m.
    pose proof (dimension_cardinality Hdim0) as Hcard.
    pose proof (cardinalO_empty _ _ Hcard) as Hemp.
    pose proof (dimension_is_realizer Hdim0) as Hreal.
    assert (Huniv : forall a b : {z | Ensembles.In _ U z},
                      fin_sub_order R U a b).
    { intros a b.
      apply (realizer_intersection Hreal a b).
      intros L' HL'.
      rewrite Hemp in HL'.
      destruct HL'. }
    assert (HallU : forall x (Hx : Ensembles.In _ U x), x = m).
    { intros x Hx.
      pose (a := exist (fun z => Ensembles.In _ U z) x Hx).
      pose (b := exist (fun z => Ensembles.In _ U z) m Hm).
      assert (Hab : a = b).
      { apply (poset_antisym a b).
        - exact (Huniv a b).
        - exact (Huniv b a). }
      change x with (proj1_sig a).
      rewrite Hab. reflexivity. }
    split.
    - intro x.
      destruct (Hcov x) as [HxL | HxU].
      + exact (Hbelow x m HxL Hm).
      + rewrite (HallU x HxU). apply poset_refl.
    - intro x; split.
      + intro HxL. intro Heq. subst x.
        exact (Hdisj m (conj HxL Hm)).
      + intro Hne.
        destruct (Hcov x) as [HxL | HxU].
        * exact HxL.
        * exfalso. apply Hne. exact (HallU x HxU).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* fin_barrier_dimension: dim = max of block dims (both > 0)        *)
  (* ---------------------------------------------------------------- *)

  Section FinBarrierDimension.
    Context (L U : Ensemble A).
    Context (HB : fin_is_barrier L U).

    #[local] Notation RL := (fin_sub_order R L).
    #[local] Notation RU := (fin_sub_order R U).
    #[local] Notation SumT :=
      ({x : A | Ensembles.In _ L x} + {x : A | Ensembles.In _ U x})%type.
    #[local] Notation SumRel := (LinearSumRel RL RU).

    #[local] Instance RL_poset : IsPoset _ RL := fin_sub_order_poset R L.
    #[local] Instance RU_poset : IsPoset _ RU := fin_sub_order_poset R U.
    #[local] Instance SumRel_poset : IsPoset SumT SumRel :=
      LinearSum_IsPoset RL RU.

    Lemma fin_barrier_not_L_in_U :
      forall x, ~ Ensembles.In _ L x -> Ensembles.In _ U x.
    Proof.
      intros x HnL.
      destruct HB as [Hcov _].
      destruct (Hcov x) as [HxL | HxU]; [contradiction | exact HxU].
    Qed.

    Definition fin_bd_f (x : A) : SumT :=
      match excluded_middle_informative (Ensembles.In _ L x) with
      | left h  => inl (exist _ x h)
      | right h => inr (exist _ x (fin_barrier_not_L_in_U x h))
      end.

    Definition fin_bd_g (s : SumT) : A :=
      match s with
      | inl p => proj1_sig p
      | inr p => proj1_sig p
      end.

    Lemma fin_bd_gf : forall a, fin_bd_g (fin_bd_f a) = a.
    Proof.
      intro a. unfold fin_bd_f, fin_bd_g.
      destruct (excluded_middle_informative (Ensembles.In _ L a)); reflexivity.
    Qed.

    Lemma fin_bd_fg : forall s, fin_bd_f (fin_bd_g s) = s.
    Proof.
      intro s. unfold fin_bd_f, fin_bd_g.
      destruct s as [[x Hx] | [x Hx]]; simpl.
      - destruct (excluded_middle_informative (Ensembles.In _ L x)) as [h | h].
        + f_equal. f_equal. apply proof_irrelevance.
        + contradiction.
      - destruct (excluded_middle_informative (Ensembles.In _ L x)) as [h | h].
        + exfalso. destruct HB as [_ [Hdisj _]]. apply (Hdisj x). split; assumption.
        + f_equal. f_equal. apply proof_irrelevance.
    Qed.

    Lemma fin_bd_iso :
      forall a a', R a a' <-> SumRel (fin_bd_f a) (fin_bd_f a').
    Proof.
      intros a a'. unfold fin_bd_f.
      destruct (excluded_middle_informative (Ensembles.In _ L a)) as [HaL | HaU];
      destruct (excluded_middle_informative (Ensembles.In _ L a')) as [Ha'L | Ha'U].
      - (* both in L *)
        split.
        + intro Hord. apply SumAA. unfold fin_sub_order. simpl. exact Hord.
        + intro Hsum. inversion Hsum as [x y Hxy Heqx Heqy | | ]; subst.
          unfold fin_sub_order in Hxy. simpl in Hxy. exact Hxy.
      - (* a in L, a' not in L => a' in U *)
        pose proof (fin_barrier_not_L_in_U a' Ha'U) as Ha'Uin.
        split.
        + intro _Hord. apply SumAB.
        + intro _Hsum.
          destruct HB as [_ [_ [_ [_ Hbelow]]]].
          apply Hbelow; assumption.
      - (* a not in L (so in U), a' in L *)
        pose proof (fin_barrier_not_L_in_U a HaU) as HaUin.
        split.
        + intro Hord. exfalso.
          exact (fin_barrier_upper_above L U HB a a' HaUin Ha'L Hord).
        + intro Hsum. inversion Hsum.
      - (* both not in L (both in U) *)
        pose proof (fin_barrier_not_L_in_U a HaU) as HaUin.
        pose proof (fin_barrier_not_L_in_U a' Ha'U) as Ha'Uin.
        split.
        + intro Hord. apply SumBB. unfold fin_sub_order. simpl. exact Hord.
        + intro Hsum. inversion Hsum as [| x y Hxy Heqx Heqy | ]; subst.
          unfold fin_sub_order in Hxy. simpl in Hxy. exact Hxy.
    Qed.

    Theorem fin_barrier_dimension_section :
      forall dL dU d,
        PosetDimension RL dL ->
        PosetDimension RU dU ->
        PosetDimension R d ->
        0 < dL -> 0 < dU -> d = Nat.max dL dU.
    Proof.
      intros dL dU d HdL HdU Hd HposL HposU.
      (* Transport the whole-poset dimension to the linear-sum poset. *)
      assert (HdSum : PosetDimension SumRel d).
      { apply (dimension_iso A SumT R SumRel
                             fin_bd_f fin_bd_g fin_bd_gf fin_bd_fg fin_bd_iso d Hd). }
      exact (linear_sum_dimension RL RU dL dU d HdL HdU HdSum HposL HposU).
    Qed.

  End FinBarrierDimension.

  Theorem fin_barrier_dimension :
    forall L U, fin_is_barrier L U ->
      forall dL dU d,
        PosetDimension (fin_sub_order R L) dL ->
        PosetDimension (fin_sub_order R U) dU ->
        PosetDimension R d ->
        0 < dL -> 0 < dU -> d = Nat.max dL dU.
  Proof.
    intros L U HB dL dU d HdL HdU Hd HposL HposU.
    exact (fin_barrier_dimension_section L U HB dL dU d HdL HdU Hd HposL HposU).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The lever: barrier with both blocks dim<=2 => whole dim<=2       *)
  (* ---------------------------------------------------------------- *)

  Lemma fin_barrier_dim_le2 :
    forall L U, fin_is_barrier L U ->
      (exists d, inhabited (PosetDimension (fin_sub_order R L) d) /\ d <= 2) ->
      (exists d, inhabited (PosetDimension (fin_sub_order R U) d) /\ d <= 2) ->
      (exists d, inhabited (PosetDimension R d) /\ d <= 2).
  Proof.
    intros L U HB [dL [ [HdL] HleL ]] [dU [ [HdU] HleU ]].
    destruct dL as [|dL'].
    - (* dL = 0: lower block singleton -> global min *)
      destruct (fin_block_dim0_global_min L U HB HdL) as [m [Hmin HUeq]].
      assert (HUfun : U = (fun x => x <> m)).
      { apply functional_extensionality. intro x.
        apply propositional_extensionality. exact (HUeq x). }
      rewrite HUfun in HdU.
      apply (proj1 (fin_remove_min_dim2 R Hfin m Hmin)).
      exists dU. split.
      + exact (inhabits HdU).
      + exact HleU.
    - destruct dU as [|dU'].
      + (* dU = 0: upper block singleton -> global max *)
        destruct (fin_block_dim0_global_max L U HB HdU) as [m [Hmax HLeq]].
        assert (HLfun : L = (fun x => x <> m)).
        { apply functional_extensionality. intro x.
          apply propositional_extensionality. exact (HLeq x). }
        rewrite HLfun in HdL.
        apply (proj1 (fin_remove_max_dim2 R Hfin m Hmax)).
        exists (S dL'). split.
        * exact (inhabits HdL).
        * exact HleL.
      + (* both > 0: apply the max-formula *)
        destruct (fin_dim_exists R Hfin) as [d [Hd]].
        pose proof (fin_barrier_dimension L U HB (S dL') (S dU') d
                      HdL HdU Hd
                      (Nat.lt_0_succ dL') (Nat.lt_0_succ dU')) as Hmax.
        exists d. split.
        * exact (inhabits Hd).
        * rewrite Hmax. lia.
  Qed.

End FinPosetDimBarrier.
Print Assumptions fin_barrier_dim_le2.

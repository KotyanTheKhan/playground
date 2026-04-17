From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall.

Section DilworthBackward.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* ========================================================================= *)
  (* Helper Lemmas for Above and Below                                         *)
  (* ========================================================================= *)

  Lemma la_in_Above : forall la,
    IsAntichain R la ->
    Included A la (Above R la).
  Proof.
    intros la Ha x Hx.
    destruct Ha as [Hinhab Hanti].
    unfold Above. exists x. split; auto.
    apply poset_refl.
  Qed.

  Lemma la_in_Below : forall la,
    IsAntichain R la ->
    Included A la (Below R la).
  Proof.
    intros la Ha x Hx.
    destruct Ha as [Hinhab Hanti].
    unfold Below. exists x. split; auto.
    apply poset_refl.
  Qed.

  Lemma largest_antichain_in_Above : forall la w,
    IsLargestAntichain R (Full_set A) la w ->
    Inhabited A (Above R la) ->
    forall s n, IsAntichain R s -> Included A s (Above R la) -> 
                cardinal A s n -> n <= w.
  Proof.
    intros la w Hla Hinhab_above s n Hs Hincl Hcard_s.
    destruct Hla as [Hanti Hincl_la Hcard Hmax].
    apply (Hmax s n Hs); [intros x Hx; apply Full_intro | exact Hcard_s].
  Qed.

  Lemma largest_antichain_in_Below : forall la w,
    IsLargestAntichain R (Full_set A) la w ->
    Inhabited A (Below R la) ->
    forall s n, IsAntichain R s -> Included A s (Below R la) -> 
                cardinal A s n -> n <= w.
  Proof.
    intros la w Hla Hinhab_below s n Hs Hincl Hcard_s.
    destruct Hla as [Hanti Hincl_la Hcard Hmax].
    apply (Hmax s n Hs); [intros x Hx; apply Full_intro | exact Hcard_s].
  Qed.

  Lemma above_contains_la : forall la,
    IsAntichain R la ->
    Inhabited A (Above R la).
  Proof.
    intros la Ha.
    destruct Ha as [Hinhab _].
    destruct Hinhab as [a Ha].
    apply Inhabited_intro with a.
    unfold Above. exists a. split; auto.
    apply poset_refl.
  Qed.

  Lemma below_contains_la : forall la,
    IsAntichain R la ->
    Inhabited A (Below R la).
  Proof.
    intros la Ha.
    destruct Ha as [Hinhab _].
    destruct Hinhab as [a Ha].
    apply Inhabited_intro with a.
    unfold Below. exists a. split; auto.
    apply poset_refl.
  Qed.

  Lemma min_elements_eq_la : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    forall x, In A sub x ->
      ((forall y, In A sub y -> R y x -> y = x) <-> In A la x).
  Proof.
    intros sub la w Hla Habove x Hx.
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    split.
    - intro Hmin.
      destruct (Habove x Hx) as [a [Ha_la Hax]].
      assert (Ha_sub : In A sub a) by exact (Hincl_la a Ha_la).
      assert (Haeqx : a = x) by exact (Hmin a Ha_sub Hax).
      subst a. exact Ha_la.
    - intro Hx_la.
      intros y Hy_sub Hyx.
      destruct (Habove y Hy_sub) as [b [Hb_la Hby]].
      assert (Hbx : R b x) by exact (poset_trans b y x Hby Hyx).
      assert (Hbeqx : b = x) by exact (Hincompat b x Hb_la Hx_la (or_introl Hbx)).
      subst b.
      exact (poset_antisym y x Hyx Hby).
  Qed.

  Definition StrictSucc (sub S : Ensemble A) : Ensemble A :=
    fun y => In A sub y /\ exists x, In A S x /\ R x y /\ x <> y.

  Lemma dilworth_hall_defect : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    forall S ns nn,
      Included A S sub ->
      cardinal A S ns ->
      cardinal A (StrictSucc sub S) nn ->
      ns <= nn + w.
  Proof.
    intros sub la w Hla Habove S ns nn HinclS HcardS HcardNS.
    destruct Hla as [_ Hincl_la Hcard_la Hmax].
    pose (M := fun x => In A S x /\ ~ In A (StrictSucc sub S) x).
    assert (HfinS : Finite A S) by exact (cardinal_finite A S ns HcardS).
    assert (HfinM : Finite A M).
    { apply (Finite_downward_closed A S HfinS). intros x [HxS _]. exact HxS. }
    destruct (finite_cardinal A M HfinM) as [m HcardM].
    assert (Hincl_S : Included A S (Union A M (StrictSucc sub S))).
    { intros x HxS.
      destruct (classic (In A (StrictSucc sub S) x)) as [Hxin | Hxout].
      - apply Union_intror. exact Hxin.
      - apply Union_introl. exact (conj HxS Hxout). }
    assert (HdisM : forall x, In A M x -> ~ In A (StrictSucc sub S) x).
    { intros x [_ Hxout]. exact Hxout. }
    assert (HcardMN : cardinal A (Union A M (StrictSucc sub S)) (m + nn)).
    { exact (cardinal_disjoint_union_gen A M (StrictSucc sub S) m nn HdisM HcardM HcardNS). }
    assert (Hns_le : ns <= m + nn).
    { exact (incl_card_le A S (Union A M (StrictSucc sub S)) ns (m + nn)
               HcardS HcardMN Hincl_S). }
    assert (HM_le_w : m <= w).
    { destruct m as [| m'].
      - lia.
      - assert (HinhM : Inhabited A M).
        { inversion HcardM as [| M' n' Hcard' x Hx_notin]. subst.
          apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
        assert (HincompM : forall x y, In A M x -> In A M y -> (R x y \/ R y x) -> x = y).
        { intros x y [HxS HxnN] [HyS HynN] Hcomp.
          destruct Hcomp as [Hxy | Hyx].
          - destruct (classic (x = y)) as [Heq | Hneq]; [exact Heq |].
            exfalso. apply HynN.
            exact (conj (HinclS y HyS) (ex_intro _ x (conj HxS (conj Hxy Hneq)))).
          - destruct (classic (x = y)) as [Heq | Hneq]; [exact Heq |].
            exfalso. apply HxnN.
            exact (conj (HinclS x HxS)
                        (ex_intro _ y (conj HyS (conj Hyx (fun h => Hneq (eq_sym h)))))). }
        exact (Hmax M _ (Build_IsAntichain R M HinhM HincompM)
                        (fun x HxM => HinclS x (proj1 HxM))
                        HcardM). }
    lia.
  Qed.

  (* ========================================================================= *)
  (* Special Cases: Width 0 and Width 1                                        *)
  (* ========================================================================= *)

  Lemma empty_antichain_contradiction : forall (s : Ensemble A),
    IsAntichain R s -> cardinal A s 0 -> False.
  Proof.
    intros s Ha Hcard.
    destruct Ha as [Hinhab _].
    destruct Hinhab as [a Ha].
    inversion Hcard. subst. inversion Ha.
  Qed.

  Lemma singleton_antichain_is_chain : forall (s : Ensemble A),
    IsAntichain R s -> cardinal A s 1 -> IsChain R s.
  Proof.
    intros s Ha Hcard.
    destruct Ha as [Hinhab Hanti].
    split; [exact Hinhab |].
    intros x y Hx Hy.
    inversion Hcard as [| A0 n H_A0 x0 H_notin]. subst s.
    inversion H_A0. subst A0.
    unfold Add in Hx, Hy.
    inversion Hx as [x' Hx' | x' Hx']; inversion Hy as [y' Hy' | y' Hy']; subst.
    - inversion Hx'.
    - inversion Hx'.
    - inversion Hy'.
    - inversion Hx'. inversion Hy'. subst.
      left. apply poset_refl.
  Qed.

  Lemma width_one_implies_chain : forall (sub s : Ensemble A),
    IsLargestAntichain R sub s 1 ->
    IsChain R sub.
  Proof.
    intros sub s Hla.
    destruct Hla as [Ha Hincl_s Hcard Hmaximal].
    destruct Ha as [Hinhab Hanti].
    split.
    - destruct Hinhab as [a Ha].
      apply Inhabited_intro with a.
      apply Hincl_s. exact Ha.
    - intros x y Hx Hy.
      destruct (classic (R x y \/ R y x)) as [Hcomp | Hincomp]; [exact Hcomp | exfalso].
      pose (pair := Add A (Add A (Empty_set A) x) y).
      assert (Hneq : x <> y).
      { intro Heq. subst y. apply Hincomp. left. apply poset_refl. }
      assert (Hanti_pair : IsAntichain R pair).
      { split.
        - unfold pair, Add. apply Inhabited_intro with x.
          apply Union_introl. apply Union_intror. apply In_singleton.
        - intros z1 z2 Hz1 Hz2 Hcomp'.
          unfold pair, Add in Hz1, Hz2.
          inversion Hz1 as [z1' Hz1' | z1' Hz1']; inversion Hz2 as [z2' Hz2' | z2' Hz2']; subst.
          + unfold Add in Hz1', Hz2'.
            inversion Hz1' as [z1'' Hz1'' | z1'' Hz1''];
            inversion Hz2' as [z2'' Hz2'' | z2'' Hz2'']; subst.
            * inversion Hz1''.
            * inversion Hz1''.
            * inversion Hz2''.
            * inversion Hz1''. inversion Hz2''. subst. reflexivity.
          + unfold Add in Hz1'.
            inversion Hz1' as [z1'' Hz1'' | z1'' Hz1'']; subst.
            * inversion Hz1''.
            * inversion Hz1''. inversion Hz2'. subst.
              exfalso. apply Hincomp. exact Hcomp'.
          + unfold Add in Hz2'.
            inversion Hz2' as [z2'' Hz2'' | z2'' Hz2'']; subst.
            * inversion Hz2''.
            * inversion Hz2''. inversion Hz1'; subst.
              exfalso. apply Hincomp. destruct Hcomp'; [right | left]; auto.
          + inversion Hz1'. inversion Hz2'. subst. reflexivity. }
      assert (Hcard_pair : cardinal A pair 2).
      { unfold pair. replace 2 with (S (S 0)) by reflexivity.
        apply card_add.
        - apply card_add; [apply card_empty | intro Hempty; inversion Hempty].
        - unfold Add. intro Hcontra.
          inversion Hcontra as [z' Hz' | z' Hz']; subst.
          + unfold Add in Hz'. inversion Hz'; subst; inversion H.
          + inversion Hz'. contradiction. }
      assert (Hcontra : 2 <= 1).
      { apply (Hmaximal pair 2 Hanti_pair); [| exact Hcard_pair].
        intros z Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
        - inversion Hz' as [z'' Hz'' | z'' Hz'']; subst.
          + inversion Hz''.
          + inversion Hz''; subst. exact Hx.
        - inversion Hz'; subst. exact Hy. }
      lia.
  Qed.

  (* ========================================================================= *)
  (* Inductive Step for DilworthB                                              *)
  (* ========================================================================= *)

  Lemma sub_in_above_or_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Union A (Above R la) (Below R la)).
  Proof.
    intros sub la w Hla x Hx.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    destruct Hanti as [Hinhab Hanti_incompat].
    destruct (classic (In A (Union A (Above R la) (Below R la)) x)) as [Hin | Hnin].
    - exact Hin.
    - exfalso.
      assert (Hnot_above : ~ In A (Above R la) x).
      { intro Hin'. apply Hnin. apply Union_introl. exact Hin'. }
      assert (Hnot_below : ~ In A (Below R la) x).
      { intro Hin'. apply Hnin. apply Union_intror. exact Hin'. }
      assert (Hx_notin_la : ~ In A la x).
      { intro Hx_la. apply Hnot_above.
        unfold Above. exists x. split; [exact Hx_la | apply poset_refl]. }
      assert (Hla'_anti : IsAntichain R (Add A la x)).
      { split.
        - destruct Hinhab as [a Ha].
          apply Inhabited_intro with a. unfold Add. apply Union_introl. exact Ha.
        - intros z1 z2 Hz1 Hz2 Hcomp.
          unfold Add in Hz1, Hz2.
          inversion Hz1 as [z1' Hz1' | z1' Hz1']; inversion Hz2 as [z2' Hz2' | z2' Hz2']; subst.
          + apply Hanti_incompat; assumption.
          + inversion Hz2'. subst.
            destruct Hcomp as [Hc | Hc].
            * exfalso. apply Hnot_above. unfold Above. exists z1. split; [exact Hz1' | exact Hc].
            * exfalso. apply Hnot_below. unfold Below. exists z1. split; [exact Hz1' | exact Hc].
          + inversion Hz1'. subst.
            destruct Hcomp as [Hc | Hc].
            * exfalso. apply Hnot_below. unfold Below. exists z2. split; [exact Hz2' | exact Hc].
            * exfalso. apply Hnot_above. unfold Above. exists z2. split; [exact Hz2' | exact Hc].
          + inversion Hz1'. inversion Hz2'. subst. reflexivity. }
      assert (Hla'_incl : Included A (Add A la x) sub).
      { intros z Hz. unfold Add in Hz.
        inversion Hz as [z' Hz' | z' Hz']; subst.
        - apply Hincl. exact Hz'.
        - inversion Hz'. subst. exact Hx. }
      assert (Hla'_card : cardinal A (Add A la x) (S w)).
      { apply card_add; assumption. }
      assert (Hle : S w <= w).
      { apply (Hmax (Add A la x) (S w)); assumption. }
      lia.
  Qed.

  Lemma la_largest_in_above : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    IsLargestAntichain R (Intersection A (Above R la) sub) la w.
  Proof.
    intros sub la w Hla.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    constructor.
    - exact Hanti.
    - intros x Hx. apply Intersection_intro.
      + exact (la_in_Above la Hanti x Hx).
      + exact (Hincl x Hx).
    - exact Hcard.
    - intros s n Hs Hincl_s Hcard_s.
      apply (Hmax s n Hs).
      + intros x Hx. apply Hincl_s in Hx. inversion Hx; assumption.
      + exact Hcard_s.
  Qed.

  Lemma la_largest_in_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    IsLargestAntichain R (Intersection A (Below R la) sub) la w.
  Proof.
    intros sub la w Hla.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    constructor.
    - exact Hanti.
    - intros x Hx. apply Intersection_intro.
      + exact (la_in_Below la Hanti x Hx).
      + exact (Hincl x Hx).
    - exact Hcard.
    - intros s n Hs Hincl_s Hcard_s.
      apply (Hmax s n Hs).
      + intros x Hx. apply Hincl_s in Hx. inversion Hx; assumption.
      + exact Hcard_s.
  Qed.

  Lemma la_card_le_sub : forall (sub la : Ensemble A) n w,
    cardinal A sub n ->
    IsLargestAntichain R sub la w ->
    w <= n.
  Proof.
    intros sub la n w Hcard Hla.
    destruct Hla as [_ Hincl Hcard_la _].
    revert sub n Hcard Hincl.
    induction Hcard_la as [| la0 w0 Hcard_la0 IH a Ha_notin]; intros sub n Hcard Hincl.
    - lia.
    - assert (Ha_in_sub : In A sub a).
      { apply Hincl. unfold Add. apply Union_intror. apply In_singleton. }
      destruct n as [| n0].
      + inversion Hcard. subst. inversion Ha_in_sub.
      + assert (Hcard_minus : cardinal A (fun y => In A sub y /\ y <> a) n0).
        { apply cardinal_remove; assumption. }
        assert (Hincl0 : Included A la0 (fun y => In A sub y /\ y <> a)).
        { intros x Hx. split.
          - apply Hincl. unfold Add. apply Union_introl. exact Hx.
          - intro Heq. subst. exact (Ha_notin Hx). }
        assert (w0 <= n0) by exact (IH _ _ Hcard_minus Hincl0).
        lia.
  Qed.

  Lemma above_card_lt : forall (sub la : Ensemble A) n w,
    cardinal A sub n ->
    w < n ->
    IsLargestAntichain R sub la w ->
    ~ Included A sub (Above R la) ->
    { na : nat | cardinal A (Intersection A (Above R la) sub) na /\ na < n }.
  Proof.
    intros sub la n w Hcard Hwn_lt Hla Hnotincl.
    destruct n as [| n']. { exfalso; lia. }
    assert (Hex : exists x : A, In A sub x /\ ~ In A (Above R la) x).
    { apply not_all_ex_not in Hnotincl.
      destruct Hnotincl as [x Hx]. apply imply_to_and in Hx.
      exact (ex_intro _ x Hx). }
    destruct (constructive_indefinite_description _ Hex) as [x [Hx_sub Hx_not_above]].
    assert (Hcard_minus : cardinal A (fun y => In A sub y /\ y <> x) n').
    { apply cardinal_remove; assumption. }
    assert (Hincl_inter : Included A (Intersection A (Above R la) sub)
                                     (fun y => In A sub y /\ y <> x)).
    { intros z Hz. inversion Hz. split; [assumption | intro Heq; subst; contradiction]. }
    assert (Hprop : exists na,
        cardinal A (Intersection A (Above R la) sub) na /\ na < S n').
    { assert (Hfin_sub : Finite A sub) by exact (cardinal_finite A sub (S n') Hcard).
      assert (Hfin_inter : Finite A (Intersection A (Above R la) sub)).
      { apply (Finite_downward_closed A sub Hfin_sub).
        intros z Hz. inversion Hz. assumption. }
      destruct (finite_cardinal A (Intersection A (Above R la) sub) Hfin_inter) as [na Hna].
      exists na. split. exact Hna.
      assert (Hle : na <= n')
        by exact (incl_card_le A _ _ na n' Hna Hcard_minus Hincl_inter). lia. }
    exact (constructive_indefinite_description _ Hprop).
  Qed.

  Lemma below_card_lt : forall (sub la : Ensemble A) n w,
    cardinal A sub n ->
    w < n ->
    IsLargestAntichain R sub la w ->
    ~ Included A sub (Below R la) ->
    { nb : nat | cardinal A (Intersection A (Below R la) sub) nb /\ nb < n }.
  Proof.
    intros sub la n w Hcard Hwn_lt Hla Hnotincl.
    destruct n as [| n']. { exfalso; lia. }
    assert (Hex : exists x : A, In A sub x /\ ~ In A (Below R la) x).
    { apply not_all_ex_not in Hnotincl.
      destruct Hnotincl as [x Hx]. apply imply_to_and in Hx.
      exact (ex_intro _ x Hx). }
    destruct (constructive_indefinite_description _ Hex) as [x [Hx_sub Hx_not_below]].
    assert (Hcard_minus : cardinal A (fun y => In A sub y /\ y <> x) n').
    { apply cardinal_remove; assumption. }
    assert (Hincl_inter : Included A (Intersection A (Below R la) sub)
                                     (fun y => In A sub y /\ y <> x)).
    { intros z Hz. inversion Hz. split; [assumption | intro Heq; subst; contradiction]. }
    assert (Hprop : exists nb,
        cardinal A (Intersection A (Below R la) sub) nb /\ nb < S n').
    { assert (Hfin_sub : Finite A sub) by exact (cardinal_finite A sub (S n') Hcard).
      assert (Hfin_inter : Finite A (Intersection A (Below R la) sub)).
      { apply (Finite_downward_closed A sub Hfin_sub).
        intros z Hz. inversion Hz. assumption. }
      destruct (finite_cardinal A (Intersection A (Below R la) sub) Hfin_inter) as [nb Hnb].
      exists nb. split. exact Hnb.
      assert (Hle : nb <= n')
        by exact (incl_card_le A _ _ nb n' Hnb Hcard_minus Hincl_inter). lia. }
    exact (constructive_indefinite_description _ Hprop).
  Qed.

  Lemma singleton_chain_cover : forall (s : Ensemble A) n,
    cardinal A s n ->
    { cover : Ensemble (Ensemble A) | IsChainCover R s cover /\ cardinal (Ensemble A) cover n }.
  Proof.
    intros s n Hcard.
    exists (fun C => exists x, In A s x /\ C = Singleton A x).
    split.
    - constructor.
      + intros C [x [Hx_in Heq_C]]. subst C. split.
        * apply Inhabited_intro with x. apply In_singleton.
        * intros a b Ha Hb. inversion Ha. inversion Hb. subst. left. apply poset_refl.
      + intros C [x [Hx_in Heq_C]]. subst C. intros y Hy. inversion Hy. subst y. exact Hx_in.
      + intros y Hy. exists (Singleton A y). split.
        * exists y. split; [exact Hy | reflexivity].
        * apply In_singleton.
    - induction Hcard as [| s0 m0 Hcard0 IH x Hx_notin].
      + assert (Hempty : (fun C => exists z, In A (Empty_set A) z /\ C = Singleton A z) =
                          Empty_set (Ensemble A)).
        { apply Extensionality_Ensembles. intro C. split.
          - intros [z [Hz _]]. inversion Hz.
          - intro HC. inversion HC. }
        rewrite Hempty. apply card_empty.
      + assert (Hset_eq :
          (fun C => exists z, In A (Add A s0 x) z /\ C = Singleton A z) =
          Add (Ensemble A) (fun C => exists z, In A s0 z /\ C = Singleton A z) (Singleton A x)).
        { apply Extensionality_Ensembles. intro C. split.
          - intros [z [Hz Hc]]. subst C.
            unfold Add in Hz.
            inversion Hz as [z' Hz' | z' Hz']; subst.
            + unfold Add. apply Union_introl. exists z. split; [exact Hz' | reflexivity].
            + inversion Hz'. subst z. unfold Add. apply Union_intror. apply In_singleton.
          - intro HC. unfold Add in HC.
            inversion HC as [z Hz | z Hz]; subst z.
            + destruct Hz as [a [Ha Heq_C]]. subst C.
              exists a. split; [unfold Add; apply Union_introl; exact Ha | reflexivity].
            + inversion Hz. subst C.
              exists x. split; [unfold Add; apply Union_intror; apply In_singleton | reflexivity]. }
        rewrite Hset_eq.
        apply card_add.
        * exact IH.
        * intros [z [Hz Heq_z]].
          assert (Hx_in_sz : In A (Singleton A z) x).
          { rewrite <- Heq_z. apply In_singleton. }
          inversion Hx_in_sz; subst. exact (Hx_notin Hz).
  Qed.

  Lemma antichain_singleton_cover : forall (sub la : Ensemble A) n,
    cardinal A sub n ->
    IsLargestAntichain R sub la n ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover n }.
  Proof.
    intros sub la n Hcard _. exact (singleton_chain_cover sub n Hcard).
  Qed.

  (* ========================================================================= *)
  (* Antichain Lower Bound for Chain Covers                                    *)
  (* ========================================================================= *)

  Lemma antichain_lb_for_chain_cover : forall (sub la : Ensemble A) w n
      (cover : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    IsChainCover R sub cover ->
    cardinal (Ensemble A) cover n ->
    w <= n.
  Proof.
    intros sub la w n cover Hla Hcover Hcard_cov.
    destruct Hla as [Hanti Hincl_la Hcard_la _].
    destruct Hanti as [_ Hincompat].
    destruct Hcover as [Hchains _ Hcovers].
    apply (InjectionPrinciple.cardinal_injection_principle_poly
             A (Ensemble A) la cover (fun a c => In A c a) w n);
    [| | exact Hcard_la | exact Hcard_cov].
    - intros a Ha_la.
      destruct (Hcovers a (Hincl_la a Ha_la)) as [c [Hc_cov Hca]].
      exact (ex_intro _ c (conj Hc_cov Hca)).
    - intros a b c Ha_la Hb_la Hc_cov Hca Hcb.
      destruct (Hchains c Hc_cov) as [_ Hcomp].
      exact (Hincompat a b Ha_la Hb_la (Hcomp a b Hca Hcb)).
  Qed.

  (* ========================================================================= *)
  (* Fiber Cover Cardinality                                                   *)
  (* ========================================================================= *)

  Lemma below_fiber_cover_cardinal : forall (sub la : Ensemble A) w (f : A -> A),
    cardinal A la w ->
    Included A la sub ->
    (forall a, In A la a -> f a = a) ->
    cardinal (Ensemble A)
      (fun C => exists a, In A la a /\ C = (fun x => In A sub x /\ f x = a))
      w.
  Proof.
    intros sub la w f Hcard.
    induction Hcard as [| la' w' Hcard' IH a0 Ha0_notin];
    intros Hincl Hfxa.
    - apply (cardinal_extensional_poly (Ensemble A) (Empty_set (Ensemble A)) _ 0).
      + intro C. split.
        * intro Hbot. inversion Hbot.
        * intros [a [Ha _]]. inversion Ha.
      + apply card_empty.
    - assert (Hincl' : Included A la' sub).
      { intros x Hx. apply Hincl. unfold Add. apply Union_introl. exact Hx. }
      assert (Hfxa' : forall a, In A la' a -> f a = a).
      { intros a Ha. apply Hfxa. unfold Add. apply Union_introl. exact Ha. }
      assert (Ha0_sub : In A sub a0).
      { apply Hincl. unfold Add. apply Union_intror. apply In_singleton. }
      assert (Ha0_f : f a0 = a0).
      { apply Hfxa. unfold Add. apply Union_intror. apply In_singleton. }
      assert (Heq_cov :
        (fun C => exists a, In A (Add A la' a0) a /\
                  C = (fun x => In A sub x /\ f x = a)) =
        Add (Ensemble A)
          (fun C => exists a, In A la' a /\ C = (fun x => In A sub x /\ f x = a))
          (fun x => In A sub x /\ f x = a0)).
      { apply Extensionality_Ensembles. intro C. split.
        - intros [a [Ha Heq_C]].
          unfold Add in Ha.
          inversion Ha as [z Hz | z Hz]; subst z.
          + apply Union_introl. exact (ex_intro _ a (conj Hz Heq_C)).
          + inversion Hz. subst a. subst C. apply Union_intror. apply In_singleton.
        - intro HC. unfold Add in HC.
          inversion HC as [z Hz | z Hz]; subst z.
          + destruct Hz as [a [Ha Heq_C]].
            exact (ex_intro _ a (conj (Union_introl _ _ _ _ Ha) Heq_C)).
          + inversion Hz. subst C.
            exact (ex_intro _ a0
              (conj (Union_intror _ _ _ _ (In_singleton _ _)) eq_refl)). }
      apply (cardinal_extensional_poly (Ensemble A)
        (Add (Ensemble A)
           (fun C => exists a, In A la' a /\ C = (fun x => In A sub x /\ f x = a))
           (fun x => In A sub x /\ f x = a0))
        _ (S w')).
      + intro C. rewrite <- Heq_cov. tauto.
      + apply card_add.
        * exact (IH Hincl' Hfxa').
        * intros [b [Hb_la' Heq_fiber]].
          assert (HRHS : In A sub a0 /\ f a0 = b) by
            exact (eq_rect _ (fun h : A -> Prop => h a0)
                     (conj Ha0_sub Ha0_f) _ Heq_fiber).
          assert (Ha0_b : a0 = b) by
            exact (eq_trans (eq_sym Ha0_f) (proj2 HRHS)).
          subst b. exact (Ha0_notin Hb_la').
  Qed.

  (* ========================================================================= *)
  (* Assignment Lemmas (Hall's Marriage Theorem)                               *)
  (* ========================================================================= *)

  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
  Admitted.

  Lemma chain_cover_above_existence : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    { p : Ensemble (Ensemble A) * nat |
        IsChainCover R sub (fst p) /\
        cardinal (Ensemble A) (fst p) (snd p) /\
        (snd p) <= w }.
  Proof.
    intros sub la w Hla Habove.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la _].
    destruct Hanti as [_ Hincompat].
    destruct (constructive_indefinite_description _
               (above_chain_assignment_exists sub la w Hla' Habove))
      as [f [Hf_assign Hf_chain]].
    assert (Hfxa : forall a, In A la a -> f a = a).
    { intros a Ha_la.
      destruct (Hf_assign a (Hincl_la a Ha_la)) as [Hfa_la Hfa_R].
      exact (Hincompat (f a) a Hfa_la Ha_la (or_introl Hfa_R)). }
    pose (cover := fun C => exists a, In A la a /\ C = (fun x => In A sub x /\ f x = a)).
    assert (Hcov : IsChainCover R sub cover).
    { constructor.
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C. exact (Hf_chain a Ha_la).
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C. intros x [Hx_sub _]. exact Hx_sub.
      - intros x Hx_sub.
        destruct (Hf_assign x Hx_sub) as [Hfx_la _].
        exact (ex_intro _ (fun y => In A sub y /\ f y = f x)
                 (conj (ex_intro _ (f x) (conj Hfx_la eq_refl))
                       (conj Hx_sub eq_refl))). }
    assert (Hcard_cov : cardinal (Ensemble A) cover w).
    { exact (below_fiber_cover_cardinal sub la w f Hcard_la Hincl_la Hfxa). }
    exact (exist _ (cover, w) (conj Hcov (conj Hcard_cov (Nat.le_refl w)))).
  Qed.

  Lemma chain_cover_of_above : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w Hla Habove.
    destruct (chain_cover_above_existence sub la w Hla Habove) as [[cover n] [Hcover [Hcard Hle]]].
    simpl in *.
    assert (Hge : w <= n) by
      exact (antichain_lb_for_chain_cover sub la w n cover Hla Hcover Hcard).
    assert (Heq : n = w) by lia. subst n.
    exact (exist _ cover (conj Hcover Hcard)).
  Qed.

  Lemma below_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R x (f x)) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
  Admitted.

  Lemma chain_cover_of_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w Hla Hbelow.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    destruct (constructive_indefinite_description _
               (below_chain_assignment_exists sub la w Hla' Hbelow))
      as [f [Hf_assign Hf_chain]].
    assert (Hfxa : forall a, In A la a -> f a = a).
    { intros a Ha_la.
      destruct (Hf_assign a (Hincl_la a Ha_la)) as [Hfa_la Hfa_R].
      exact (eq_sym (Hincompat a (f a) Ha_la Hfa_la (or_introl Hfa_R))). }
    pose (cover := fun C => exists a, In A la a /\ C = (fun x => In A sub x /\ f x = a)).
    assert (Hcov : IsChainCover R sub cover).
    { constructor.
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C. exact (Hf_chain a Ha_la).
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C. intros x [Hx_sub _]. exact Hx_sub.
      - intros x Hx_sub.
        destruct (Hf_assign x Hx_sub) as [Hfx_la _].
        exact (ex_intro _ (fun y => In A sub y /\ f y = f x)
                 (conj (ex_intro _ (f x) (conj Hfx_la eq_refl))
                       (conj Hx_sub eq_refl))). }
    assert (Hcard_cov : cardinal (Ensemble A) cover w).
    { exact (below_fiber_cover_cardinal sub la w f Hcard_la Hincl_la Hfxa). }
    exact (exist _ cover (conj Hcov Hcard_cov)).
  Qed.

  Lemma extend_cover_above : forall (sub la : Ensemble A) w
      (cover_b : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    IsChainCover R (Intersection A (Below R la) sub) cover_b ->
    cardinal (Ensemble A) cover_b w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w _cover_b Hla Habove _ _.
    exact (chain_cover_of_above sub la w Hla Habove).
  Qed.

  Lemma extend_cover_below : forall (sub la : Ensemble A) w
      (cover_a : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    IsChainCover R (Intersection A (Above R la) sub) cover_a ->
    cardinal (Ensemble A) cover_a w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w _cover_a Hla Hbelow _ _.
    exact (chain_cover_of_below sub la w Hla Hbelow).
  Qed.

  (* ========================================================================= *)
  (* The Merge Lemma                                                           *)
  (* ========================================================================= *)

  Lemma merge_above_below_covers : forall (sub la : Ensemble A) w
      (cover_a cover_b : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    Included A sub (Union A (Above R la) (Below R la)) ->
    IsChainCover R (Intersection A (Above R la) sub) cover_a ->
    cardinal (Ensemble A) cover_a w ->
    IsChainCover R (Intersection A (Below R la) sub) cover_b ->
    cardinal (Ensemble A) cover_b w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w cover_a cover_b Hla Hunion Hcov_a Hcard_a Hcov_b Hcard_b.
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [Hinhab Hincompat].
    assert (Hla_above : forall a, In A la a -> In A (Intersection A (Above R la) sub) a).
    { intros a Ha. apply Intersection_intro.
      - exists a. split; [exact Ha | apply poset_refl].
      - exact (Hincl_la a Ha). }
    assert (Hla_below : forall a, In A la a -> In A (Intersection A (Below R la) sub) a).
    { intros a Ha. apply Intersection_intro.
      - exists a. split; [exact Ha | apply poset_refl].
      - exact (Hincl_la a Ha). }
    assert (HCa_above : forall Ca, In (Ensemble A) cover_a Ca ->
              Included A Ca (Above R la)).
    { intros Ca HCa z Hz.
      destruct (chain_cover_included R (IsChainCover := Hcov_a) Ca HCa z Hz). assumption. }
    assert (HCb_below : forall Cb, In (Ensemble A) cover_b Cb ->
              Included A Cb (Below R la)).
    { intros Cb HCb z Hz.
      destruct (chain_cover_included R (IsChainCover := Hcov_b) Cb HCb z Hz). assumption. }
    (* Use choice to get functions ca : A -> Ensemble A and cb : A -> Ensemble A *)
    assert (Hca_exists : forall a, In A la a ->
              exists Ca, In (Ensemble A) cover_a Ca /\ In A Ca a).
    { intros a Ha.
      exact (chain_cover_covers R (IsChainCover := Hcov_a) a (Hla_above a Ha)). }
    assert (Hcb_exists : forall a, In A la a ->
              exists Cb, In (Ensemble A) cover_b Cb /\ In A Cb a).
    { intros a Ha.
      exact (chain_cover_covers R (IsChainCover := Hcov_b) a (Hla_below a Ha)). }
    (* Extract functions using epsilon *)
    pose (ca := fun a => epsilon (inhabits (Empty_set A))
                  (fun Ca => In (Ensemble A) cover_a Ca /\ In A Ca a)).
    pose (cb := fun a => epsilon (inhabits (Empty_set A))
                  (fun Cb => In (Ensemble A) cover_b Cb /\ In A Cb a)).
    assert (Hca_spec : forall a, In A la a ->
              In (Ensemble A) cover_a (ca a) /\ In A (ca a) a).
    { intros a Ha. unfold ca. apply epsilon_spec. exact (Hca_exists a Ha). }
    assert (Hcb_spec : forall a, In A la a ->
              In (Ensemble A) cover_b (cb a) /\ In A (cb a) a).
    { intros a Ha. unfold cb. apply epsilon_spec. exact (Hcb_exists a Ha). }
    (* ca is injective on la *)
    assert (Hca_inj : forall a1 a2, In A la a1 -> In A la a2 ->
              ca a1 = ca a2 -> a1 = a2).
    { intros a1 a2 Ha1 Ha2 Heq.
      destruct (Hca_spec a1 Ha1) as [HCa1 Ha1_Ca].
      destruct (Hca_spec a2 Ha2) as [HCa2 Ha2_Ca].
      rewrite Heq in Ha1_Ca.
      assert (Hchain : IsChain R (ca a2))
        by exact (chain_cover_chains R (IsChainCover := Hcov_a) (ca a2) HCa2).
      destruct Hchain as [_ Hcomp].
      exact (Hincompat a1 a2 Ha1 Ha2 (Hcomp a1 a2 Ha1_Ca Ha2_Ca)). }
    (* ca is surjective onto cover_a *)
    assert (Hca_surj : forall Ca, In (Ensemble A) cover_a Ca ->
              exists a, In A la a /\ ca a = Ca).
    { intros Ca HCa.
      destruct (classic (exists a, In A la a /\ ca a = Ca)) as [Hex | Hnex].
      - exact Hex.
      - exfalso.
        (* Ca is not in the range of ca|_la. So ca maps la into cover_a \ {Ca}. *)
        assert (Hno_hit : forall a, In A la a -> ca a <> Ca).
        { intros a Ha Heq. apply Hnex. exact (ex_intro _ a (conj Ha Heq)). }
        (* cover_a \ {Ca} has cardinality w - 1 *)
        destruct w as [| w'].
        { (* w = 0: la empty, but la is inhabited *)
          destruct Hinhab as [a Ha]. inversion Hcard_la. subst. inversion Ha. }
        assert (Hcard_minus : cardinal (Ensemble A)
                  (fun D => In (Ensemble A) cover_a D /\ D <> Ca) w').
        { apply cardinal_remove; assumption. }
        (* The injection la → cover_a \ {Ca} gives S w' ≤ w', contradiction *)
        assert (Habs : S w' <= w').
        { apply (InjectionPrinciple.cardinal_injection_principle_poly
                   A (Ensemble A) la
                   (fun D => In (Ensemble A) cover_a D /\ D <> Ca)
                   (fun a D => ca a = D) (S w') w').
          - intros a Ha.
            destruct (Hca_spec a Ha) as [HCa_a _].
            exists (ca a). split.
            + split; [exact HCa_a | exact (Hno_hit a Ha)].
            + reflexivity.
          - intros a1 a2 D Ha1 Ha2 _ Heq1 Heq2.
            apply (Hca_inj a1 a2 Ha1 Ha2). rewrite Heq1. symmetry. exact Heq2.
          - exact Hcard_la.
          - exact Hcard_minus. }
        lia. }
    (* cb is surjective onto cover_b (same argument) *)
    assert (Hcb_surj : forall Cb, In (Ensemble A) cover_b Cb ->
              exists a, In A la a /\ cb a = Cb).
    { intros Cb HCb.
      destruct (classic (exists a, In A la a /\ cb a = Cb)) as [Hex | Hnex].
      - exact Hex.
      - exfalso.
        assert (Hno_hit : forall a, In A la a -> cb a <> Cb).
        { intros a Ha Heq. apply Hnex. exact (ex_intro _ a (conj Ha Heq)). }
        destruct w as [| w'].
        { destruct Hinhab as [a Ha]. inversion Hcard_la. subst. inversion Ha. }
        assert (Hcard_minus : cardinal (Ensemble A)
                  (fun D => In (Ensemble A) cover_b D /\ D <> Cb) w').
        { apply cardinal_remove; assumption. }
        assert (Habs : S w' <= w').
        { apply (InjectionPrinciple.cardinal_injection_principle_poly
                   A (Ensemble A) la
                   (fun D => In (Ensemble A) cover_b D /\ D <> Cb)
                   (fun a D => cb a = D) (S w') w').
          - intros a Ha.
            destruct (Hcb_spec a Ha) as [HCb_a _].
            exists (cb a). split.
            + split; [exact HCb_a | exact (Hno_hit a Ha)].
            + reflexivity.
          - intros a1 a2 D Ha1 Ha2 _ Heq1 Heq2.
            destruct (Hcb_spec a1 Ha1) as [HCb1 Ha1_Cb].
            destruct (Hcb_spec a2 Ha2) as [HCb2 Ha2_Cb].
            assert (Hcb_eq : cb a1 = cb a2) by (rewrite Heq1; symmetry; exact Heq2).
            rewrite Hcb_eq in Ha1_Cb.
            assert (Hchain : IsChain R (cb a2))
              by exact (chain_cover_chains R (IsChainCover := Hcov_b) (cb a2) HCb2).
            destruct Hchain as [_ Hcomp].
            exact (Hincompat a1 a2 Ha1 Ha2 (Hcomp a1 a2 Ha1_Cb Ha2_Cb)).
          - exact Hcard_la.
          - exact Hcard_minus. }
        lia. }
    (* Define merged as the image of la under the merge function *)
    pose (merged := fun E : Ensemble A =>
      exists a, In A la a /\ E = Union A (ca a) (cb a)).
    exists merged.
    (* Part 1: merged is a chain cover of sub *)
    assert (Hmerged_cov : IsChainCover R sub merged).
    { constructor.
      - (* Each merged chain is a chain *)
        intros E HE. destruct HE as [a [Ha_la Heq_E]]. subst E.
        destruct (Hca_spec a Ha_la) as [HCa Ha_Ca].
        destruct (Hcb_spec a Ha_la) as [HCb Ha_Cb].
        assert (chain_Ca : IsChain R (ca a))
          by exact (chain_cover_chains R (IsChainCover := Hcov_a) (ca a) HCa).
        assert (chain_Cb : IsChain R (cb a))
          by exact (chain_cover_chains R (IsChainCover := Hcov_b) (cb a) HCb).
        constructor.
        + apply Inhabited_intro with a. apply Union_introl. exact Ha_Ca.
        + intros x y Hx Hy.
          inversion Hx as [x' Hx' | x' Hx']; subst x';
          inversion Hy as [y' Hy' | y' Hy']; subst y'.
          * exact (chain_comparable R (IsChain := chain_Ca) x y Hx' Hy').
          * right. apply (poset_trans y a x).
            -- exact (chain_la_is_max R la (cb a) a y
                 (Build_IsAntichain R la Hinhab Hincompat) chain_Cb
                 (HCb_below (cb a) HCb) Ha_Cb Ha_la Hy').
            -- exact (chain_la_is_min R la (ca a) a x
                 (Build_IsAntichain R la Hinhab Hincompat) chain_Ca
                 (HCa_above (ca a) HCa) Ha_Ca Ha_la Hx').
          * left. apply (poset_trans x a y).
            -- exact (chain_la_is_max R la (cb a) a x
                 (Build_IsAntichain R la Hinhab Hincompat) chain_Cb
                 (HCb_below (cb a) HCb) Ha_Cb Ha_la Hx').
            -- exact (chain_la_is_min R la (ca a) a y
                 (Build_IsAntichain R la Hinhab Hincompat) chain_Ca
                 (HCa_above (ca a) HCa) Ha_Ca Ha_la Hy').
          * exact (chain_comparable R (IsChain := chain_Cb) x y Hx' Hy').
      - (* Each merged chain is included in sub *)
        intros E HE. destruct HE as [a [Ha_la Heq_E]]. subst E.
        destruct (Hca_spec a Ha_la) as [HCa _].
        destruct (Hcb_spec a Ha_la) as [HCb _].
        intros x Hx.
        inversion Hx as [x' Hx' | x' Hx']; subst x'.
        + destruct (chain_cover_included R (IsChainCover := Hcov_a) (ca a) HCa x Hx').
          assumption.
        + destruct (chain_cover_included R (IsChainCover := Hcov_b) (cb a) HCb x Hx').
          assumption.
      - (* merged covers sub *)
        intros x Hx.
        pose proof (Hunion x Hx) as Hx_union.
        destruct Hx_union as [x0 Hx_ab | x0 Hx_ab].
        + (* x ∈ Above(la) *)
          assert (Hx_inter : In A (Intersection A (Above R la) sub) x0)
            by exact (Intersection_intro _ _ _ x0 Hx_ab Hx).
          destruct (chain_cover_covers R (IsChainCover := Hcov_a) x0 Hx_inter)
            as [Ca' [HCa' Hx_Ca']].
          (* By surjectivity, Ca' = ca(a') for some a' ∈ la *)
          destruct (Hca_surj Ca' HCa') as [a' [Ha'_la Hca_eq]].
          exists (Union A (ca a') (cb a')). split.
          { exists a'. exact (conj Ha'_la eq_refl). }
          { apply Union_introl. rewrite Hca_eq. exact Hx_Ca'. }
        + (* x ∈ Below(la) *)
          assert (Hx_inter : In A (Intersection A (Below R la) sub) x0)
            by exact (Intersection_intro _ _ _ x0 Hx_ab Hx).
          destruct (chain_cover_covers R (IsChainCover := Hcov_b) x0 Hx_inter)
            as [Cb' [HCb' Hx_Cb']].
          (* By surjectivity, Cb' = cb(a') for some a' ∈ la *)
          destruct (Hcb_surj Cb' HCb') as [a' [Ha'_la Hcb_eq]].
          exists (Union A (ca a') (cb a')). split.
          { exists a'. exact (conj Ha'_la eq_refl). }
          { apply Union_intror. rewrite Hcb_eq. exact Hx_Cb'. } }
    split; [exact Hmerged_cov |].
    (* Part 2: |merged| = w *)
    assert (Hla_full : IsLargestAntichain R sub la w).
    { constructor; [constructor; [exact Hinhab | exact Hincompat]
      | exact Hincl_la | exact Hcard_la | exact Hmax]. }
    (* merged is the image of la under (fun a => Union (ca a) (cb a)) *)
    (* So |merged| ≤ |la| = w by image_cardinal_le *)
    pose (f := fun a => Union A (ca a) (cb a)).
    assert (Hmerged_eq : forall E, In (Ensemble A) merged E <->
              exists a, In A la a /\ E = f a).
    { intros E. split; intros [a [Ha Heq]]; exists a; exact (conj Ha Heq). }
    assert (Hmerged_ext : merged = (fun E => exists a, In A la a /\ E = f a)).
    { apply Extensionality_Ensembles. intro E. split.
      - intro HE. exact (proj1 (Hmerged_eq E) HE).
      - intro HE. exact (proj2 (Hmerged_eq E) HE). }
    destruct (image_cardinal_le la f w Hcard_la) as [m [Hcard_img Hm_le]].
    (* The image set equals merged *)
    assert (Himg_eq : (fun y : Ensemble A => exists x, In A la x /\ y = f x) = merged).
    { apply Extensionality_Ensembles. intro E. split.
      - intros [a [Ha Heq]]. exists a. exact (conj Ha Heq).
      - intros [a [Ha Heq]]. exists a. exact (conj Ha Heq). }
    rewrite Himg_eq in Hcard_img.
    assert (Hge : w <= m).
    { exact (antichain_lb_for_chain_cover sub la w m merged
               Hla_full Hmerged_cov Hcard_img). }
    assert (Heq : m = w) by lia.
    subst m. exact Hcard_img.
  Qed.

  (* ========================================================================= *)
  (* The Inductive Step                                                        *)
  (* ========================================================================= *)

  Lemma dilworth_inductive_step : forall n (sub la : Ensemble A) (w : nat),
    cardinal A sub n ->
    w >= 2 ->
    IsLargestAntichain R sub la w ->
    (forall n' (sub' la' : Ensemble A) (w' : nat),
      n' < n ->
      cardinal A sub' n' ->
      IsLargestAntichain R sub' la' w' ->
      { cover : Ensemble (Ensemble A) | IsChainCover R sub' cover /\ cardinal (Ensemble A) cover w' }) ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros n sub la w Hcard Hwge2 Hla IH.
    assert (Hwn : w <= n) by exact (la_card_le_sub sub la n w Hcard Hla).
    destruct (Nat.eq_dec w n) as [Hwn_eq | Hwn_ne].
    { subst n. exact (antichain_singleton_cover sub la w Hcard Hla). }
    assert (Hwn_lt : w < n) by lia.
    destruct (excluded_middle_informative (Included A sub (Above R la))) as [Habove | Hnotabove].
    { destruct (excluded_middle_informative (Included A sub (Below R la))) as [Hbelow | Hnotbelow].
      { exfalso.
        destruct Hla as [Hanti Hincl_la Hcard_la _].
        destruct Hanti as [_ Hanti_incompat].
        assert (Hsub_la : Included A sub la).
        { intros x Hx.
          destruct (Habove x Hx) as [a [Ha_la Hra_x]].
          destruct (Hbelow x Hx) as [b [Hb_la Hrx_b]].
          assert (Hrab : R a b) by exact (poset_trans a x b Hra_x Hrx_b).
          assert (Hab : a = b) by exact (Hanti_incompat a b Ha_la Hb_la (or_introl Hrab)).
          subst b. rewrite (poset_antisym x a Hrx_b Hra_x). exact Ha_la. }
        assert (Hle : n <= w) by exact (incl_card_le A sub la n w Hcard Hcard_la Hsub_la).
        lia. }
      { destruct (below_card_lt sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (extend_cover_above sub la w cover_b Hla Habove Hcover_b Hcard_b). } }
    { destruct (excluded_middle_informative (Included A sub (Below R la))) as [Hbelow | Hnotbelow].
      { destruct (above_card_lt sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        exact (extend_cover_below sub la w cover_a Hla Hbelow Hcover_a Hcard_a). }
      { destruct (above_card_lt sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (below_card_lt sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (merge_above_below_covers sub la w cover_a cover_b Hla
                 (sub_in_above_or_below sub la w Hla)
                 Hcover_a Hcard_a Hcover_b Hcard_b). } }
  Qed.

  (* ========================================================================= *)
  (* Backward Direction: DilworthB                                             *)
  (* ========================================================================= *)

  Lemma DilworthB : forall n sub w la,
    cardinal A sub n ->
    IsLargestAntichain R sub la w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    refine (Fix lt_wf (fun n => forall sub w la,
      cardinal A sub n ->
      IsLargestAntichain R sub la w ->
      { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w })
      (fun n IH sub w la Hcard_n Hla => _)).
    destruct w as [| w'].
    - exfalso.
      apply (empty_antichain_contradiction la).
      + destruct Hla; assumption.
      + destruct Hla; assumption.
    - destruct w' as [| w''].
      + exists (Singleton (Ensemble A) sub).
        destruct Hla as [Hanti Hincl_la Hcard_w Hmax].
        split.
        * constructor.
          -- intros c Hc. inversion Hc. subst c.
             apply (width_one_implies_chain sub la).
             constructor; [exact Hanti | exact Hincl_la | exact Hcard_w | exact Hmax].
          -- intros c Hc. inversion Hc. subst c. intros x Hx. exact Hx.
          -- intros x Hx. exists sub. split.
             ++ apply In_singleton.
             ++ exact Hx.
        * replace 1 with (S 0) by reflexivity.
          apply (cardinal_extensional_poly (Ensemble A)
            (Add (Ensemble A) (Empty_set (Ensemble A)) sub)
            (Singleton (Ensemble A) sub) 1).
          -- intro X. split; intro HX.
             ++ unfold Add in HX. inversion HX as [X' HX' | X' HX']; subst.
                ** inversion HX'.
                ** inversion HX'. apply In_singleton.
             ++ inversion HX. subst X. unfold Add. apply Union_intror. apply In_singleton.
          -- apply card_add;
             [apply card_empty; intros X HX; inversion HX | intro Hcontra; inversion Hcontra].
      + eapply dilworth_inductive_step.
        * exact Hcard_n.
        * lia.
        * exact Hla.
        * intros n' sub' la' w_prime Hn_prime Hcard_n' Hla'.
          apply (IH n' Hn_prime sub' w_prime la' Hcard_n' Hla').
  Qed.

End DilworthBackward.

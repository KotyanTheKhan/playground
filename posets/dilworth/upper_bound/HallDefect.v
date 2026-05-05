(* Hall-defect bounds for the largest antichain.
   These are the inequalities |S| <= |StrictSucc S| + w (and the predecessor
   variant) that Hall's marriage theorem requires when matching sub against
   sub union la in the assignment kernel. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section HallDefect.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* la-elements are exactly the minimal elements of sub, when sub is included in Above(la). *)
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

  (* Strict successors of S inside sub: y in sub with some x in S, R x y, x <> y. *)
  Definition StrictSucc (sub S : Ensemble A) : Ensemble A :=
    fun y => In A sub y /\ exists x, In A S x /\ R x y /\ x <> y.

  (* Strict predecessors, dual to StrictSucc. *)
  Definition StrictPred (sub S : Ensemble A) : Ensemble A :=
    fun y => In A sub y /\ exists x, In A S x /\ R y x /\ x <> y.

  (* For any S included in sub, |S| <= |StrictSucc S| + w. The "missing" part of S
     beyond StrictSucc is itself an antichain, so bounded by w. *)
  Lemma dilworth_hall_defect : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    forall S ns nn,
      Included A S sub ->
      cardinal A S ns ->
      cardinal A (StrictSucc sub S) nn ->
      ns <= nn + w.
  Proof.
    intros sub la w Hla S ns nn HinclS HcardS HcardNS.
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

  (* Predecessor variant; symmetric proof. *)
  Lemma dilworth_hall_defect_pred : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    forall S ns nn,
      Included A S sub ->
      cardinal A S ns ->
      cardinal A (StrictPred sub S) nn ->
      ns <= nn + w.
  Proof.
    intros sub la w Hla Habove S ns nn HinclS HcardS HcardNS.
    destruct Hla as [_ Hincl_la Hcard_la Hmax].
    pose (M := fun x => In A S x /\ ~ In A (StrictPred sub S) x).
    assert (HfinS : Finite A S) by exact (cardinal_finite A S ns HcardS).
    assert (HfinM : Finite A M).
    { apply (Finite_downward_closed A S HfinS). intros x [HxS _]. exact HxS. }
    destruct (finite_cardinal A M HfinM) as [m HcardM].
    assert (Hincl_S : Included A S (Union A M (StrictPred sub S))).
    { intros x HxS.
      destruct (classic (In A (StrictPred sub S) x)) as [Hxin | Hxout].
      - apply Union_intror. exact Hxin.
      - apply Union_introl. exact (conj HxS Hxout). }
    assert (HdisM : forall x, In A M x -> ~ In A (StrictPred sub S) x).
    { intros x [_ Hxout]. exact Hxout. }
    assert (HcardMN : cardinal A (Union A M (StrictPred sub S)) (m + nn)).
    { exact (cardinal_disjoint_union_gen A M (StrictPred sub S) m nn HdisM HcardM HcardNS). }
    assert (Hns_le : ns <= m + nn).
    { exact (incl_card_le A S (Union A M (StrictPred sub S)) ns (m + nn)
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
            exfalso. apply HxnN.
            exact (conj (HinclS x HxS) (ex_intro _ y (conj HyS (conj Hxy (fun h => Hneq (eq_sym h)))))).
          - destruct (classic (x = y)) as [Heq | Hneq]; [exact Heq |].
            exfalso. apply HynN.
            exact (conj (HinclS y HyS)
                        (ex_intro _ x (conj HxS (conj Hyx Hneq)))). }
        exact (Hmax M _ (Build_IsAntichain R M HinhM HincompM)
                        (fun x HxM => HinclS x (proj1 HxM))
                        HcardM). }
    lia.
  Qed.

End HallDefect.

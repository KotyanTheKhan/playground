From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section DilworthBackward.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* WidthUpperBound.v now uses the classes defined in Definitions.v *)


  (* ========================================================================= *)
  (* Helper Lemmas for Above and Below                                         *)
  (* ========================================================================= *)

  (** Above and Below include the antichain itself (by reflexivity) *)
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

  (** If la is the largest antichain, it's also the largest in Above/Below *)
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

  (** Above contains la *)
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

  (** Below contains la *)
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

  (* ========================================================================= *)
  (* Special Cases: Width 0 and Width 1                                        *)
  (* ========================================================================= *)

  Lemma empty_antichain_contradiction : forall (s : Ensemble A),
    IsAntichain R s -> cardinal A s 0 -> False.
  Proof.
    intros s Ha Hcard.
    destruct Ha as [Hinhab _].
    destruct Hinhab as [a Ha].
    inversion Hcard. subst.
    inversion Ha.
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

  (** Key lemma: If width = 1, then the subposet is a chain *)
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
      
      (* Construct the antichain {x, y} *)
      pose (pair := Add A (Add A (Empty_set A) x) y).
      
      assert (Hneq : x <> y).
      {
        intro Heq. subst y.
        apply Hincomp. left. apply poset_refl.
      }
      
      assert (Hanti_pair : IsAntichain R pair).
      {
        split.
        - unfold pair, Add. apply Inhabited_intro with x.
          apply Union_introl. apply Union_intror. apply In_singleton.
        - intros z1 z2 Hz1 Hz2 Hcomp.
          unfold pair, Add in Hz1, Hz2.
          inversion Hz1 as [z1' Hz1' | z1' Hz1']; inversion Hz2 as [z2' Hz2' | z2' Hz2']; subst.
          + unfold Add in Hz1', Hz2'.
            inversion Hz1' as [z1'' Hz1'' | z1'' Hz1'']; inversion Hz2' as [z2'' Hz2'' | z2'' Hz2'']; subst.
            * inversion Hz1''.
            * inversion Hz1''.
            * inversion Hz2''.
            * inversion Hz1''. inversion Hz2''. subst. reflexivity.
          + unfold Add in Hz1'.
            inversion Hz1' as [z1'' Hz1'' | z1'' Hz1'']; subst.
            * inversion Hz1''.
            * inversion Hz1''. inversion Hz2'. subst.
              exfalso. apply Hincomp. exact Hcomp.
          + unfold Add in Hz2'.
            inversion Hz2' as [z2'' Hz2'' | z2'' Hz2'']; subst.
            * inversion Hz2''.
            * inversion Hz2''. inversion Hz1'; subst.
              exfalso. apply Hincomp. destruct Hcomp; [right | left]; auto.
          + inversion Hz1'. inversion Hz2'. subst. reflexivity.
      }
      
      assert (Hcard_pair : cardinal A pair 2).
      {
        unfold pair. replace 2 with (S (S 0)) by reflexivity.
        apply card_add.
        - apply card_add; [apply card_empty | intro Hempty; inversion Hempty].
        - unfold Add. intro Hcontra.
          inversion Hcontra as [z' Hz' | z' Hz']; subst.
          + unfold Add in Hz'. inversion Hz'; subst; inversion H.
          + inversion Hz'. contradiction.
      }
      
      assert (Hcontra : 2 <= 1).
      { apply (Hmaximal pair 2 Hanti_pair); [| exact Hcard_pair].
        intros z Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
        - inversion Hz' as [z'' Hz'' | z'' Hz'']; subst.
          + inversion Hz''.
          + inversion Hz''; subst. exact Hx.
        - inversion Hz'; subst. exact Hy.
      }
      lia.
  Qed.

  Lemma singleton_ensemble_card : forall (s : Ensemble A),
    IsAntichain R s -> cardinal A s 1 ->
    cardinal (Ensemble A) (Singleton (Ensemble A) s) 1.
  Proof.
    intros s Hanti Hcard.
    replace 1 with (S 0) by reflexivity.
    
    assert (Hadd_card : cardinal (Ensemble A) (Add (Ensemble A) (Empty_set (Ensemble A)) s) 1).
    {
      apply card_add; [apply card_empty; intros X HX; inversion HX | intro Hcontra; inversion Hcontra].
    }
    
    apply (cardinal_extensional_poly (Ensemble A) (Add (Ensemble A) (Empty_set (Ensemble A)) s) (Singleton (Ensemble A) s) 1).
    
    - intro X. split; intro HX.
      + unfold Add in HX.
        inversion HX as [X' HX' | X' HX']; subst.
        * inversion HX'.
        * inversion HX'. apply In_singleton.
      + inversion HX. subst X.
        unfold Add. apply Union_intror. apply In_singleton.
    
    - exact Hadd_card.
  Qed.

  (* ========================================================================= *)
  (* Inductive Step for DilworthB                                              *)
  (* ========================================================================= *)

  (** Every element of sub is comparable to some element of la,
      hence lies in Above(la) or Below(la). *)
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
      (* x ∉ la: if x ∈ la then R x x witnesses x ∈ Above(la) *)
      assert (Hx_notin_la : ~ In A la x).
      {
        intro Hx_la.
        apply Hnot_above.
        unfold Above. exists x. split; [exact Hx_la | apply poset_refl].
      }
      (* Build Add A la x as an antichain of size w+1 in sub *)
      assert (Hla'_anti : IsAntichain R (Add A la x)).
      {
        split.
        - destruct Hinhab as [a Ha].
          apply Inhabited_intro with a.
          unfold Add. apply Union_introl. exact Ha.
        - intros z1 z2 Hz1 Hz2 Hcomp.
          unfold Add in Hz1, Hz2.
          inversion Hz1 as [z1' Hz1' | z1' Hz1']; inversion Hz2 as [z2' Hz2' | z2' Hz2']; subst.
          + (* Both in la *)
            apply Hanti_incompat; assumption.
          + (* z1 ∈ la, z2 = x *)
            inversion Hz2'. subst.
            destruct Hcomp as [Hc | Hc].
            * exfalso. apply Hnot_above.
              unfold Above. exists z1. split; [exact Hz1' | exact Hc].
            * exfalso. apply Hnot_below.
              unfold Below. exists z1. split; [exact Hz1' | exact Hc].
          + (* z1 = x, z2 ∈ la *)
            inversion Hz1'. subst.
            destruct Hcomp as [Hc | Hc].
            * exfalso. apply Hnot_below.
              unfold Below. exists z2. split; [exact Hz2' | exact Hc].
            * exfalso. apply Hnot_above.
              unfold Above. exists z2. split; [exact Hz2' | exact Hc].
          + (* Both = x *)
            inversion Hz1'. inversion Hz2'. subst. reflexivity.
      }
      assert (Hla'_incl : Included A (Add A la x) sub).
      {
        intros z Hz.
        unfold Add in Hz.
        inversion Hz as [z' Hz' | z' Hz']; subst.
        - apply Hincl. exact Hz'.
        - inversion Hz'. subst. exact Hx.
      }
      assert (Hla'_card : cardinal A (Add A la x) (S w)).
      { apply card_add; assumption. }
      assert (Hle : S w <= w).
      { apply (Hmax (Add A la x) (S w)); assumption. }
      lia.
  Qed.

  (** la is a largest antichain within (Above la) ∩ sub. *)
  Lemma la_largest_in_above : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    IsLargestAntichain R (Intersection A (Above R la) sub) la w.
  Proof.
    intros sub la w Hla.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    constructor.
    - exact Hanti.
    - intros x Hx.
      apply Intersection_intro.
      + exact (la_in_Above la Hanti x Hx).
      + exact (Hincl x Hx).
    - exact Hcard.
    - intros s n Hs Hincl_s Hcard_s.
      apply (Hmax s n Hs).
      + intros x Hx.
        apply Hincl_s in Hx.
        inversion Hx; assumption.
      + exact Hcard_s.
  Qed.

  (** la is a largest antichain within (Below la) ∩ sub. *)
  Lemma la_largest_in_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    IsLargestAntichain R (Intersection A (Below R la) sub) la w.
  Proof.
    intros sub la w Hla.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    constructor.
    - exact Hanti.
    - intros x Hx.
      apply Intersection_intro.
      + exact (la_in_Below la Hanti x Hx).
      + exact (Hincl x Hx).
    - exact Hcard.
    - intros s n Hs Hincl_s Hcard_s.
      apply (Hmax s n Hs).
      + intros x Hx.
        apply Hincl_s in Hx.
        inversion Hx; assumption.
      + exact Hcard_s.
  Qed.

  (** la is no larger than sub. *)
  Lemma la_card_le_sub : forall (sub la : Ensemble A) n w,
    cardinal A sub n ->
    IsLargestAntichain R sub la w ->
    w <= n.
  Proof.
    intros sub la n w Hcard Hla.
    destruct Hla as [_ Hincl Hcard_la _].
    (* Generalise over sub and n so induction on Hcard_la goes through *)
    revert sub n Hcard Hincl.
    induction Hcard_la as [| la0 w0 Hcard_la0 IH a Ha_notin]; intros sub n Hcard Hincl.
    - lia.
    - (* la = Add A la0 a, |la| = S w0 *)
      assert (Ha_in_sub : In A sub a).
      { apply Hincl. unfold Add. apply Union_intror. apply In_singleton. }
      destruct n as [| n0].
      + (* sub is empty but a ∈ sub — contradiction *)
        inversion Hcard. subst. inversion Ha_in_sub.
      + (* |sub| = S n0; remove a to get |sub \ {a}| = n0 *)
        assert (Hcard_minus : cardinal A (fun y => In A sub y /\ y <> a) n0).
        { apply cardinal_remove; assumption. }
        assert (Hincl0 : Included A la0 (fun y => In A sub y /\ y <> a)).
        {
          intros x Hx. split.
          - apply Hincl. unfold Add. apply Union_introl. exact Hx.
          - intro Heq. subst. exact (Ha_notin Hx).
        }
        assert (w0 <= n0) by exact (IH _ _ Hcard_minus Hincl0).
        lia.
  Qed.

  (** When n > w and sub is not entirely contained in Above la,
      (Above la) ∩ sub has cardinality strictly less than n.
      The extra hypothesis ~ Included A sub (Above R la) witnesses a strict
      subset, from which na < n follows by finite-set cardinality. *)
  Lemma above_card_lt : forall (sub la : Ensemble A) n w,
    cardinal A sub n ->
    w < n ->
    IsLargestAntichain R sub la w ->
    ~ Included A sub (Above R la) ->
    { na : nat | cardinal A (Intersection A (Above R la) sub) na /\ na < n }.
  Proof.
    intros sub la n w Hcard Hwn_lt Hla Hnotincl.
    destruct n as [| n']. { exfalso; lia. }
    (* Step 1: build the Prop-level witness x ∈ sub, x ∉ Above(la).
       We keep this as a Prop assert so we can destruct it freely. *)
    assert (Hex : exists x : A, In A sub x /\ ~ In A (Above R la) x).
    { apply not_all_ex_not in Hnotincl.
      destruct Hnotincl as [x Hx].
      apply imply_to_and in Hx.
      exact (ex_intro _ x Hx). }
    (* Step 2: lift the Prop existential to a Set-level sigma via CID *)
    destruct (constructive_indefinite_description _ Hex) as [x [Hx_sub Hx_not_above]].
    (* Step 3: cardinal A (sub \ {x}) = n' *)
    assert (Hcard_minus : cardinal A (fun y => In A sub y /\ y <> x) n').
    { apply cardinal_remove; assumption. }
    (* Step 4: Intersection ⊆ sub \ {x} since x ∉ Above(la) *)
    assert (Hincl_inter : Included A (Intersection A (Above R la) sub)
                                     (fun y => In A sub y /\ y <> x)).
    { intros z Hz. inversion Hz.
      split.
      - assumption.
      - intro Heq. subst. contradiction. }
    (* Step 5: Prop-level existential giving the cardinality bound *)
    assert (Hprop : exists na,
        cardinal A (Intersection A (Above R la) sub) na /\ na < S n').
    { assert (Hfin_sub : Finite A sub)
        by exact (cardinal_finite A sub (S n') Hcard).
      assert (Hfin_inter : Finite A (Intersection A (Above R la) sub)).
      { apply (Finite_downward_closed A sub Hfin_sub).
        intros z Hz. inversion Hz. assumption. }
      destruct (finite_cardinal A (Intersection A (Above R la) sub) Hfin_inter)
        as [na Hna].
      exists na. split. exact Hna.
      assert (Hle : na <= n')
        by exact (incl_card_le A
                   (Intersection A (Above R la) sub)
                   (fun y => In A sub y /\ y <> x)
                   na n' Hna Hcard_minus Hincl_inter).
      lia. }
    (* Step 6: lift the cardinality Prop existential to Set *)
    exact (constructive_indefinite_description _ Hprop).
  Qed.

  (** When n > w and sub is not entirely contained in Below la,
      (Below la) ∩ sub has cardinality strictly less than n.
      The extra hypothesis ~ Included A sub (Below R la) witnesses a strict
      subset, from which nb < n follows by finite-set cardinality. *)
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
      destruct Hnotincl as [x Hx].
      apply imply_to_and in Hx.
      exact (ex_intro _ x Hx). }
    destruct (constructive_indefinite_description _ Hex) as [x [Hx_sub Hx_not_below]].
    assert (Hcard_minus : cardinal A (fun y => In A sub y /\ y <> x) n').
    { apply cardinal_remove; assumption. }
    assert (Hincl_inter : Included A (Intersection A (Below R la) sub)
                                     (fun y => In A sub y /\ y <> x)).
    { intros z Hz. inversion Hz.
      split.
      - assumption.
      - intro Heq. subst. contradiction. }
    assert (Hprop : exists nb,
        cardinal A (Intersection A (Below R la) sub) nb /\ nb < S n').
    { assert (Hfin_sub : Finite A sub)
        by exact (cardinal_finite A sub (S n') Hcard).
      assert (Hfin_inter : Finite A (Intersection A (Below R la) sub)).
      { apply (Finite_downward_closed A sub Hfin_sub).
        intros z Hz. inversion Hz. assumption. }
      destruct (finite_cardinal A (Intersection A (Below R la) sub) Hfin_inter)
        as [nb Hnb].
      exists nb. split. exact Hnb.
      assert (Hle : nb <= n')
        by exact (incl_card_le A
                   (Intersection A (Below R la) sub)
                   (fun y => In A sub y /\ y <> x)
                   nb n' Hnb Hcard_minus Hincl_inter).
      lia. }
    exact (constructive_indefinite_description _ Hprop).
  Qed.

  (** Any finite set can be covered by singleton chains. *)
  Lemma singleton_chain_cover : forall (s : Ensemble A) n,
    cardinal A s n ->
    { cover : Ensemble (Ensemble A) | IsChainCover R s cover /\ cardinal (Ensemble A) cover n }.
  Proof.
    intros s n Hcard.
    (* Provide the cover explicitly: the set of all singletons of elements of s.
       Both goals (IsChainCover and cardinal) are then Prop-valued, so induction on
       Hcard is permitted for the cardinal part. *)
    exists (fun C => exists x, In A s x /\ C = Singleton A x).
    split.
    - (* IsChainCover *)
      constructor.
      + (* chain_cover_chains: each singleton is a chain *)
        intros C [x [Hx_in Heq_C]]. subst C.
        split.
        * apply Inhabited_intro with x. apply In_singleton.
        * intros a b Ha Hb. inversion Ha. inversion Hb. subst. left. apply poset_refl.
      + (* chain_cover_included: {x} ⊆ s since x ∈ s *)
        intros C [x [Hx_in Heq_C]]. subst C.
        intros y Hy. inversion Hy. subst y. exact Hx_in.
      + (* chain_cover_covers: y is covered by {y} *)
        intros y Hy.
        exists (Singleton A y). split.
        * exists y. split; [exact Hy | reflexivity].
        * apply In_singleton.
    - (* cardinal: goal is Prop-valued, so induction on Hcard is allowed *)
      induction Hcard as [| s0 m0 Hcard0 IH x Hx_notin].
      + (* n = 0: s = Empty_set, so singletons(s) = Empty_set *)
        assert (Hempty : (fun C => exists z, In A (Empty_set A) z /\ C = Singleton A z) =
                          Empty_set (Ensemble A)).
        { apply Extensionality_Ensembles. intro C. split.
          - intros [z [Hz _]]. inversion Hz.
          - intro HC. inversion HC. }
        rewrite Hempty. apply card_empty.
      + (* n = S m0: s = Add s0 x; singletons(Add s0 x) = Add (singletons s0) (Singleton A x) *)
        assert (Hset_eq :
          (fun C => exists z, In A (Add A s0 x) z /\ C = Singleton A z) =
          Add (Ensemble A) (fun C => exists z, In A s0 z /\ C = Singleton A z) (Singleton A x)).
        { apply Extensionality_Ensembles. intro C. split.
          - intros [z [Hz Heq_C]]. subst C.
            unfold Add in Hz.
            inversion Hz as [z' Hz' | z' Hz']; subst.
            + unfold Add. apply Union_introl. exists z. split; [exact Hz' | reflexivity].
            + inversion Hz'. subst z.
              unfold Add. apply Union_intror. apply In_singleton.
          - intro HC. unfold Add in HC.
            inversion HC as [C' HC' | C' HC']; subst.
            + destruct HC' as [z [Hz Heq_C]]. subst C.
              exists z. split.
              * unfold Add. apply Union_introl. exact Hz.
              * reflexivity.
            + inversion HC'. subst C.
              exists x. split.
              * unfold Add. apply Union_intror. apply In_singleton.
              * reflexivity. }
        rewrite Hset_eq.
        apply card_add.
        * exact IH.
        * (* Singleton A x ∉ singletons(s0): injectivity of Singleton *)
          intros [z [Hz Heq_z]].
          assert (Hx_in_sz : In A (Singleton A z) x).
          { rewrite <- Heq_z. apply In_singleton. }
          inversion Hx_in_sz; subst.
          exact (Hx_notin Hz).
  Qed.

  (** When sub is an antichain of size w = n, cover it with w singleton chains. *)
  Lemma antichain_singleton_cover : forall (sub la : Ensemble A) n,
    cardinal A sub n ->
    IsLargestAntichain R sub la n ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover n }.
  Proof.
    intros sub la n Hcard _.
    exact (singleton_chain_cover sub n Hcard).
  Qed.

  (** In a chain contained in Below R la, the la-element (if any) is the maximum
      of that chain, since any element above the la-element would have to lie
      above two la-elements, forcing them equal by the antichain condition. *)
  Lemma chain_la_is_max : forall (la C : Ensemble A) a y,
    IsAntichain R la ->
    IsChain R C ->
    Included A C (Below R la) ->
    In A C a ->
    In A la a ->
    In A C y ->
    R y a.
  Proof.
    intros la C a y Hanti Hchain Hincl Ha_C Ha_la Hy_C.
    destruct Hanti as [_ Hincompat].
    destruct Hchain as [_ Hcomp].
    assert (Hy_below : In A (Below R la) y) by exact (Hincl y Hy_C).
    destruct Hy_below as [b [Hb_la Hyb]].
    destruct (Hcomp a y Ha_C Hy_C) as [Ray | Rya].
    - assert (Hab : a = b).
      { apply Hincompat; [exact Ha_la | exact Hb_la | left].
        exact (poset_trans a y b Ray Hyb). }
      subst b. exact Hyb.
    - exact Rya.
  Qed.

  (** Elements of sub that are above a and have a as their unique la-ancestor
      form a chain.  If two such elements x, y were incomparable then
      {x, y} ∪ (la \ {a}) would be an antichain of size w+1 in sub,
      contradicting the maximality of la. *)
  Lemma above_unique_la_is_chain : forall (sub la : Ensemble A) w a,
    IsLargestAntichain R sub la w ->
    In A la a ->
    IsChain R (fun x => In A sub x /\ R a x /\ forall b, In A la b -> R b x -> b = a).
  Proof.
    intros sub la w a Hla Ha_la.
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    constructor.
    - (* a itself belongs to the set *)
      apply Inhabited_intro with a.
      refine (conj (Hincl_la a Ha_la) (conj (poset_refl a) _)).
      intros b Hb_la Hba.
      exact (Hincompat b a Hb_la Ha_la (or_introl Hba)).
    - intros x y [Hx_sub [Hax Hx_uniq]] [Hy_sub [Hay Hy_uniq]].
      destruct (classic (R x y \/ R y x)) as [Hcomp | Hincomp]; [exact Hcomp |].
      exfalso.
      assert (Hne : x <> y).
      { intro Heq. subst. apply Hincomp. left. apply poset_refl. }
      (* x is incomparable to every c ∈ la \ {a} *)
      assert (Hx_incomp : forall c, In A la c -> c <> a -> ~ R x c /\ ~ R c x).
      { intros c Hc_la Hca. split.
        - intro Hxc.
          assert (Hac : a = c).
          { apply Hincompat; [exact Ha_la | exact Hc_la | left].
            exact (poset_trans a x c Hax Hxc). }
          exact (Hca (eq_sym Hac)).
        - intro Hcx.
          exact (Hca (Hx_uniq c Hc_la Hcx)). }
      (* y is incomparable to every c ∈ la \ {a} *)
      assert (Hy_incomp : forall c, In A la c -> c <> a -> ~ R y c /\ ~ R c y).
      { intros c Hc_la Hca. split.
        - intro Hyc.
          assert (Hac : a = c).
          { apply Hincompat; [exact Ha_la | exact Hc_la | left].
            exact (poset_trans a y c Hay Hyc). }
          exact (Hca (eq_sym Hac)).
        - intro Hcy.
          exact (Hca (Hy_uniq c Hc_la Hcy)). }
      (* Get w = S w' to work with la \ {a} of cardinality w' *)
      destruct w as [| w'].
      { inversion Hcard_la; subst. inversion Ha_la. }
      assert (Hcard_minus : cardinal A (fun z => In A la z /\ z <> a) w').
      { apply cardinal_remove; assumption. }
      (* x ∉ la \ {a}: if x ∈ la then R a x forces a = x (antichain) *)
      assert (Hx_nla : ~ In A (fun z => In A la z /\ z <> a) x).
      { intros [Hx_la Hxa].
        assert (Hax' : a = x).
        { apply Hincompat; [exact Ha_la | exact Hx_la | left; exact Hax]. }
        exact (Hxa (eq_sym Hax')). }
      (* y ∉ Add (la \ {a}) x *)
      assert (Hy_nadd : ~ In A (Add A (fun z => In A la z /\ z <> a) x) y).
      { intro Hyin.
        inversion Hyin as [zz Hzz | zz Hzz]; subst zz.
        - destruct Hzz as [Hy_la Hya].
          assert (Hay' : a = y).
          { apply Hincompat; [exact Ha_la | exact Hy_la | left; exact Hay]. }
          exact (Hya (eq_sym Hay')).
        - inversion Hzz; subst. exact (Hne eq_refl). }
      (* Build the antichain {x, y} ∪ (la \ {a}) of size w'+2 = w+1 *)
      pose (antich := Add A (Add A (fun z => In A la z /\ z <> a) x) y).
      assert (Hcard_antich : cardinal A antich (S (S w'))).
      { unfold antich. apply card_add; [apply card_add |]; assumption. }
      assert (Hantich_anti : IsAntichain R antich).
      { constructor.
        - apply Inhabited_intro with y.
          unfold antich. apply Union_intror. apply In_singleton.
        - intros z1 z2 Hz1 Hz2 Hrel.
          assert (Hc1 : (In A la z1 /\ z1 <> a) \/ z1 = x \/ z1 = y).
          { unfold antich in Hz1.
            inversion Hz1 as [zz1 Hzz1 | zz1 Hzz1]; subst zz1.
            - inversion Hzz1 as [zz1' Hzz1' | zz1' Hzz1']; subst zz1'.
              + left. exact Hzz1'.
              + inversion Hzz1'; subst. right. left. reflexivity.
            - inversion Hzz1; subst. right. right. reflexivity. }
          assert (Hc2 : (In A la z2 /\ z2 <> a) \/ z2 = x \/ z2 = y).
          { unfold antich in Hz2.
            inversion Hz2 as [zz2 Hzz2 | zz2 Hzz2]; subst zz2.
            - inversion Hzz2 as [zz2' Hzz2' | zz2' Hzz2']; subst zz2'.
              + left. exact Hzz2'.
              + inversion Hzz2'; subst. right. left. reflexivity.
            - inversion Hzz2; subst. right. right. reflexivity. }
          destruct Hc1 as [[Hz1_la Hz1_ne] | [Hz1x | Hz1y]];
          destruct Hc2 as [[Hz2_la Hz2_ne] | [Hz2x | Hz2y]].
          + exact (Hincompat z1 z2 Hz1_la Hz2_la Hrel).
          + subst z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj2 (Hx_incomp z1 Hz1_la Hz1_ne) Hr).
            * exact (proj1 (Hx_incomp z1 Hz1_la Hz1_ne) Hr).
          + subst z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj2 (Hy_incomp z1 Hz1_la Hz1_ne) Hr).
            * exact (proj1 (Hy_incomp z1 Hz1_la Hz1_ne) Hr).
          + subst z1. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj1 (Hx_incomp z2 Hz2_la Hz2_ne) Hr).
            * exact (proj2 (Hx_incomp z2 Hz2_la Hz2_ne) Hr).
          + subst z1 z2. reflexivity.
          + subst z1 z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (Hincomp (or_introl Hr)).
            * exact (Hincomp (or_intror Hr)).
          + subst z1. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj1 (Hy_incomp z2 Hz2_la Hz2_ne) Hr).
            * exact (proj2 (Hy_incomp z2 Hz2_la Hz2_ne) Hr).
          + subst z1 z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (Hincomp (or_intror Hr)).
            * exact (Hincomp (or_introl Hr)).
          + subst z1 z2. reflexivity. }
      assert (Hantich_incl : Included A antich sub).
      { intros z Hz.
        unfold antich in Hz.
        inversion Hz as [zz Hzz | zz Hzz]; subst zz.
        - inversion Hzz as [zz' Hzz' | zz' Hzz']; subst zz'.
          + exact (Hincl_la z (proj1 Hzz')).
          + inversion Hzz'; subst. exact Hx_sub.
        - inversion Hzz; subst. exact Hy_sub. }
      assert (Hle : S (S w') <= S w').
      { exact (Hmax antich (S (S w')) Hantich_anti Hantich_incl Hcard_antich). }
      lia.
  Qed.

  (** Any chain cover of sub has cardinality ≥ w: the w elements of la must
      land in distinct chains (they are mutually incomparable), giving an
      injection la → cover.  The injection principle then yields w ≤ |cover|. *)
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
    - (* Totality: each a ∈ la lies in some chain of cover *)
      intros a Ha_la.
      destruct (Hcovers a (Hincl_la a Ha_la)) as [c [Hc_cov Hca]].
      exact (ex_intro _ c (conj Hc_cov Hca)).
    - (* Injectivity: if a, b ∈ la are both in chain c, then a = b *)
      intros a b c Ha_la Hb_la Hc_cov Hca Hcb.
      destruct (Hchains c Hc_cov) as [_ Hcomp].
      exact (Hincompat a b Ha_la Hb_la (Hcomp a b Hca Hcb)).
  Qed.

  (** The w fibers {x ∈ sub | f x = a} for a ∈ la form a cover set of
      cardinality w, provided f fixes every la-element (f a = a for a ∈ la). *)
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
    - (* la = ∅: the fiber set is empty *)
      apply (cardinal_extensional_poly (Ensemble A) (Empty_set (Ensemble A)) _ 0).
      + intro C. split.
        * intro Hbot. inversion Hbot.
        * intros [a [Ha _]]. inversion Ha.
      + apply card_empty.
    - (* la = Add la' a0 *)
      assert (Hincl' : Included A la' sub).
      { intros x Hx. apply Hincl. unfold Add. apply Union_introl. exact Hx. }
      assert (Hfxa' : forall a, In A la' a -> f a = a).
      { intros a Ha. apply Hfxa. unfold Add. apply Union_introl. exact Ha. }
      assert (Ha0_sub : In A sub a0).
      { apply Hincl. unfold Add. apply Union_intror. apply In_singleton. }
      assert (Ha0_f : f a0 = a0).
      { apply Hfxa. unfold Add. apply Union_intror. apply In_singleton. }
      (* Rewrite the fiber set as Add cover' fiber_{a0} *)
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
          + apply Union_introl.
            exact (ex_intro _ a (conj Hz Heq_C)).
          + inversion Hz. subst a. subst C.
            apply Union_intror. apply In_singleton.
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
        * (* fiber_{a0} ∉ cover': if it were, then a0 = some b ∈ la', contradiction *)
          intros [b [Hb_la' Heq_fiber]].
          assert (HRHS : In A sub a0 /\ f a0 = b) by
            exact (eq_rect _ (fun h : A -> Prop => h a0)
                     (conj Ha0_sub Ha0_f) _ Heq_fiber).
          assert (Ha0_b : a0 = b) by
            exact (eq_trans (eq_sym Ha0_f) (proj2 HRHS)).
          subst b.
          exact (Ha0_notin Hb_la').
  Qed.

  (** The hard matching core for the Above case: Hall's theorem / matching argument.
      There exists an assignment f mapping each x ∈ sub to some f(x) ∈ la
      with R (f(x)) x (la-ancestor), such that each fiber {x ∈ sub | f(x) = a}
      is a chain. *)
  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
  Admitted.

  (** The hard constructive core for the Above case: use above_chain_assignment_exists
      to assign each element of sub to a la-ancestor fiber chain.  The number of
      chains equals w because there are exactly w la-elements. *)
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
    (* f fixes la-elements: R (f a) a with a, f(a) ∈ la, antichain ⇒ f a = a *)
    assert (Hfxa : forall a, In A la a -> f a = a).
    { intros a Ha_la.
      destruct (Hf_assign a (Hincl_la a Ha_la)) as [Hfa_la Hfa_R].
      exact (Hincompat (f a) a Hfa_la Ha_la (or_introl Hfa_R)). }
    (* Build the fiber cover *)
    pose (cover := fun C => exists a, In A la a /\ C = (fun x => In A sub x /\ f x = a)).
    assert (Hcov : IsChainCover R sub cover).
    { constructor.
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C.
        exact (Hf_chain a Ha_la).
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C.
        intros x [Hx_sub _]. exact Hx_sub.
      - intros x Hx_sub.
        destruct (Hf_assign x Hx_sub) as [Hfx_la _].
        exact (ex_intro _ (fun y => In A sub y /\ f y = f x)
                 (conj (ex_intro _ (f x) (conj Hfx_la eq_refl))
                       (conj Hx_sub eq_refl))). }
    assert (Hcard_cov : cardinal (Ensemble A) cover w).
    { exact (below_fiber_cover_cardinal sub la w f Hcard_la Hincl_la Hfxa). }
    exact (exist _ (cover, w)
             (conj Hcov (conj Hcard_cov (Nat.le_refl w)))).
  Qed.

  (** chain_cover_of_above follows: chain_cover_above_existence gives a cover
      with n ≤ w chains; antichain_lb_for_chain_cover gives w ≤ n; so n = w. *)
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
    assert (Heq : n = w) by lia.
    subst n.
    exact (exist _ cover (conj Hcover Hcard)).
  Qed.

  (** Elements of sub that are below a and have a as their unique la-successor
      form a chain.  Symmetric to above_unique_la_is_chain: if x, y were
      incomparable then {x, y} ∪ (la \ {a}) would be an antichain of size w+1. *)
  Lemma below_unique_la_is_chain : forall (sub la : Ensemble A) w a,
    IsLargestAntichain R sub la w ->
    In A la a ->
    IsChain R (fun x => In A sub x /\ R x a /\ forall b, In A la b -> R x b -> b = a).
  Proof.
    intros sub la w a Hla Ha_la.
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    constructor.
    - (* a itself belongs to the set *)
      apply Inhabited_intro with a.
      refine (conj (Hincl_la a Ha_la) (conj (poset_refl a) _)).
      intros b Hb_la Hab.
      exact (eq_sym (Hincompat a b Ha_la Hb_la (or_introl Hab))).
    - intros x y [Hx_sub [Hxa Hx_uniq]] [Hy_sub [Hya Hy_uniq]].
      destruct (classic (R x y \/ R y x)) as [Hcomp | Hincomp]; [exact Hcomp |].
      exfalso.
      assert (Hne : x <> y).
      { intro Heq. subst. apply Hincomp. left. apply poset_refl. }
      (* x is incomparable to every c ∈ la \ {a} *)
      assert (Hx_incomp : forall c, In A la c -> c <> a -> ~ R x c /\ ~ R c x).
      { intros c Hc_la Hca. split.
        - intro Hxc.
          exact (Hca (Hx_uniq c Hc_la Hxc)).
        - intro Hcx.
          assert (Hca' : c = a).
          { apply Hincompat; [exact Hc_la | exact Ha_la | left].
            exact (poset_trans c x a Hcx Hxa). }
          exact (Hca Hca'). }
      (* y is incomparable to every c ∈ la \ {a} *)
      assert (Hy_incomp : forall c, In A la c -> c <> a -> ~ R y c /\ ~ R c y).
      { intros c Hc_la Hca. split.
        - intro Hyc.
          exact (Hca (Hy_uniq c Hc_la Hyc)).
        - intro Hcy.
          assert (Hca' : c = a).
          { apply Hincompat; [exact Hc_la | exact Ha_la | left].
            exact (poset_trans c y a Hcy Hya). }
          exact (Hca Hca'). }
      (* Get w = S w' to work with la \ {a} of cardinality w' *)
      destruct w as [| w'].
      { inversion Hcard_la; subst. inversion Ha_la. }
      assert (Hcard_minus : cardinal A (fun z => In A la z /\ z <> a) w').
      { apply cardinal_remove; assumption. }
      (* x ∉ la \ {a}: if x ∈ la then R x a forces x = a (antichain) *)
      assert (Hx_nla : ~ In A (fun z => In A la z /\ z <> a) x).
      { intros [Hx_la Hxa'].
        assert (Hax' : x = a).
        { apply Hincompat; [exact Hx_la | exact Ha_la | left; exact Hxa]. }
        exact (Hxa' Hax'). }
      (* y ∉ Add (la \ {a}) x *)
      assert (Hy_nadd : ~ In A (Add A (fun z => In A la z /\ z <> a) x) y).
      { intro Hyin.
        inversion Hyin as [zz Hzz | zz Hzz]; subst zz.
        - destruct Hzz as [Hy_la Hya'].
          assert (Hay' : y = a).
          { apply Hincompat; [exact Hy_la | exact Ha_la | left; exact Hya]. }
          exact (Hya' Hay').
        - inversion Hzz; subst. exact (Hne eq_refl). }
      (* Build the antichain {x, y} ∪ (la \ {a}) of size w'+2 = w+1 *)
      pose (antich := Add A (Add A (fun z => In A la z /\ z <> a) x) y).
      assert (Hcard_antich : cardinal A antich (S (S w'))).
      { unfold antich. apply card_add; [apply card_add |]; assumption. }
      assert (Hantich_anti : IsAntichain R antich).
      { constructor.
        - apply Inhabited_intro with y.
          unfold antich. apply Union_intror. apply In_singleton.
        - intros z1 z2 Hz1 Hz2 Hrel.
          assert (Hc1 : (In A la z1 /\ z1 <> a) \/ z1 = x \/ z1 = y).
          { unfold antich in Hz1.
            inversion Hz1 as [zz1 Hzz1 | zz1 Hzz1]; subst zz1.
            - inversion Hzz1 as [zz1' Hzz1' | zz1' Hzz1']; subst zz1'.
              + left. exact Hzz1'.
              + inversion Hzz1'; subst. right. left. reflexivity.
            - inversion Hzz1; subst. right. right. reflexivity. }
          assert (Hc2 : (In A la z2 /\ z2 <> a) \/ z2 = x \/ z2 = y).
          { unfold antich in Hz2.
            inversion Hz2 as [zz2 Hzz2 | zz2 Hzz2]; subst zz2.
            - inversion Hzz2 as [zz2' Hzz2' | zz2' Hzz2']; subst zz2'.
              + left. exact Hzz2'.
              + inversion Hzz2'; subst. right. left. reflexivity.
            - inversion Hzz2; subst. right. right. reflexivity. }
          destruct Hc1 as [[Hz1_la Hz1_ne] | [Hz1x | Hz1y]];
          destruct Hc2 as [[Hz2_la Hz2_ne] | [Hz2x | Hz2y]].
          + exact (Hincompat z1 z2 Hz1_la Hz2_la Hrel).
          + subst z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj2 (Hx_incomp z1 Hz1_la Hz1_ne) Hr).
            * exact (proj1 (Hx_incomp z1 Hz1_la Hz1_ne) Hr).
          + subst z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj2 (Hy_incomp z1 Hz1_la Hz1_ne) Hr).
            * exact (proj1 (Hy_incomp z1 Hz1_la Hz1_ne) Hr).
          + subst z1. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj1 (Hx_incomp z2 Hz2_la Hz2_ne) Hr).
            * exact (proj2 (Hx_incomp z2 Hz2_la Hz2_ne) Hr).
          + subst z1 z2. reflexivity.
          + subst z1 z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (Hincomp (or_introl Hr)).
            * exact (Hincomp (or_intror Hr)).
          + subst z1. exfalso. destruct Hrel as [Hr | Hr].
            * exact (proj1 (Hy_incomp z2 Hz2_la Hz2_ne) Hr).
            * exact (proj2 (Hy_incomp z2 Hz2_la Hz2_ne) Hr).
          + subst z1 z2. exfalso. destruct Hrel as [Hr | Hr].
            * exact (Hincomp (or_intror Hr)).
            * exact (Hincomp (or_introl Hr)).
          + subst z1 z2. reflexivity. }
      assert (Hantich_incl : Included A antich sub).
      { intros z Hz.
        unfold antich in Hz.
        inversion Hz as [zz Hzz | zz Hzz]; subst zz.
        - inversion Hzz as [zz' Hzz' | zz' Hzz']; subst zz'.
          + exact (Hincl_la z (proj1 Hzz')).
          + inversion Hzz'; subst. exact Hx_sub.
        - inversion Hzz; subst. exact Hy_sub. }
      assert (Hle : S (S w') <= S w').
      { exact (Hmax antich (S (S w')) Hantich_anti Hantich_incl Hcard_antich). }
      lia.
  Qed.

  (** The hard matching core: Hall's theorem / matching argument.
      There exists an assignment f mapping each x ∈ sub to some f(x) ∈ la
      with R x (f(x)), such that each fiber {x ∈ sub | f(x) = a} is a chain. *)
  Lemma below_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R x (f x)) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
  Admitted.

  (** chain_cover_below_extend: proved by constructing the fiber cover from
      below_chain_assignment_exists, with cardinality from below_fiber_cover_cardinal.
      The cov_la parameter is unused — it was needed only for below_chain_cover_existence. *)
  Lemma chain_cover_below_extend : forall (sub la : Ensemble A) w
      (cov_la : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    IsChainCover R la cov_la ->
    cardinal (Ensemble A) cov_la w ->
    { p : Ensemble (Ensemble A) * nat |
        IsChainCover R sub (fst p) /\
        cardinal (Ensemble A) (fst p) (snd p) /\
        (snd p) <= w }.
  Proof.
    intros sub la w cov_la Hla Hbelow _ _.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    destruct (constructive_indefinite_description _
               (below_chain_assignment_exists sub la w Hla' Hbelow))
      as [f [Hf_assign Hf_chain]].
    (* f fixes la-elements: R a (f a) with a,f(a) ∈ la, antichain ⇒ f a = a *)
    assert (Hfxa : forall a, In A la a -> f a = a).
    { intros a Ha_la.
      destruct (Hf_assign a (Hincl_la a Ha_la)) as [Hfa_la Hfa_R].
      exact (eq_sym (Hincompat a (f a) Ha_la Hfa_la (or_introl Hfa_R))). }
    (* Build the fiber cover *)
    pose (cover := fun C => exists a, In A la a /\ C = (fun x => In A sub x /\ f x = a)).
    assert (Hcov : IsChainCover R sub cover).
    { constructor.
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C.
        exact (Hf_chain a Ha_la).
      - intros C HC. destruct HC as [a [Ha_la Heq_C]]. subst C.
        intros x [Hx_sub _]. exact Hx_sub.
      - intros x Hx_sub.
        destruct (Hf_assign x Hx_sub) as [Hfx_la _].
        exact (ex_intro _ (fun y => In A sub y /\ f y = f x)
                 (conj (ex_intro _ (f x) (conj Hfx_la eq_refl))
                       (conj Hx_sub eq_refl))). }
    assert (Hcard_cov : cardinal (Ensemble A) cover w).
    { exact (below_fiber_cover_cardinal sub la w f Hcard_la Hincl_la Hfxa). }
    exact (exist _ (cover, w)
             (conj Hcov (conj Hcard_cov (Nat.le_refl w)))).
  Qed.

  (** chain_cover_below_existence: start with the w-singleton cover of la
      (from singleton_chain_cover), then extend via chain_cover_below_extend. *)
  Lemma chain_cover_below_existence : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    { p : Ensemble (Ensemble A) * nat |
        IsChainCover R sub (fst p) /\
        cardinal (Ensemble A) (fst p) (snd p) /\
        (snd p) <= w }.
  Proof.
    intros sub la w Hla Hbelow.
    assert (Hcard_la : cardinal A la w) by (destruct Hla; assumption).
    destruct (singleton_chain_cover la w Hcard_la) as [cov_la [Hcov_la Hcard_cov]].
    exact (chain_cover_below_extend sub la w cov_la Hla Hbelow Hcov_la Hcard_cov).
  Qed.

  (** chain_cover_of_below follows by the same counting argument:
      chain_cover_below_existence gives n ≤ w; antichain_lb gives w ≤ n. *)
  Lemma chain_cover_of_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w Hla Hbelow.
    destruct (chain_cover_below_existence sub la w Hla Hbelow) as [[cover n] [Hcover [Hcard Hle]]].
    simpl in *.
    assert (Hge : w <= n) by
      exact (antichain_lb_for_chain_cover sub la w n cover Hla Hcover Hcard).
    assert (Heq : n = w) by lia.
    subst n.
    exact (exist _ cover (conj Hcover Hcard)).
  Qed.

  (** When sub ⊆ Above(la) the input cover_b is not needed: we delegate
      directly to chain_cover_of_above which builds the cover from scratch. *)
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

  (** Symmetric. *)
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

  (** A chain cover of (Above la ∩ sub) and a chain cover of (Below la ∩ sub),
      each of size w, can be interleaved at la into a chain cover of sub of size w. *)
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
  Admitted.

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
    (* w ≤ n *)
    assert (Hwn : w <= n) by exact (la_card_le_sub sub la n w Hcard Hla).
    (* If w = n then sub itself is an antichain, covered by w singleton chains *)
    destruct (Nat.eq_dec w n) as [Hwn_eq | Hwn_ne].
    { subst n. exact (antichain_singleton_cover sub la w Hcard Hla). }
    assert (Hwn_lt : w < n) by lia.
    (* Case split on Above / Below inclusions *)
    destruct (excluded_middle_informative (Included A sub (Above R la))) as [Habove | Hnotabove].
    { destruct (excluded_middle_informative (Included A sub (Below R la))) as [Hbelow | Hnotbelow].
      { (* Case D: sub ⊆ Above ∧ sub ⊆ Below → sub ⊆ la → n ≤ w, contradicts w < n *)
        exfalso.
        destruct Hla as [Hanti Hincl_la Hcard_la _].
        destruct Hanti as [_ Hanti_incompat].
        assert (Hsub_la : Included A sub la).
        { intros x Hx.
          assert (Hx_above : In A (Above R la) x) by exact (Habove x Hx).
          assert (Hx_below : In A (Below R la) x) by exact (Hbelow x Hx).
          unfold Above in Hx_above. destruct Hx_above as [a [Ha_la Hra_x]].
          unfold Below in Hx_below. destruct Hx_below as [b [Hb_la Hrx_b]].
          assert (Hrab : R a b) by exact (poset_trans a x b Hra_x Hrx_b).
          assert (Hab : a = b) by exact (Hanti_incompat a b Ha_la Hb_la (or_introl Hrab)).
          subst b.
          rewrite (poset_antisym x a Hrx_b Hra_x). exact Ha_la. }
        assert (Hle : n <= w) by exact (incl_card_le A sub la n w Hcard Hcard_la Hsub_la).
        lia. }
      { (* Case B: sub ⊆ Above R la, sub ⊄ Below R la *)
        destruct (below_card_lt sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (extend_cover_above sub la w cover_b Hla Habove Hcover_b Hcard_b). } }
    { destruct (excluded_middle_informative (Included A sub (Below R la))) as [Hbelow | Hnotbelow].
      { (* Case C: sub ⊄ Above R la, sub ⊆ Below R la *)
        destruct (above_card_lt sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        exact (extend_cover_below sub la w cover_a Hla Hbelow Hcover_a Hcard_a). }
      { (* Case A: sub ⊄ Above ∧ sub ⊄ Below *)
        destruct (above_card_lt sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
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
    - (* w = 0: empty antichain - contradiction *)
      exfalso.
      apply (empty_antichain_contradiction la).
      + destruct Hla; assumption.
      + destruct Hla; assumption.
      
    - (* w = S w' *)
      destruct w' as [| w''].
      + (* w = 1: singleton antichain *)
        exists (Singleton (Ensemble A) sub).
        destruct Hla as [Hanti Hincl_la Hcard_w Hmax].
        split.
        * constructor.
          -- intros c Hc. inversion Hc. subst c.
             apply (width_one_implies_chain sub la).
             constructor; [exact Hanti | exact Hincl_la | exact Hcard_w | exact Hmax].
          -- intros c Hc. inversion Hc. subst c.
             intros x Hx. exact Hx.
          -- intros x Hx.
             exists sub. split.
             ++ apply In_singleton.
             ++ exact Hx.
        * replace 1 with (S 0) by reflexivity.
          apply (cardinal_extensional_poly (Ensemble A) (Add (Ensemble A) (Empty_set (Ensemble A)) sub) (Singleton (Ensemble A) sub) 1).
          -- intro X. split; intro HX.
             ++ unfold Add in HX. inversion HX as [X' HX' | X' HX']; subst.
                ** inversion HX'.
                ** inversion HX'. apply In_singleton.
             ++ inversion HX. subst X. unfold Add. apply Union_intror. apply In_singleton.
          -- apply card_add; [apply card_empty; intros X HX; inversion HX | intro Hcontra; inversion Hcontra].
          
      + (* w = S (S w''): use inductive step *)
        eapply dilworth_inductive_step.
        * exact Hcard_n.
        * lia.
        * exact Hla.
        * intros n' sub' la' w_prime Hn_prime Hcard_n' Hla'.
          apply (IH n' Hn_prime sub' w_prime la' Hcard_n' Hla').
  Qed.



End DilworthBackward.

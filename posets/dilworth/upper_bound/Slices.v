(* Structural lemmas relating a subposet to its largest antichain via Above/Below.
   Used throughout the upper-bound proof to slice sub by its position relative to la. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section Slices.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

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

End Slices.

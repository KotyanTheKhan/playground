(* The backward direction of Dilworth's theorem:
   any subposet with largest antichain of size w admits a chain cover of size w.
   Proceeds by strong induction on |sub|, using merge_above_below_covers
   to combine Above- and Below-side covers when sub straddles la. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas WidthLowerBound Helpers Hall
                              upper_bound.Slices upper_bound.HallDefect
                              upper_bound.BaseCases upper_bound.Iter
                              upper_bound.HallKernel upper_bound.Cover
                              upper_bound.Merge.

Section Backward.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Local Notation StrictSucc := (HallDefect.StrictSucc R).
  Local Notation StrictPred := (HallDefect.StrictPred R).

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
    assert (HfinSub : Finite A sub) by exact (cardinal_finite A sub n Hcard).
    assert (Hwn : w <= n) by exact (la_card_le_sub R sub la n w Hcard Hla).
    destruct (Nat.eq_dec w n) as [Hwn_eq | Hwn_ne].
    { subst n. exact (antichain_singleton_cover R sub la w Hcard Hla). }
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
      { destruct (below_card_lt R sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below R sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (Cover.extend_cover_above R sub la w cover_b Hla Habove HfinSub Hcover_b Hcard_b). } }
    { destruct (excluded_middle_informative (Included A sub (Below R la))) as [Hbelow | Hnotbelow].
      { destruct (above_card_lt R sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above R sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        exact (Cover.extend_cover_below R sub la w cover_a Hla Hbelow HfinSub Hcover_a Hcard_a). }
      { destruct (above_card_lt R sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (below_card_lt R sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above R sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below R sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (merge_above_below_covers R sub la w cover_a cover_b Hla
                 (sub_in_above_or_below R sub la w Hla)
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
      apply (empty_antichain_contradiction R la).
      + destruct Hla; assumption.
      + destruct Hla; assumption.
    - destruct w' as [| w''].
      + exists (Singleton (Ensemble A) sub).
        destruct Hla as [Hanti Hincl_la Hcard_w Hmax].
        split.
        * constructor.
          -- intros c Hc. inversion Hc. subst c.
             apply (width_one_implies_chain R sub la).
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

End Backward.

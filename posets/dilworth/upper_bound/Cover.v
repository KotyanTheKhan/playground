(* Chain covers derived from the assignment kernel.

   The Above variant applies chain_assignment_kernel directly with R.
   The Below variant (added in the next task) applies it with flip R,
   using small duality lemmas to translate hypotheses and conclusions. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas Helpers
                              upper_bound.Slices upper_bound.HallDefect
                              upper_bound.BaseCases upper_bound.HallKernel.

Section Cover.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Habove HfinSub.
    exact (HallKernel.chain_assignment_kernel R sub la w Hla Habove HfinSub).
  Qed.

  Lemma chain_cover_above_existence : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    { p : Ensemble (Ensemble A) * nat |
        IsChainCover R sub (fst p) /\
        cardinal (Ensemble A) (fst p) (snd p) /\
        (snd p) <= w }.
  Proof.
    intros sub la w Hla Habove HfinSub.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la _].
    destruct Hanti as [_ Hincompat].
    destruct (constructive_indefinite_description _
               (above_chain_assignment_exists sub la w Hla' Habove HfinSub))
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
    Finite A sub ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w Hla Habove HfinSub.
    destruct (chain_cover_above_existence sub la w Hla Habove HfinSub) as [[cover n] [Hcover [Hcard Hle]]].
    simpl in *.
    assert (Hge : w <= n) by
      exact (antichain_lb_for_chain_cover R sub la w n cover Hla Hcover Hcard).
    assert (Heq : n = w) by lia. subst n.
    exact (exist _ cover (conj Hcover Hcard)).
  Qed.

  Lemma extend_cover_above : forall (sub la : Ensemble A) w
      (cover_b : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    IsChainCover R (Intersection A (Below R la) sub) cover_b ->
    cardinal (Ensemble A) cover_b w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w _cover_b Hla Habove HfinSub _ _.
    exact (chain_cover_of_above sub la w Hla Habove HfinSub).
  Qed.

End Cover.

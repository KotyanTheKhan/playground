(* Combine Above- and Below-side chain covers into a single chain cover of sub.
   Used by dilworth_inductive_step when neither sub ⊆ Above(la) nor sub ⊆ Below(la). *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas Helpers
                              upper_bound.Slices.

Section Merge.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

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
    assert (Hca_exists : forall a, In A la a ->
              exists Ca, In (Ensemble A) cover_a Ca /\ In A Ca a).
    { intros a Ha.
      exact (chain_cover_covers R (IsChainCover := Hcov_a) a (Hla_above a Ha)). }
    assert (Hcb_exists : forall a, In A la a ->
              exists Cb, In (Ensemble A) cover_b Cb /\ In A Cb a).
    { intros a Ha.
      exact (chain_cover_covers R (IsChainCover := Hcov_b) a (Hla_below a Ha)). }
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
    assert (Hca_surj : forall Ca, In (Ensemble A) cover_a Ca ->
              exists a, In A la a /\ ca a = Ca).
    { intros Ca HCa.
      destruct (classic (exists a, In A la a /\ ca a = Ca)) as [Hex | Hnex].
      - exact Hex.
      - exfalso.
        (* Ca is not in the range of ca|_la. So ca maps la into cover_a \ {Ca}. *)
        assert (Hno_hit : forall a, In A la a -> ca a <> Ca).
        { intros a Ha Heq. apply Hnex. exact (ex_intro _ a (conj Ha Heq)). }
        destruct w as [| w'].
        { destruct Hinhab as [a Ha]. inversion Hcard_la. subst. inversion Ha. }
        assert (Hcard_minus : cardinal (Ensemble A)
                  (fun D => In (Ensemble A) cover_a D /\ D <> Ca) w').
        { apply cardinal_remove; assumption. }
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
    pose (merged := fun E : Ensemble A =>
      exists a, In A la a /\ E = Union A (ca a) (cb a)).
    exists merged.
    assert (Hmerged_cov : IsChainCover R sub merged).
    { constructor.
      - intros E HE. destruct HE as [a [Ha_la Heq_E]]. subst E.
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
      - intros E HE. destruct HE as [a [Ha_la Heq_E]]. subst E.
        destruct (Hca_spec a Ha_la) as [HCa _].
        destruct (Hcb_spec a Ha_la) as [HCb _].
        intros x Hx.
        inversion Hx as [x' Hx' | x' Hx']; subst x'.
        + destruct (chain_cover_included R (IsChainCover := Hcov_a) (ca a) HCa x Hx').
          assumption.
        + destruct (chain_cover_included R (IsChainCover := Hcov_b) (cb a) HCb x Hx').
          assumption.
      - intros x Hx.
        pose proof (Hunion x Hx) as Hx_union.
        destruct Hx_union as [x0 Hx_ab | x0 Hx_ab].
        + assert (Hx_inter : In A (Intersection A (Above R la) sub) x0)
            by exact (Intersection_intro _ _ _ x0 Hx_ab Hx).
          destruct (chain_cover_covers R (IsChainCover := Hcov_a) x0 Hx_inter)
            as [Ca' [HCa' Hx_Ca']].
          (* By surjectivity, Ca' = ca(a') for some a' ∈ la *)
          destruct (Hca_surj Ca' HCa') as [a' [Ha'_la Hca_eq]].
          exists (Union A (ca a') (cb a')). split.
          { exists a'. exact (conj Ha'_la eq_refl). }
          { apply Union_introl. rewrite Hca_eq. exact Hx_Ca'. }
        + assert (Hx_inter : In A (Intersection A (Below R la) sub) x0)
            by exact (Intersection_intro _ _ _ x0 Hx_ab Hx).
          destruct (chain_cover_covers R (IsChainCover := Hcov_b) x0 Hx_inter)
            as [Cb' [HCb' Hx_Cb']].
          (* By surjectivity, Cb' = cb(a') for some a' ∈ la *)
          destruct (Hcb_surj Cb' HCb') as [a' [Ha'_la Hcb_eq]].
          exists (Union A (ca a') (cb a')). split.
          { exists a'. exact (conj Ha'_la eq_refl). }
          { apply Union_intror. rewrite Hcb_eq. exact Hx_Cb'. } }
    split; [exact Hmerged_cov |].
    assert (Hla_full : IsLargestAntichain R sub la w).
    { constructor; [constructor; [exact Hinhab | exact Hincompat]
      | exact Hincl_la | exact Hcard_la | exact Hmax]. }
    pose (f := fun a => Union A (ca a) (cb a)).
    assert (Hmerged_eq : forall E, In (Ensemble A) merged E <->
              exists a, In A la a /\ E = f a).
    { intros E. split; intros [a [Ha Heq]]; exists a; exact (conj Ha Heq). }
    assert (Hmerged_ext : merged = (fun E => exists a, In A la a /\ E = f a)).
    { apply Extensionality_Ensembles. intro E. split.
      - intro HE. exact (proj1 (Hmerged_eq E) HE).
      - intro HE. exact (proj2 (Hmerged_eq E) HE). }
    destruct (image_cardinal_le la f w Hcard_la) as [m [Hcard_img Hm_le]].
    assert (Himg_eq : (fun y : Ensemble A => exists x, In A la x /\ y = f x) = merged).
    { apply Extensionality_Ensembles. intro E. split.
      - intros [a [Ha Heq]]. exists a. exact (conj Ha Heq).
      - intros [a [Ha Heq]]. exists a. exact (conj Ha Heq). }
    rewrite Himg_eq in Hcard_img.
    assert (Hge : w <= m).
    { exact (antichain_lb_for_chain_cover R sub la w m merged
               Hla_full Hmerged_cov Hcard_img). }
    assert (Heq : m = w) by lia.
    subst m. exact Hcard_img.
  Qed.

End Merge.

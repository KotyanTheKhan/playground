(* Parameterized chain-assignment kernel for Dilworth's backward direction.

   Given a poset R', a finite sub ⊆ Above R' la with la its largest antichain
   of size w, produces an assignment f : A → A with:
     - f x ∈ la and R' (f x) x for every x ∈ sub
     - the fiber {x ∈ sub | f x = a} is an R'-chain for every a ∈ la

   Cover.v applies this twice: once with R' := R (the Above case) and once
   with R' := flip R (the Below case). *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas Helpers Hall
                              upper_bound.Slices upper_bound.HallDefect
                              upper_bound.Iter.

Section HallKernel.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Local Notation StrictSucc := (HallDefect.StrictSucc R).
  Local Notation StrictPred := (HallDefect.StrictPred R).

  (* The inl-image of a finite subset of A inside sum A A has the same cardinal. *)
  Lemma inl_image_cardinal : forall (S : Ensemble A) n,
    cardinal A S n ->
    cardinal (sum A A)
      (fun z => match z with inl y => In A S y | inr _ => False end) n.
  Proof.
    intros S n Hcard.
    induction Hcard as [| S' k Hcard' IH a Ha_notin].
    - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
      + intro z. split.
        * intro Hz. inversion Hz.
        * intro Hz. destruct z as [y|b]; simpl in Hz; inversion Hz.
      + apply card_empty.
    - apply (cardinal_extensional_poly (sum A A)
            (Add (sum A A)
              (fun z => match z with inl y => In A S' y | inr _ => False end)
              (inl a))).
      + intro z. split.
        * intro Hz. unfold Add in Hz.
          inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
          -- destruct z as [y | b].
             ++ apply Union_introl. simpl in Hu. exact Hu.
             ++ simpl in Hu. exact (False_rect _ Hu).
          -- inversion Hu. subst z. apply Union_intror. apply In_singleton.
        * intro Hz. destruct z as [y | b].
          -- simpl in Hz.
             inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
             ++ apply Union_introl. simpl. exact Hu.
             ++ inversion Hu. subst y. apply Union_intror. apply In_singleton.
          -- simpl in Hz. exact (False_rect _ Hz).
      + apply card_add. exact IH.
        intro Hcontra. simpl in Hcontra. exact (Ha_notin Hcontra).
  Qed.

  (* The inr-image of a finite subset of A inside sum A A has the same cardinal. *)
  Lemma inr_image_cardinal : forall (T : Ensemble A) n,
    cardinal A T n ->
    cardinal (sum A A)
      (fun z => match z with inl _ => False | inr a => In A T a end) n.
  Proof.
    intros T n Hcard.
    induction Hcard as [| T' k Hcard' IH a Ha_notin].
    - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
      + intro z. split.
        * intro Hz. inversion Hz.
        * intro Hz. destruct z as [y|b]; simpl in Hz; inversion Hz.
      + apply card_empty.
    - apply (cardinal_extensional_poly (sum A A)
            (Add (sum A A)
              (fun z => match z with inl _ => False | inr a => In A T' a end)
              (inr a))).
      + intro z. split.
        * intro Hz. unfold Add in Hz.
          inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
          -- destruct z as [y | b].
             ++ simpl in Hu. exact (False_rect _ Hu).
             ++ apply Union_introl. simpl in Hu. exact Hu.
          -- inversion Hu. subst z. apply Union_intror. apply In_singleton.
        * intro Hz. destruct z as [y | b].
          -- simpl in Hz. exact (False_rect _ Hz).
          -- simpl in Hz.
             inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
             ++ apply Union_introl. simpl. exact Hu.
             ++ inversion Hu. subst b. apply Union_intror. apply In_singleton.
      + apply card_add. exact IH.
        intro Hcontra. simpl in Hcontra. exact (Ha_notin Hcontra).
  Qed.

  (* The augmented right-side Y = inl-image(sub) ⊎ inr-image(la) has cardinal nx + w. *)
  Lemma Y_cardinal : forall (sub la : Ensemble A) nx w,
    cardinal A sub nx ->
    cardinal A la w ->
    cardinal (sum A A)
      (fun z : sum A A =>
        match z with inl y => In A sub y | inr a => In A la a end)
      (nx + w).
  Proof.
    intros sub la nx w Hcard_sub Hcard_la.
    apply (cardinal_extensional_poly (sum A A)
        (Union (sum A A)
          (fun z => match z with inl y => In A sub y | inr _ => False end)
          (fun z => match z with inl _ => False | inr a => In A la a end))).
    - intro z. split; intro Hz.
      + destruct z as [y | a].
        * inversion Hz as [u Hu | u Hu]; subst u; simpl in Hu; [exact Hu | exact (False_rect _ Hu)].
        * inversion Hz as [u Hu | u Hu]; subst u; simpl in Hu; [exact (False_rect _ Hu) | exact Hu].
      + destruct z as [y | a].
        * apply Union_introl. exact Hz.
        * apply Union_intror. exact Hz.
    - apply cardinal_disjoint_union_gen.
      + intros z Hl Hr. destruct z; simpl in *; [exact Hr | exact Hl].
      + exact (inl_image_cardinal sub nx Hcard_sub).
      + exact (inr_image_cardinal la w Hcard_la).
  Qed.

  (* set_neighbors of the augmented matching graph decomposes as
     inl(StrictPred sub S) ⊎ inr(la) for any nonempty S ⊆ sub. *)
  Lemma nbrs_aug_neighbors_eq : forall (sub la : Ensemble A)
      (nbrs_aug : A -> sum A A -> Prop),
    (forall x z, nbrs_aug x z <->
       match z with
       | inl y => In A sub y /\ R y x /\ y <> x
       | inr a => In A la a
       end) ->
    forall S,
    Inhabited A S ->
    set_neighbors nbrs_aug S =
      Union (sum A A)
        (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
        (fun z => match z with inl _ => False | inr a => In A la a end).
  Proof.
    intros sub la nbrs_aug Hnbrs S HinhS.
    apply Extensionality_Ensembles. intro z. split.
    - intros [x [Hx Hz]]. apply Hnbrs in Hz.
      destruct z as [y | a].
      + apply Union_introl. unfold StrictPred.
        destruct Hz as [Hy [HRyx Hne]].
        exact (conj Hy (ex_intro _ x (conj Hx (conj HRyx (fun h => Hne (eq_sym h)))))).
      + apply Union_intror. exact Hz.
    - intro Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
      + destruct z as [y | a]. 2: exact (False_rect _ Hz').
        simpl in Hz'. unfold StrictPred in Hz'.
        destruct Hz' as [Hy [x [Hx [HRyx Hne]]]].
        exists x. split. exact Hx. apply Hnbrs.
        exact (conj Hy (conj HRyx (fun h => Hne (eq_sym h)))).
      + destruct z as [y | a]. exact (False_rect _ Hz').
        simpl in Hz'.
        destruct HinhS as [x0 Hx0].
        exists x0. split. exact Hx0. apply Hnbrs. exact Hz'.
  Qed.

  (* Hall's marriage condition for the augmented matching graph,
     discharged via dilworth_hall_defect_pred. *)
  Lemma hall_condition_holds : forall (sub la : Ensemble A) w
      (nbrs_aug : A -> sum A A -> Prop),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    cardinal A la w ->
    (forall x z, nbrs_aug x z <->
       match z with
       | inl y => In A sub y /\ R y x /\ y <> x
       | inr a => In A la a
       end) ->
    HallCondition sub nbrs_aug.
  Proof.
    intros sub la w nbrs_aug Hla Habove HfinSub Hcard_la Hnbrs.
    intros S ns nn HinclS HcardS HcardNS.
    destruct ns as [| ns'].
    { lia. }
    assert (HinhS : Inhabited A S).
    { inversion HcardS as [| S0 m Hm x Hx_notin]. subst.
      apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
    assert (HfinSP : Finite A (StrictPred sub S)).
    { apply (Finite_downward_closed A sub HfinSub). intros y Hy. exact (proj1 Hy). }
    destruct (finite_cardinal A (StrictPred sub S) HfinSP) as [nP HcardSP].
    pose proof (nbrs_aug_neighbors_eq sub la nbrs_aug Hnbrs S HinhS) as Hset_eq.
    assert (HcardInlP : cardinal (sum A A)
        (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end) nP)
      by exact (inl_image_cardinal (StrictPred sub S) nP HcardSP).
    assert (HcardInrLa : cardinal (sum A A)
        (fun z => match z with inl _ => False | inr a => In A la a end) w)
      by exact (inr_image_cardinal la w Hcard_la).
    assert (HcardUnion : cardinal (sum A A)
        (Union (sum A A)
          (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
          (fun z => match z with inl _ => False | inr a => In A la a end))
        (nP + w)).
    { apply cardinal_disjoint_union_gen.
      - intros z Hl Hr. destruct z. exact Hr. exact Hl.
      - exact HcardInlP.
      - exact HcardInrLa. }
    assert (Hnn_eq : nn = nP + w).
    { apply (cardinal_unicity (sum A A) (set_neighbors nbrs_aug S)).
      - exact HcardNS.
      - apply (cardinal_extensional_poly (sum A A)
            (Union (sum A A)
              (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
              (fun z => match z with inl _ => False | inr a => In A la a end))).
        + intro z. rewrite <- Hset_eq. tauto.
        + exact HcardUnion. }
    assert (Hns_le : Datatypes.S ns' <= nP + w).
    { apply (dilworth_hall_defect_pred R sub la w Hla Habove S (Datatypes.S ns') nP).
      - exact HinclS.
      - exact HcardS.
      - exact HcardSP. }
    lia.
  Qed.

  (* la-elements always match a dummy node: m_aug a is some inr k. *)
  Lemma la_assigned_to_dummy : forall (sub la : Ensemble A) w (m_aug : A -> sum A A),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    forall a, In A la a ->
    exists k, In A la k /\ m_aug a = inr k.
  Proof.
    intros sub la w m_aug Hla Habove Hm_match a Ha.
    assert (Hincl_la : Included A la sub)
      by exact (@largest_antichain_included A R sub la w Hla).
    assert (Ha_sub : In A sub a) by exact (Hincl_la a Ha).
    assert (Hm_in := Hm_match a Ha_sub).
    destruct (m_aug a) as [y | k] eqn:Hma.
    - destruct Hm_in as [Hy_sub [HRya Hyne]].
      exfalso.
      assert (Hmin : forall z, In A sub z -> R z a -> z = a).
      { apply (min_elements_eq_la R sub la w Hla Habove a Ha_sub). exact Ha. }
      exact (Hyne (Hmin y Hy_sub HRya)).
    - exact (ex_intro _ k (conj Hm_in eq_refl)).
  Qed.

  (* Any sub-element matched to a dummy node is itself in la
     (by surjectivity of the la-restriction of m_aug). *)
  Lemma dummy_target_in_la : forall (sub la : Ensemble A) w (m_aug : A -> sum A A),
    cardinal A la w ->
    Included A la sub ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    (forall x y, In A sub x -> In A sub y -> m_aug x = m_aug y -> x = y) ->
    (forall a, In A la a -> exists k, In A la k /\ m_aug a = inr k) ->
    forall z, In A sub z ->
    (exists d, m_aug z = inr d) ->
    In A la z.
  Proof.
    intros sub la w m_aug Hcard_la Hincl_la Hm_match Hm_inj Hla_dummy z Hz [d Hm_z].
    assert (Hd_la : In A la d).
    { assert (Hm_in := Hm_match z Hz). rewrite Hm_z in Hm_in. exact Hm_in. }
    (* π : la → la injective, hence surjective; so d is in the range and z = π⁻¹(d) ∈ la. *)
    set (π := fun a => epsilon (inhabits d) (fun k => In A la k /\ m_aug a = inr k)).
    assert (Hpi_spec : forall a, In A la a -> In A la (π a) /\ m_aug a = inr (π a)).
    { intro a. intro Ha.
      destruct (Hla_dummy a Ha) as [k [Hk Hmk]].
      unfold π. apply epsilon_spec. exact (ex_intro _ k (conj Hk Hmk)). }
    assert (Hpi_inj : forall a1 a2, In A la a1 -> In A la a2 -> π a1 = π a2 -> a1 = a2).
    { intros a1 a2 Ha1 Ha2 Heq_pi.
      apply (Hm_inj a1 a2 (Hincl_la a1 Ha1) (Hincl_la a2 Ha2)).
      rewrite (proj2 (Hpi_spec a1 Ha1)), (proj2 (Hpi_spec a2 Ha2)). congruence. }
    assert (Hpi_surj_d : exists a, In A la a /\ π a = d).
    {
      destruct (classic (exists a, In A la a /\ π a = d)) as [Hex | Hnex].
      - exact Hex.
      - exfalso.
        assert (Hnota : forall a, In A la a -> π a <> d).
        { intros a Ha Heq. apply Hnex. exact (ex_intro _ a (conj Ha Heq)). }
        destruct w as [| w'].
        { inversion Hcard_la. subst. inversion Hd_la. }
        assert (Hcard_la_minus : cardinal A (Subtract A la d) w').
        { exact (card_soustr_1 A la (Datatypes.S w') Hcard_la d Hd_la). }
        assert (Htot' : forall a, In A la a ->
            exists b, In A (Subtract A la d) b /\ π a = b).
        { intros a Ha. exists (π a). split.
          - constructor. exact (proj1 (Hpi_spec a Ha)). intro Heq. inversion Heq. exact (Hnota a Ha (eq_sym H0)).
          - reflexivity. }
        assert (Hinj' : forall a1 a2 b, In A la a1 -> In A la a2 ->
            In A (Subtract A la d) b -> π a1 = b -> π a2 = b -> a1 = a2).
        { intros a1 a2 b Ha1 Ha2 _ H1 H2. exact (Hpi_inj a1 a2 Ha1 Ha2 (eq_trans H1 (eq_sym H2))). }
        assert (Hle : Datatypes.S w' <= w').
        { exact (InjectionPrinciple.cardinal_injection_principle_poly
                   A A la (Subtract A la d) (fun a b => π a = b)
                   (Datatypes.S w') w' Htot' Hinj' Hcard_la Hcard_la_minus). }
        lia.
    }
    destruct Hpi_surj_d as [a [Ha Hpi_d]].
    assert (Heq_za : z = a).
    { apply (Hm_inj z a Hz (Hincl_la a Ha)).
      rewrite Hm_z, (proj2 (Hpi_spec a Ha)). congruence. }
    subst z. exact Ha.
  Qed.

  (* Iterating the matching from any sub-element reaches la within nx steps,
     and the final element relates to the start via R. *)
  Lemma chain_terminates : forall (sub la : Ensemble A) w (m_aug : A -> sum A A) nx,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    cardinal A sub nx ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    (forall x y, In A sub x -> In A sub y -> m_aug x = m_aug y -> x = y) ->
    (forall a, In A la a -> exists k, In A la k /\ m_aug a = inr k) ->
    forall x, In A sub x ->
    In A la (chain_root_aux m_aug nx x) /\ R (chain_root_aux m_aug nx x) x.
  Proof.
    intros sub la w m_aug nx Hla Habove Hcard_sub Hstep_R Hm_inj Hla_dummy.
    assert (Hincl_la : Included A la sub)
      by exact (@largest_antichain_included A R sub la w Hla).
    assert (Hsteps_in_sub : forall k x, In A sub x -> k <= nx ->
        In A sub (chain_root_aux m_aug k x)).
    {
      intro k. induction k as [| k' IHk].
      - intros x Hx _. simpl. exact Hx.
      - intros x Hx Hle. simpl.
        destruct (m_aug x) as [y | d] eqn:Hx_case.
        + assert (Hm_in := Hstep_R x Hx). rewrite Hx_case in Hm_in.
          exact (IHk y (proj1 Hm_in) (Nat_le_of_succ_le _ _ Hle)).
        + exact Hx.
    }
    assert (Hdummy_means_la : forall z, In A sub z -> (exists d, m_aug z = inr d) -> In A la z)
      by exact (dummy_target_in_la sub la w m_aug
                  (@largest_antichain_cardinality A R sub la w Hla)
                  Hincl_la Hstep_R Hm_inj Hla_dummy).
    set (step := fun z => match m_aug z with inl y => y | inr _ => z end).
    assert (Hiter_eq2 : forall k x0, In A sub x0 ->
        chain_root_aux m_aug k x0 = Nat.iter k step x0).
    {
      intro k. induction k as [| k' IHk].
      - intros x0 _. reflexivity.
      - intros x0 Hx0. simpl chain_root_aux.
        rewrite Nat.iter_succ_r.
        destruct (m_aug x0) as [y | d] eqn:Hx0_m.
        + assert (Hy_sub : In A sub y).
          { assert (Hm_in := Hstep_R x0 Hx0). rewrite Hx0_m in Hm_in. exact (proj1 Hm_in). }
          assert (Hstep_x0 : step x0 = y) by (unfold step; rewrite Hx0_m; reflexivity).
          rewrite Hstep_x0. exact (IHk y Hy_sub).
        + assert (Hstep_x0 : step x0 = x0) by (unfold step; rewrite Hx0_m; reflexivity).
          rewrite Hstep_x0. symmetry.
          clear IHk. induction k' as [| k'' IHk''].
          * reflexivity.
          * rewrite Nat.iter_succ_r, Hstep_x0. exact IHk''.
    }
    intro x. intro Hx.
    assert (Hiter_sub : forall k, k <= nx -> In A sub (Nat.iter k step x)).
    {
      intro k. rewrite <- Hiter_eq2 by exact Hx.
      exact (Hsteps_in_sub k x Hx).
    }

    rewrite (Hiter_eq2 nx x Hx).

    assert (Hfixed : forall z, match m_aug z with inr _ => True | inl _ => False end ->
        step z = z).
    { intros z Hz. unfold step. destruct (m_aug z) as [y | d].
      - exact (False_rect _ Hz).
      - reflexivity. }

    assert (Hstable : forall k j, k <= nx ->
        match m_aug (Nat.iter k step x) with inr _ => True | inl _ => False end ->
        Nat.iter (k + j) step x = Nat.iter k step x).
    {
      intros k j Hk_le Hstop.
      induction j as [| j' IHj].
      - rewrite Nat.add_0_r. reflexivity.
      - rewrite Nat.add_succ_r.
        rewrite Nat.iter_succ.
        rewrite IHj.
        exact (Hfixed (Nat.iter k step x) Hstop).
    }

    assert (Hdecrease : forall k, k < nx ->
        match m_aug (Nat.iter k step x) with
        | inl _ => R (Nat.iter (k+1) step x) (Nat.iter k step x) /\
                   Nat.iter (k+1) step x <> Nat.iter k step x
        | inr _ => True
        end).
    {
      intros k Hk.
      assert (Hzk_sub : In A sub (Nat.iter k step x)) by exact (Hiter_sub k (Nat.lt_le_incl _ _ Hk)).
      assert (Hstep_info := Hstep_R (Nat.iter k step x) Hzk_sub).
      replace (k + 1) with (Datatypes.S k) by lia.
      rewrite Nat.iter_succ.
      destruct (m_aug (Nat.iter k step x)) as [y | d] eqn:Hm_zk.
      - destruct Hstep_info as [Hy_sub [HRyx Hne]].
        assert (Hstep_val : step (Nat.iter k step x) = y).
        { unfold step at 1. rewrite Hm_zk. reflexivity. }
        rewrite Hstep_val. split; assumption.
      - exact I.
    }

    destruct (classic (exists k, k <= nx /\ match m_aug (Nat.iter k step x) with inr _ => True | inl _ => False end)) as [Hstop | Hnostop].
    {
      destruct Hstop as [k0 [Hk0_le Hstop]].
      assert (Hk0_plus : nx = k0 + (nx - k0)) by lia.
      rewrite Hk0_plus.
      rewrite (Hstable k0 (nx - k0) Hk0_le Hstop).
      assert (Hk0_sub : In A sub (Nat.iter k0 step x)) by exact (Hiter_sub k0 Hk0_le).
      assert (Hm_k0 := Hstep_R (Nat.iter k0 step x) Hk0_sub).
      destruct (m_aug (Nat.iter k0 step x)) as [y | a] eqn:Heq_k0.
      - exact (False_rect _ Hstop).
      - split.
        { exact (Hdummy_means_la (Nat.iter k0 step x) Hk0_sub (ex_intro _ a Heq_k0)). }
        assert (Hlocal : forall j m, j + m <= nx ->
            R (Nat.iter (j + m) step x) (Nat.iter j step x)).
        {
          intros j m. induction m as [| m' IHm].
          - intros _. rewrite Nat.add_0_r. apply poset_refl.
          - intro Hle.
            assert (Hjm'_le : j + m' <= nx) by lia.
            assert (Hiter_sub' : In A sub (Nat.iter (j + m') step x))
              by exact (Hiter_sub (j + m') Hjm'_le).
            assert (Hstep_info' := Hstep_R (Nat.iter (j + m') step x) Hiter_sub').
            replace (j + Datatypes.S m') with (Datatypes.S (j + m')) by lia.
            rewrite Nat.iter_succ.
            destruct (m_aug (Nat.iter (j + m') step x)) as [y' | d'] eqn:Hm'.
            + assert (Hstep_val' : step (Nat.iter (j + m') step x) = y').
              { unfold step at 1. rewrite Hm'. reflexivity. }
              rewrite Hstep_val'.
              apply (poset_trans y' (Nat.iter (j + m') step x) (Nat.iter j step x)).
              * exact (proj1 (proj2 Hstep_info')).
              * exact (IHm Hjm'_le).
            + assert (Hstep_val' : step (Nat.iter (j + m') step x) = Nat.iter (j + m') step x).
              { unfold step at 1. rewrite Hm'. reflexivity. }
              rewrite Hstep_val'. exact (IHm Hjm'_le).
        }
        assert (Hdesc : forall k, k <= k0 -> R (Nat.iter k0 step x) (Nat.iter k step x)).
        {
          intros k Hk_le.
          replace k0 with (k + (k0 - k)) by lia.
          apply Hlocal. lia.
        }
        exact (Hdesc 0 (Nat.le_0_l k0)).
    }
    {
      exfalso.
      assert (Hallnotfixed : forall k, k <= nx ->
          match m_aug (Nat.iter k step x) with inl _ => True | inr _ => False end).
      {
        intros k Hk.
        destruct (classic (match m_aug (Nat.iter k step x) with inr _ => True | inl _ => False end)) as [Hfx | Hnfx].
        - exfalso. apply Hnostop. exists k. split. exact Hk. exact Hfx.
        - destruct (m_aug (Nat.iter k step x)) as [y | d].
          + exact I.
          + exfalso. apply Hnfx. exact I.
      }
      assert (Hdistinct_succ : forall k, k < nx ->
          Nat.iter (k+1) step x <> Nat.iter k step x).
      {
        intros k Hk.
        assert (Hfixed_k := Hallnotfixed k (Nat.lt_le_incl _ _ Hk)).
        replace (k + 1) with (Datatypes.S k) by lia.
        rewrite Nat.iter_succ. unfold step at 1.
        assert (Hzk_sub : In A sub (Nat.iter k step x))
          by exact (Hiter_sub k (Nat.lt_le_incl _ _ Hk)).
        assert (Hstep_k := Hstep_R (Nat.iter k step x) Hzk_sub).
        destruct (m_aug (Nat.iter k step x)) as [y | d] eqn:Hm_k.
        - exact (proj2 (proj2 Hstep_k)).
        - exact (False_rect _ Hfixed_k).
      }
      assert (HRdesc_succ : forall k, k < nx ->
          R (Nat.iter (k+1) step x) (Nat.iter k step x) /\
          Nat.iter (k+1) step x <> Nat.iter k step x).
      {
        intros k Hk.
        assert (Hzk_sub : In A sub (Nat.iter k step x))
          by exact (Hiter_sub k (Nat.lt_le_incl _ _ Hk)).
        assert (Hstep_k := Hstep_R (Nat.iter k step x) Hzk_sub).
        replace (k + 1) with (Datatypes.S k) by lia.
        rewrite Nat.iter_succ. unfold step at 1.
        assert (Hfixed_k := Hallnotfixed k (Nat.lt_le_incl _ _ Hk)).
        destruct (m_aug (Nat.iter k step x)) as [y | d] eqn:Hm_k.
        - assert (Hstep_val : step (Nat.iter k step x) = y).
          { unfold step at 1. rewrite Hm_k. reflexivity. }
          rewrite Hstep_val. split.
          + exact (proj1 (proj2 Hstep_k)).
          + exact (proj2 (proj2 Hstep_k)).
        - exact (False_rect _ Hfixed_k).
      }
      assert (Hdistinct : forall i j, i < j -> j <= nx ->
          Nat.iter i step x <> Nat.iter j step x).
      {
        intros i j Hi_lt_j Hj_le.
        intro Heq.
        revert i Hi_lt_j Hj_le Heq.
        induction j as [| j'].
        - intros i Hi_lt _. lia.
        - intros i Hi_lt_Sj' HSj'_le Heq.
          destruct (Nat.eq_dec i j') as [Heq_ij | Hne_ij].
          + subst j'. rewrite <- Nat.add_1_r in Heq.
            exact (Hdistinct_succ i HSj'_le (eq_sym Heq)).
          + assert (Hi_lt_j' : i < j') by lia.
            assert (Hj'_le : j' <= nx) by lia.
            assert (Hne_succ : Nat.iter (j'+1) step x <> Nat.iter j' step x)
              by exact (Hdistinct_succ j' HSj'_le).
            rewrite <- Nat.add_1_r in Heq.
            assert (HR_down : forall a b, a < b -> b <= nx ->
                R (Nat.iter b step x) (Nat.iter a step x)).
            { intros a b Hab Hb_le.
              induction b as [| b'].
              - lia.
              - destruct (Nat.eq_dec a b') as [Hab' | Hab'].
                + subst b'. rewrite <- Nat.add_1_r. exact (proj1 (HRdesc_succ a Hb_le)).
                + assert (Ha_lt_b' : a < b') by lia.
                  assert (Hb'_le : b' <= nx) by lia.
                  apply (poset_trans (Nat.iter (S b') step x) (Nat.iter b' step x) (Nat.iter a step x)).
                  * rewrite <- Nat.add_1_r. exact (proj1 (HRdesc_succ b' Hb_le)).
                  * exact (IHb' Ha_lt_b' Hb'_le). }
            assert (Hi_lt_j1 : i < j' + 1) by lia.
            assert (Hj1_le : j' + 1 <= nx) by lia.
            assert (HR_j1_i : R (Nat.iter (j'+1) step x) (Nat.iter i step x))
              by exact (HR_down i (j'+1) Hi_lt_j1 Hj1_le).
            assert (HR_i1_i : R (Nat.iter (i+1) step x) (Nat.iter i step x))
              by exact (proj1 (HRdesc_succ i (Nat.lt_le_trans _ _ _ Hi_lt_Sj' HSj'_le))).
            assert (Hj1_gt_i1 : i + 1 < j' + 1) by lia.
            assert (HR_j1_i1 : R (Nat.iter (j'+1) step x) (Nat.iter (i+1) step x))
              by exact (HR_down (i+1) (j'+1) Hj1_gt_i1 Hj1_le).
            rewrite <- Heq in HR_j1_i1.
            assert (Heq_i_i1 : Nat.iter i step x = Nat.iter (i+1) step x)
              by exact (poset_antisym _ _ HR_j1_i1 HR_i1_i).
            exact (Hdistinct_succ i
              (Nat.lt_le_trans _ _ _ Hi_lt_Sj' HSj'_le)
              (eq_sym Heq_i_i1)).
      }
      assert (HcardRange : cardinal nat (fun k => k <= nx) (S nx)).
      { clear. induction nx as [| nx' IH].
        - apply (cardinal_extensional_poly nat (Add nat (Empty_set nat) 0)).
          + intro k. split.
            * intro Hk. inversion Hk as [z' Hz' | z' Hz']; subst.
              -- contradiction.
              -- inversion Hz'; subst. apply Nat.le_refl.
            * intro Hk. destruct k as [| k'].
              -- apply Union_intror. apply In_singleton.
              -- inversion Hk.
          + apply card_add. apply card_empty. intro H. inversion H.
        - apply (cardinal_extensional_poly nat (Add nat (fun k => k <= nx') (S nx'))).
          + intro k. split.
            * intro Hk. inversion Hk as [z Hz | z Hz]; subst.
              -- exact (le_S _ _ Hz).
              -- inversion Hz; subst. apply Nat.le_refl.
            * intro Hk. inversion Hk; subst.
              -- apply Union_intror. apply In_singleton.
              -- apply Union_introl. assumption.
          + apply card_add. exact IH.
            intro Hcontra.
            exact (Nat.lt_irrefl nx' (Nat.lt_le_trans _ _ _ (Nat.lt_succ_diag_r nx') Hcontra)). }
      assert (Hle : S nx <= nx).
      { apply (InjectionPrinciple.cardinal_injection_principle_poly
                 nat A (fun k => k <= nx) sub
                 (fun k y => y = Nat.iter k step x) (S nx) nx).
        - intros k Hk. exists (Nat.iter k step x). split.
          + exact (Hiter_sub k Hk).
          + reflexivity.
        - intros i j y Hi Hj Hy_sub Heqi Heqj. subst.
          destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
          + exact (False_rect _ (Hdistinct i j Hij Hj Heqj)).
          + exact Hij.
          + exact (False_rect _ (Hdistinct j i Hij Hi (eq_sym Heqj))).
        - exact HcardRange.
        - exact Hcard_sub. }
      exact (Nat.lt_irrefl nx (Nat.lt_le_trans _ _ _ (Nat.lt_succ_diag_r nx) Hle)).
    }
  Qed.

  (* Two sub-elements assigned to the same la-target are R-comparable. *)
  Lemma fiber_chain : forall (sub la : Ensemble A) w (m_aug : A -> sum A A) nx,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    cardinal A sub nx ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    (forall x y, In A sub x -> In A sub y -> m_aug x = m_aug y -> x = y) ->
    (forall a, In A la a -> exists k, In A la k /\ m_aug a = inr k) ->
    (forall a, In A la a -> chain_root_aux m_aug nx a = a) ->
    (forall x, In A sub x ->
       In A la (chain_root_aux m_aug nx x) /\ R (chain_root_aux m_aug nx x) x) ->
    forall a, In A la a ->
    IsChain R (fun x => In A sub x /\ chain_root_aux m_aug nx x = a).
  Proof.
    intros sub la w m_aug nx Hla Habove Hcard_sub Hstep_R Hm_inj Hla_dummy Hf_la Hf_assign a Ha.
    assert (Hincl_la : Included A la sub)
      by exact (@largest_antichain_included A R sub la w Hla).
    set (step := fun z => match m_aug z with inl y => y | inr _ => z end).
    assert (Hiter_eq2 : forall k x0, In A sub x0 ->
        chain_root_aux m_aug k x0 = Nat.iter k step x0).
    {
      intro k. induction k as [| k' IHk].
      - intros x0 _. reflexivity.
      - intros x0 Hx0. simpl chain_root_aux.
        rewrite Nat.iter_succ_r.
        destruct (m_aug x0) as [y | d] eqn:Hx0_m.
        + assert (Hy_sub : In A sub y).
          { assert (Hm_in := Hstep_R x0 Hx0). rewrite Hx0_m in Hm_in. exact (proj1 Hm_in). }
          assert (Hstep_x0 : step x0 = y) by (unfold step; rewrite Hx0_m; reflexivity).
          rewrite Hstep_x0. exact (IHk y Hy_sub).
        + assert (Hstep_x0 : step x0 = x0) by (unfold step; rewrite Hx0_m; reflexivity).
          rewrite Hstep_x0. symmetry.
          clear IHk. induction k' as [| k'' IHk''].
          * reflexivity.
          * rewrite Nat.iter_succ_r, Hstep_x0. exact IHk''.
    }
    assert (Hdummy_means_la : forall z, In A sub z -> (exists d, m_aug z = inr d) -> In A la z)
      by exact (dummy_target_in_la sub la w m_aug
                  (@largest_antichain_cardinality A R sub la w Hla)
                  Hincl_la Hstep_R Hm_inj Hla_dummy).
    set (f := fun x => chain_root_aux m_aug nx x).
    split.
    - apply Inhabited_intro with a.
      split. exact (Hincl_la a Ha).
      unfold f. exact (Hf_la a Ha).
    - intros x y [Hx_sub Hx_f] [Hy_sub Hy_f].
      unfold f in Hx_f, Hy_f.
      set (depth := fun z => depth_aux m_aug nx z).

      assert (Hdepth_inr : forall k z,
          match m_aug z with inr _ => True | inl _ => False end ->
          depth_aux m_aug k z = 0).
      { intros k. induction k as [| k' IHk].
        - intros z _. reflexivity.
        - intros z Hz. simpl. destruct (m_aug z) as [z' | d].
          + exact (False_rect _ Hz).
          + reflexivity. }

      assert (Hdepth_inl : forall k z z',
          m_aug z = inl z' ->
          depth_aux m_aug (S k) z = S (depth_aux m_aug k z')).
      { intros k z z' Hmz. simpl. rewrite Hmz. reflexivity. }

      assert (Hroot_depth : forall k z, In A sub z ->
          depth_aux m_aug k z <= k ->
          chain_root_aux m_aug (depth_aux m_aug k z) z = chain_root_aux m_aug k z).
      { intro k. induction k as [| k' IHk].
        - intros z _ _. reflexivity.
        - intros z Hz Hle. simpl.
          destruct (m_aug z) as [p | d] eqn:Hzm.
          + simpl depth_aux.
            assert (Hp_sub : In A sub p).
            { assert (Hm_in := Hstep_R z Hz). rewrite Hzm in Hm_in. exact (proj1 Hm_in). }
            assert (Hle' : depth_aux m_aug k' p <= k').
            { assert (Hdeq : depth_aux m_aug (S k') z = S (depth_aux m_aug k' p))
                by (simpl depth_aux; rewrite Hzm; reflexivity).
              lia. }
            transitivity (chain_root_aux m_aug (depth_aux m_aug k' p) p).
            * simpl chain_root_aux. rewrite Hzm. simpl. reflexivity.
            * exact (IHk p Hp_sub Hle').
          + simpl depth_aux. reflexivity. }

      assert (Hdepth_le_gen : forall k (z : A), depth_aux m_aug k z <= k).
      { intro k. induction k as [| k' IHk].
        - intro z. simpl. apply Nat.le_refl.
        - intro z. simpl. destruct (m_aug z) as [p | d].
          + exact (le_n_S _ _ (IHk p)).
          + apply Nat.le_0_l. }
      assert (Hdepth_le : forall z, In A sub z -> depth z <= nx).
      { intros z _. unfold depth. exact (Hdepth_le_gen nx z). }

      assert (Hstep_to_pred : forall z, In A sub z ->
          chain_root_aux m_aug nx z = a ->
          match m_aug z with
          | inl y => In A sub y /\ chain_root_aux m_aug nx y = a /\ R y z /\ y <> z
          | inr _ => In A la z
          end).
      { intros z Hz Hfz.
        assert (Hm_info := Hstep_R z Hz).
        destruct (m_aug z) as [p | d] eqn:Hzm.
        - simpl in Hm_info.
          split. exact (proj1 Hm_info).
          split.
          + destruct nx as [| nx'] eqn:Hnx.
            * inversion Hcard_sub. subst. inversion Hz.
            * simpl chain_root_aux in Hfz. rewrite Hzm in Hfz.
              assert (Hp_sub : In A sub p) by exact (proj1 Hm_info).
              rewrite (Hiter_eq2 (S nx') p Hp_sub).
              rewrite Nat.iter_succ.
              rewrite <- (Hiter_eq2 nx' p Hp_sub).
              rewrite Hfz.
              destruct (Hla_dummy a Ha) as [k_a [_ Hma]].
              unfold step. rewrite Hma. reflexivity.
          + exact (proj2 Hm_info).
        - exact (Hdummy_means_la z Hz (ex_intro _ d Hzm)). }

      assert (Hdepth_stable : forall k (z : A), In A sub z ->
          chain_root_aux m_aug k z = a ->
          depth_aux m_aug k z = depth_aux m_aug (S k) z).
      { intro k. induction k as [| k' IHk].
        - intros z Hz Hcr. simpl chain_root_aux in Hcr. subst z.
          destruct (Hla_dummy a Ha) as [ka [_ Hma]].
          simpl depth_aux. rewrite Hma. reflexivity.
        - intros z Hz Hcr. simpl chain_root_aux in Hcr.
          destruct (m_aug z) as [z' | d] eqn:Hzm.
          + assert (Hz'_sub : In A sub z').
            { assert (Hm_in := Hstep_R z Hz). rewrite Hzm in Hm_in. exact (proj1 Hm_in). }
            simpl depth_aux. rewrite Hzm.
            rewrite (IHk z' Hz'_sub Hcr). reflexivity.
          + simpl depth_aux. rewrite Hzm. reflexivity. }

      assert (Hfiber_depth_pred : forall z pz, In A sub z ->
          chain_root_aux m_aug nx z = a ->
          m_aug z = inl pz -> In A sub pz ->
          depth z = S (depth pz)).
      { intros z pz Hz Hcrz Hmz Hpz_sub.
        unfold depth.
        destruct nx as [| nx_prev] eqn:Hnx.
        - simpl chain_root_aux in Hcrz. subst z.
          destruct (Hla_dummy a Ha) as [ka [_ Hma]]. rewrite Hma in Hmz. discriminate Hmz.
        - assert (Hcrpz : chain_root_aux m_aug nx_prev pz = a).
          { simpl chain_root_aux in Hcrz. rewrite Hmz in Hcrz. exact Hcrz. }
          rewrite (Hdepth_inl nx_prev z pz Hmz).
          rewrite <- (Hdepth_stable nx_prev pz Hpz_sub Hcrpz).
          reflexivity. }

      assert (Hclaim : forall k v, In A sub v -> chain_root_aux m_aug nx v = a ->
          depth v = k ->
          forall u, In A sub u -> chain_root_aux m_aug nx u = a ->
          depth u <= k -> R u v).
      { intro k. induction k as [| k' IHk].
        - intros v Hv Hfv Hdv u Hu Hfu Hdu.
          assert (Hv_la : In A la v).
          { unfold depth in Hdv.
            destruct nx as [| nx'].
            - simpl in Hfv. subst v. exact Ha.
            - simpl in Hdv. destruct (m_aug v) as [z' | d] eqn:Hvm.
              + discriminate Hdv.
              + exact (Hdummy_means_la v Hv (ex_intro _ d Hvm)). }
          assert (Hveqa : v = a).
          { rewrite (Hiter_eq2 nx v Hv) in Hfv.
            assert (Hstep_v : step v = v).
            { unfold step. destruct (Hla_dummy v Hv_la) as [k_v [_ Hmv]]. rewrite Hmv. reflexivity. }
            assert (Hiter_v : forall j, Nat.iter j step v = v).
            { intro j. induction j. reflexivity. rewrite Nat.iter_succ. rewrite IHj. exact Hstep_v. }
            rewrite Hiter_v in Hfv. exact Hfv. }
          subst v.
          assert (Hu_la : In A la u).
          { unfold depth in Hdu.
            destruct nx as [| nx''].
            - simpl in Hfu. subst u. exact Ha.
            - simpl in Hdu. destruct (m_aug u) as [z'' | d''] eqn:Hum.
              + lia.
              + exact (Hdummy_means_la u Hu (ex_intro _ d'' Hum)). }
          assert (Hueqa : u = a).
          { rewrite (Hiter_eq2 nx u Hu) in Hfu.
            assert (Hstep_u : step u = u).
            { unfold step. destruct (Hla_dummy u Hu_la) as [k_u [_ Hmu]]. rewrite Hmu. reflexivity. }
            assert (Hiter_u : forall j, Nat.iter j step u = u).
            { intro j. induction j. reflexivity. rewrite Nat.iter_succ. rewrite IHj. exact Hstep_u. }
            rewrite Hiter_u in Hfu. exact Hfu. }
          subst u. apply poset_refl.
        - intros v Hv Hfv Hdv u Hu Hfu Hdu.
          assert (Hstep_v := Hstep_to_pred v Hv Hfv).
          assert (Hstep_u := Hstep_to_pred u Hu Hfu).
          unfold depth in Hdv.
          destruct (m_aug v) as [pv | dv] eqn:Hvm.
          + destruct Hstep_v as [Hpv_sub [Hpv_f [HRpv_v Hpvne]]].
            assert (Hd_pv : depth pv = k').
            { assert (Hfdp := Hfiber_depth_pred v pv Hv Hfv Hvm Hpv_sub).
              unfold depth in Hfdp. rewrite Hfdp in Hdv.
              injection Hdv as Hdv'. unfold depth. exact Hdv'. }
            unfold depth in Hdu.
            destruct (m_aug u) as [pu | du] eqn:Hum.
            * destruct Hstep_u as [Hpu_sub [Hpu_f [HRpu_u Hpune]]].
              assert (Hd_pu : depth pu <= k').
              { assert (Hfdpu := Hfiber_depth_pred u pu Hu Hfu Hum Hpu_sub).
                unfold depth in Hfdpu. rewrite Hfdpu in Hdu.
                unfold depth. lia. }
              destruct (Nat.eq_dec (depth_aux m_aug nx u) (S k')) as [Heq_du | Hne_du].
              -- assert (Hd_pu_eq : depth pu = k').
                 { assert (Hfdpu := Hfiber_depth_pred u pu Hu Hfu Hum Hpu_sub).
                   unfold depth in Hfdpu.
                   assert (Heq_pu : S (depth_aux m_aug nx pu) = S k') by congruence.
                   injection Heq_pu as Heq'. unfold depth. exact Heq'. }
                 assert (HR_pu_pv : R pu pv) by exact (IHk pv Hpv_sub Hpv_f Hd_pv pu Hpu_sub Hpu_f Hd_pu).
                 assert (HR_pv_pu : R pv pu).
                 { apply (IHk pu Hpu_sub Hpu_f Hd_pu_eq pv Hpv_sub Hpv_f).
                   rewrite Hd_pv. apply Nat.le_refl. }
                 assert (Hpu_eq_pv : pu = pv) by exact (poset_antisym pu pv HR_pu_pv HR_pv_pu).
                 assert (Hm_eq : m_aug u = m_aug v) by (rewrite Hum, Hvm, Hpu_eq_pv; reflexivity).
                 assert (Huv : u = v) by exact (Hm_inj u v Hu Hv Hm_eq).
                 subst v. apply poset_refl.
              -- assert (Hdu_le_k' : depth_aux m_aug nx u <= k').
                 { lia. }
                 assert (HR_u_pv : R u pv) by exact (IHk pv Hpv_sub Hpv_f Hd_pv u Hu Hfu Hdu_le_k').
                 exact (poset_trans u pv v HR_u_pv HRpv_v).
            * assert (Hu_la : In A la u) by exact (Hdummy_means_la u Hu (ex_intro _ du Hum)).
              assert (Hueqa : u = a).
              { rewrite (Hiter_eq2 nx u Hu) in Hfu.
                assert (Hstep_u' : step u = u).
                { unfold step. destruct (Hla_dummy u Hu_la) as [k_u [_ Hmu]]. rewrite Hmu. reflexivity. }
                assert (Hiter_u : forall j, Nat.iter j step u = u).
                { intro j. induction j. reflexivity. rewrite Nat.iter_succ. rewrite IHj. exact Hstep_u'. }
                rewrite Hiter_u in Hfu. exact Hfu. }
              subst u.
              assert (Hrfv := proj2 (Hf_assign v Hv)).
              unfold f in Hrfv. rewrite Hfv in Hrfv. exact Hrfv.
          + assert (Hv_inr : match m_aug v with inr _ => True | inl _ => False end)
              by (rewrite Hvm; exact I).
            rewrite (Hdepth_inr nx v Hv_inr) in Hdv. discriminate Hdv.
      }

      destruct (classic (depth x <= depth y)) as [Hdxy | Hlt].
      + left. exact (Hclaim (depth y) y Hy_sub Hy_f eq_refl x Hx_sub Hx_f Hdxy).
      + right. assert (Hdxy : depth y < depth x) by lia.
        exact (Hclaim (depth x) x Hx_sub Hx_f eq_refl y Hy_sub Hy_f (Nat.lt_le_incl _ _ Hdxy)).
  Qed.

  Lemma chain_assignment_kernel : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Habove HfinSub.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [HinhLa HincompLa].
    destruct (finite_cardinal A sub HfinSub) as [nx Hcard_sub].

    set (nbrs_aug := fun (x : A) (z : sum A A) =>
      match z with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end).

    set (Y := fun (z : sum A A) =>
      match z with
      | inl y => In A sub y
      | inr a => In A la a
      end).

    assert (HfinY : Finite (sum A A) Y).
    {
      pose proof (Y_cardinal sub la nx w Hcard_sub Hcard_la) as HcardY.
      exact (cardinal_finite (sum A A) Y (nx + w) HcardY).
    }

    assert (HinhR : inhabited (sum A A)).
    { destruct HinhLa as [a Ha]. exact (inhabits (inr a)). }

    assert (Hnbrs_Y : forall x z, In A sub x -> In (sum A A) (nbrs_aug x) z -> In (sum A A) Y z).
    { intros x z Hx Hz. unfold nbrs_aug in Hz. unfold Y.
      destruct z as [y | a].
      - exact (proj1 Hz).
      - exact Hz. }

    assert (Hhall : HallCondition sub nbrs_aug)
      by exact (hall_condition_holds sub la w nbrs_aug Hla' Habove HfinSub Hcard_la
                  (fun x z => iff_refl _)).

    destruct (hall_marriage_theorem sub Y nx nbrs_aug Hcard_sub HfinY HinhR
                (fun x z Hx Hz => Hnbrs_Y x z Hx Hz) Hhall)
      as [m_aug [Hm_Y [Hm_nbrs Hm_inj]]].

    assert (Hm_match : forall x, In A sub x ->
        match m_aug x with
        | inl y => In A sub y /\ R y x /\ y <> x
        | inr a => In A la a
        end).
    { intros x Hx. exact (Hm_nbrs x Hx). }
    pose proof (la_assigned_to_dummy sub la w m_aug Hla' Habove Hm_match) as Hla_dummy.

    pose proof (dummy_target_in_la sub la w m_aug Hcard_la Hincl_la Hm_match Hm_inj Hla_dummy)
      as Hdummy_means_la.

    set (f := fun x => chain_root_aux m_aug nx x).

    assert (Hf_la : forall a, In A la a -> chain_root_aux m_aug nx a = a).
    {
      intros a Ha.
      destruct (Hla_dummy a Ha) as [k [_ Hma]].
      destruct nx as [| nx'].
      - simpl. reflexivity.
      - simpl. rewrite Hma. reflexivity.
    }

    assert (Hf_assign : forall x, In A sub x -> In A la (f x) /\ R (f x) x).
    {
      pose proof (chain_terminates sub la w m_aug nx Hla' Habove Hcard_sub
                    Hm_match Hm_inj Hla_dummy) as Hct.
      intros x Hx. unfold f. exact (Hct x Hx).
    }

    pose proof (fiber_chain sub la w m_aug nx Hla' Habove Hcard_sub
                  Hm_match Hm_inj Hla_dummy Hf_la Hf_assign) as Hf_chain.

    exact (ex_intro _ f (conj Hf_assign Hf_chain)).
  Qed.

End HallKernel.

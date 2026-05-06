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

    (* The augmented right type is (sum A A), left = inl y means predecessor y in sub,
       right = inr a means assigned to la-element a (dummy). *)
    set (nbrs_aug := fun (x : A) (z : sum A A) =>
      match z with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end).

    (* Y = {inl y | y ∈ sub} ∪ {inr a | a ∈ la} *)
    set (Y := fun (z : sum A A) =>
      match z with
      | inl y => In A sub y
      | inr a => In A la a
      end).

    (* Y is finite *)
    assert (HfinY : Finite (sum A A) Y).
    {
      (* Helper: lift cardinal through inl/inr injections *)
      assert (HcardInl : cardinal (sum A A)
          (fun z => match z with inl y => In A sub y | inr _ => False end) nx)
        by exact (inl_image_cardinal sub nx Hcard_sub).
      assert (HcardInr : cardinal (sum A A)
          (fun z => match z with inl _ => False | inr a => In A la a end) w)
        by exact (inr_image_cardinal la w Hcard_la).
      pose proof (Y_cardinal sub la nx w Hcard_sub Hcard_la) as HcardY.
      exact (cardinal_finite (sum A A) Y (nx + w) HcardY).
    }

    (* (sum A A) is inhabited *)
    assert (HinhR : inhabited (sum A A)).
    { destruct HinhLa as [a Ha]. exact (inhabits (inr a)). }

    (* nbrs_aug x ⊆ Y for x ∈ sub *)
    assert (Hnbrs_Y : forall x z, In A sub x -> In (sum A A) (nbrs_aug x) z -> In (sum A A) Y z).
    { intros x z Hx Hz. unfold nbrs_aug in Hz. unfold Y.
      destruct z as [y | a].
      - exact (proj1 Hz).
      - exact Hz. }

    (* Hall's condition *)
    assert (Hhall : HallCondition sub nbrs_aug).
    {
      intros S ns nn HinclS HcardS HcardNS.
      (* We need ns <= nn *)
      (* set_neighbors nbrs_aug S = {inl y | StrictPred sub S y} ∪ {inr a | a ∈ la} when S non-empty *)
      (* and = {inr a | a ∈ la} when S empty *)
      destruct ns as [| ns'].
      { lia. }
      assert (HinhS : Inhabited A S).
      { inversion HcardS as [| S0 m Hm x Hx_notin]. subst.
        apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
      (* StrictPred sub S is finite *)
      assert (HfinSP : Finite A (StrictPred sub S)).
      { apply (Finite_downward_closed A sub HfinSub). intros y Hy. exact (proj1 Hy). }
      destruct (finite_cardinal A (StrictPred sub S) HfinSP) as [nP HcardSP].
      (* set_neighbors nbrs_aug S = inl-image(StrictPred) ∪ inr-image(la) *)
      assert (Hset_eq : set_neighbors nbrs_aug S =
          Union (sum A A)
            (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
            (fun z => match z with inl _ => False | inr a => In A la a end)).
      { apply Extensionality_Ensembles. intro z. split.
        - intros [x [Hx Hz]]. unfold nbrs_aug in Hz. destruct z as [y | a].
          + apply Union_introl. unfold HallDefect.StrictPred.
            exact (conj (proj1 Hz) (ex_intro _ x (conj Hx (conj (proj1 (proj2 Hz)) (fun h => proj2 (proj2 Hz) (eq_sym h)))))).
          + apply Union_intror. exact Hz.
        - intro Hz.
          inversion Hz as [z' Hz' | z' Hz']; subst.
          + destruct z as [y | a]. 2: exact (False_rect _ Hz').
            simpl in Hz'. unfold HallDefect.StrictPred in Hz'.
            destruct Hz' as [Hy [x [Hx [HRyx Hne]]]].
            exists x. split. exact Hx. unfold nbrs_aug.
            exact (conj Hy (conj HRyx (fun h => Hne (eq_sym h)))).
          + destruct z as [y | a]. exact (False_rect _ Hz').
            simpl in Hz'.
            destruct HinhS as [x0 Hx0].
            exists x0. split. exact Hx0. unfold nbrs_aug. exact Hz'. }
      (* Cardinal of inl-image(StrictPred) *)
      assert (HcardInlP : cardinal (sum A A)
          (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end) nP)
        by exact (inl_image_cardinal (StrictPred sub S) nP HcardSP).
      (* Cardinal of inr-image(la) *)
      assert (HcardInrLa : cardinal (sum A A)
          (fun z => match z with inl _ => False | inr a => In A la a end) w)
        by exact (inr_image_cardinal la w Hcard_la).
      (* Cardinal of the union *)
      assert (HcardUnion : cardinal (sum A A)
          (Union (sum A A)
            (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
            (fun z => match z with inl _ => False | inr a => In A la a end))
          (nP + w)).
      { apply cardinal_disjoint_union_gen.
        - intros z Hl Hr. destruct z. exact Hr. exact Hl.
        - exact HcardInlP.
        - exact HcardInrLa. }
      (* nn = nP + w *)
      assert (Hnn_eq : nn = nP + w).
      { apply (cardinal_unicity (sum A A) (set_neighbors nbrs_aug S)).
        - exact HcardNS.
        - apply (cardinal_extensional_poly (sum A A)
              (Union (sum A A)
                (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
                (fun z => match z with inl _ => False | inr a => In A la a end))).
          + intro z. rewrite <- Hset_eq. tauto.
          + exact HcardUnion. }
      (* Apply dilworth_hall_defect_pred *)
      assert (Hns_le : Datatypes.S ns' <= nP + w).
      { apply (dilworth_hall_defect_pred R sub la w Hla' Habove S (Datatypes.S ns') nP).
        - exact HinclS.
        - exact HcardS.
        - exact HcardSP. }
      lia.
    }

    (* Apply Hall's marriage theorem *)
    destruct (hall_marriage_theorem sub Y nx nbrs_aug Hcard_sub HfinY HinhR
                (fun x z Hx Hz => Hnbrs_Y x z Hx Hz) Hhall)
      as [m_aug [Hm_Y [Hm_nbrs Hm_inj]]].

    (* For la-elements: m_aug returns inr *)
    assert (Hla_dummy : forall a, In A la a ->
        exists k, In A la k /\ m_aug a = inr k).
    {
      intros a Ha.
      assert (Ha_sub : In A sub a) by exact (Hincl_la a Ha).
      assert (Hm_in : In (sum A A) (nbrs_aug a) (m_aug a)) by exact (Hm_nbrs a Ha_sub).
      unfold nbrs_aug in Hm_in.
      destruct (m_aug a) as [y | k] eqn:Hma.
      - (* m_aug a = inl y: y ∈ sub, R y a, y ≠ a. But a ∈ la is minimal in sub. *)
        destruct Hm_in as [Hy_sub [HRya Hyne]].
        exfalso.
        assert (Hmin : forall z, In A sub z -> R z a -> z = a).
        { apply (min_elements_eq_la R sub la w Hla' Habove a Ha_sub). exact Ha. }
        exact (Hyne (Hmin y Hy_sub HRya)).
      - exact (ex_intro _ k (conj Hm_in eq_refl)).
    }

    (* Any sub-element matched to a dummy node must be in la *)
    assert (Hdummy_means_la : forall z, In A sub z -> (exists d, m_aug z = inr d) -> In A la z).
    {
      intros z Hz [d Hm_z].
      assert (Hd_la : In A la d).
      { assert (Hm_in : In (sum A A) (nbrs_aug z) (m_aug z)) by exact (Hm_nbrs z Hz).
        rewrite Hm_z in Hm_in. exact Hm_in. }
      (* π : la → la, a ↦ k where m_aug a = inr k, is a total injection.
         Since la is finite, π is surjective. So d = π(a) for some a ∈ la,
         and injectivity of m_aug gives z = a ∈ la. *)
      set (π := fun a => epsilon (inhabits d) (fun k => In A la k /\ m_aug a = inr k)).
      assert (Hpi_spec : forall a, In A la a -> In A la (π a) /\ m_aug a = inr (π a)).
      { intro a. intro Ha.
        destruct (Hla_dummy a Ha) as [k [Hk Hmk]].
        unfold π. apply epsilon_spec. exact (ex_intro _ k (conj Hk Hmk)). }
      assert (Hpi_inj : forall a1 a2, In A la a1 -> In A la a2 -> π a1 = π a2 -> a1 = a2).
      { intros a1 a2 Ha1 Ha2 Heq_pi.
        apply (Hm_inj a1 a2 (Hincl_la a1 Ha1) (Hincl_la a2 Ha2)).
        rewrite (proj2 (Hpi_spec a1 Ha1)), (proj2 (Hpi_spec a2 Ha2)). congruence. }
      (* Surjectivity: d ∈ la, so ∃ a ∈ la, π a = d *)
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
    }

    (* Define f via chain_root_aux *)
    set (f := fun x => chain_root_aux m_aug nx x).

    (* f(a) = a for a ∈ la *)
    assert (Hf_la : forall a, In A la a -> chain_root_aux m_aug nx a = a).
    {
      intros a Ha.
      destruct (Hla_dummy a Ha) as [k [_ Hma]].
      destruct nx as [| nx'].
      - simpl. reflexivity.
      - simpl. rewrite Hma. reflexivity.
    }

    (* Key: steps in sub *)
    assert (Hsteps_in_sub : forall k x, In A sub x -> k <= nx ->
        In A sub (chain_root_aux m_aug k x)).
    {
      intro k. induction k as [| k' IHk].
      - intros x Hx _. simpl. exact Hx.
      - intros x Hx Hle. simpl.
        destruct (m_aug x) as [y | d] eqn:Hx_case.
        + assert (Hm_in : In (sum A A) (nbrs_aug x) (m_aug x)) by exact (Hm_nbrs x Hx).
          rewrite Hx_case in Hm_in. unfold nbrs_aug in Hm_in.
          exact (IHk y (proj1 Hm_in) (Nat_le_of_succ_le _ _ Hle)).
        + exact Hx.
    }

    (* Key: step strictly reduces - if m_aug z = inl y then R y z and y ≠ z and y ∈ sub *)
    assert (Hstep_R : forall z, In A sub z ->
        match m_aug z with
        | inl y => In A sub y /\ R y z /\ y <> z
        | inr _ => True
        end).
    {
      intros z Hz.
      assert (Hm_in : In (sum A A) (nbrs_aug z) (m_aug z)) by exact (Hm_nbrs z Hz).
      unfold nbrs_aug in Hm_in.
      destruct (m_aug z) as [y | d].
      - exact Hm_in.
      - exact I.
    }

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
          { assert (Hm_in : In (sum A A) (nbrs_aug x0) (m_aug x0)) by exact (Hm_nbrs x0 Hx0).
            rewrite Hx0_m in Hm_in. exact (proj1 Hm_in). }
          assert (Hstep_x0 : step x0 = y) by (unfold step; rewrite Hx0_m; reflexivity).
          rewrite Hstep_x0. exact (IHk y Hy_sub).
        + assert (Hstep_x0 : step x0 = x0) by (unfold step; rewrite Hx0_m; reflexivity).
          rewrite Hstep_x0. symmetry.
          clear IHk. induction k' as [| k'' IHk''].
          * reflexivity.
          * rewrite Nat.iter_succ_r, Hstep_x0. exact IHk''.
    }

    (* Assignment: f(x) ∈ la and R(f(x)) x *)
    assert (Hf_assign : forall x, In A sub x -> In A la (f x) /\ R (f x) x).
    {
      intro x. intro Hx.
      unfold f.
      (* We prove the chain doesn't reach la in at most nx steps, or rather DOES reach la *)
      (* Strategy: if it doesn't reach la in nx steps, we get nx+1 distinct sub-elements *)

      (* The sequence is: z_k = Nat.iter k step x for k = 0, ..., nx *)
      (* z_0 = x, z_{k+1} = step z_k *)
      (* As long as m_aug z_k = inl _, z_{k+1} ≠ z_k and R z_{k+1} z_k *)
      (* All z_k ∈ sub (by Hsteps_in_sub and Hiter_eq2) *)

      assert (Hiter_sub : forall k, k <= nx -> In A sub (Nat.iter k step x)).
      {
        intro k. rewrite <- Hiter_eq2 by exact Hx.
        exact (Hsteps_in_sub k x Hx).
      }

      (* The final element chain_root_aux nx x = Nat.iter nx step x *)
      rewrite (Hiter_eq2 nx x Hx).

      (* Case: does the chain reach la? *)
      (* The sequence must reach a fixed point (an inr element) within nx steps,
         otherwise we have nx+1 distinct elements in sub (of size nx), contradiction. *)

      (* Define: "hits_la k" := m_aug (Nat.iter k step x) = inr _ *)
      (* If hits_la k for some k ≤ nx-1, then Nat.iter k step x ∈ la,
         and the sequence stabilizes: Nat.iter (k+j) step x = Nat.iter k step x.
         So Nat.iter nx step x = Nat.iter k step x ∈ la.
         And R(Nat.iter nx step x)(x) by transitivity of the descending chain. *)

      (* First establish: if m_aug z = inr _, then step z = z *)
      assert (Hfixed : forall z, match m_aug z with inr _ => True | inl _ => False end ->
          step z = z).
      { intros z Hz. unfold step. destruct (m_aug z) as [y | d].
        - exact (False_rect _ Hz).
        - reflexivity. }

      (* Establish: if m_aug (iter k x) = inr _, then iter (k+j) x = iter k x *)
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

      (* Establish strict decrease: if m_aug (iter k x) = inl _, then
         R (iter (k+1) x) (iter k x) and iter (k+1) x ≠ iter k x *)
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

      (* Now: either ∃ k < nx with m_aug(iter k x) = inr _, or all k ≤ nx-1 have inl *)
      destruct (classic (exists k, k <= nx /\ match m_aug (Nat.iter k step x) with inr _ => True | inl _ => False end)) as [Hstop | Hnostop].
      {
        (* There's a first stopping point *)
        destruct Hstop as [k0 [Hk0_le Hstop]].
        (* iter nx x = iter k0 x (stable) *)
        assert (Hk0_plus : nx = k0 + (nx - k0)) by lia.
        rewrite Hk0_plus.
        rewrite (Hstable k0 (nx - k0) Hk0_le Hstop).
        (* iter k0 x ∈ la *)
        assert (Hk0_sub : In A sub (Nat.iter k0 step x)) by exact (Hiter_sub k0 Hk0_le).
        assert (Hm_k0 : In (sum A A) (nbrs_aug (Nat.iter k0 step x)) (m_aug (Nat.iter k0 step x)))
          by exact (Hm_nbrs (Nat.iter k0 step x) Hk0_sub).
        unfold nbrs_aug in Hm_k0.
        destruct (m_aug (Nat.iter k0 step x)) as [y | a] eqn:Heq_k0.
        - exact (False_rect _ Hstop).
        - split.
          { exact (Hdummy_means_la (Nat.iter k0 step x) Hk0_sub (ex_intro _ a Heq_k0)). }
          (* R (iter k0 x) x: by transitivity of the chain *)
          (* Prove: R (iter k x) (iter (k-1) x) for all k in the chain,
             then by transitivity R (iter k0 x) x = R (iter k0 x) (iter 0 x) *)
          (* Need to show: for all k ≤ k0, R (iter k0 x) (iter k x) *)
          (* Prove R (iter k0 x) (iter k x) for k ≤ k0, by showing
             R (iter (j+m) x) (iter j x) for all j+m ≤ nx, via induction on m *)
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
        (* No stopping point: all k ≤ nx have inl *)
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
        (* All z_0, ..., z_nx are in sub and are distinct *)
        (* z_{k+1} ≠ z_k for k < nx *)
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
        (* All z_0, ..., z_nx are distinct (by transitivity of distinctness + strictness) *)
        (* More precisely: they are STRICTLY DECREASING: R z_{k+1} z_k and ≠ *)
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
        (* z_i ≠ z_j for i < j ≤ nx: by the strict decrease *)
        assert (Hdistinct : forall i j, i < j -> j <= nx ->
            Nat.iter i step x <> Nat.iter j step x).
        {
          intros i j Hi_lt_j Hj_le.
          intro Heq.
          (* We have a strictly decreasing chain z_i > z_{i+1} > ... > z_j = z_i *)
          (* Contradiction: R z_j z_i and R z_i z_{i+1} → R z_j z_{i+1}, but z_j = z_i implies
             R z_i z_{i+1} and by antisymm would need z_i = z_{i+1}, contradicting Hdistinct_succ *)
          (* More carefully: R z_{i+1} z_i and ... and R z_j z_{j-1} *)
          (* So R z_j z_i (by transitivity) *)
          (* But z_j = z_i, so R z_i z_i ✓ (refl), hmm that doesn't help directly *)
          (* Better: R z_{i+1} z_i and R z_i = z_j. So R z_{i+1} z_i.
             And z_{i+1} ≠ z_i. But also step goes from z_i downward.
             So we need the full chain to get a contradiction. *)
          (* The injection {0,...,nx} → sub is not injective since z_i = z_j *)
          (* Actually the simplest: use that the map k ↦ z_k from {0,...,nx} to sub
             has z_i = z_j, so it's not injective on this (nx+1)-element domain.
             But we want an injection from a (nx+1)-element set to an nx-element set,
             which is impossible by InjectionPrinciple. *)
          (* Let's use: all z_k are in sub. Since |sub| = nx and there are nx+1 iterates,
             two must be equal. But the strict decrease implies all distinct. *)
          (* Strategy: prove z_i ≠ z_j for i < j by induction on j - i. *)
          (* Induction *)
          revert i Hi_lt_j Hj_le Heq.
          induction j as [| j'].
          - intros i Hi_lt _. lia.
          - intros i Hi_lt_Sj' HSj'_le Heq.
            destruct (Nat.eq_dec i j') as [Heq_ij | Hne_ij].
            + (* i = j': z_i = z_{i+1} contradicts Hdistinct_succ i *)
              subst j'. rewrite <- Nat.add_1_r in Heq.
              exact (Hdistinct_succ i HSj'_le (eq_sym Heq)).
            + (* i < j' *)
              assert (Hi_lt_j' : i < j') by lia.
              assert (Hj'_le : j' <= nx) by lia.
              (* z_{j'+1} ≠ z_{j'} (by Hdistinct_succ j') *)
              assert (Hne_succ : Nat.iter (j'+1) step x <> Nat.iter j' step x)
                by exact (Hdistinct_succ j' HSj'_le).
              rewrite <- Nat.add_1_r in Heq.
              (* z_i = z_{j'+1}, and we also have (by IH) z_i ≠ z_{j'} *)
              (* Hmm, we need to use IH on (i, j'): z_i ≠ z_{j'} *)
              (* Actually: R z_{j'+1} z_{j'} and z_{j'+1} = z_i *)
              (* and R z_{j'} z_{j'-1} ... R z_{i+1} z_i *)
              (* So R z_i z_{j'} (downward from j' to i, wait this is upward) *)
              (* z_{i} > z_{i+1} > ... > z_{j'} > z_{j'+1} = z_i *)
              (* So R z_{j'+1} z_{j'} and R z_{j'} ... z_{i+1} z_i *)
              (* By transitivity: R z_{j'+1} z_i = R z_i z_i *)
              (* This is fine (reflexivity). Hmm that doesn't give contradiction. *)
              (* But also R z_{i+1} z_i (from Hdistinct_succ i), and z_{i+1} ≠ z_i *)
              (* And by transitivity of the downward chain: R z_{j'+1} z_{i+1} *)
              (* z_{j'+1} = z_i, so R z_i z_{i+1} *)
              (* But R z_{i+1} z_i and R z_i z_{i+1} → z_i = z_{i+1} (antisymm) *)
              (* That contradicts Hdistinct_succ i! *)
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
              (* R z_{j'+1} z_i: since j'+1 > i *)
              assert (Hi_lt_j1 : i < j' + 1) by lia.
              assert (Hj1_le : j' + 1 <= nx) by lia.
              assert (HR_j1_i : R (Nat.iter (j'+1) step x) (Nat.iter i step x))
                by exact (HR_down i (j'+1) Hi_lt_j1 Hj1_le).
              (* R z_{i+1} z_i: since i+1 > i *)
              assert (HR_i1_i : R (Nat.iter (i+1) step x) (Nat.iter i step x))
                by exact (proj1 (HRdesc_succ i (Nat.lt_le_trans _ _ _ Hi_lt_Sj' HSj'_le))).
              (* z_{j'+1} = z_i, so R z_i z_i ✓ *)
              (* But R z_i z_{i+1}: z_{j'+1} = z_i, so R z_i z_{i+1} = R z_{j'+1} z_{i+1} *)
              (* z_{i+1}: from HR_down, R z_{j'+1} z_{i+1} since j'+1 > i+1 (since j' > i) *)
              assert (Hj1_gt_i1 : i + 1 < j' + 1) by lia.
              assert (HR_j1_i1 : R (Nat.iter (j'+1) step x) (Nat.iter (i+1) step x))
                by exact (HR_down (i+1) (j'+1) Hj1_gt_i1 Hj1_le).
              (* z_{j'+1} = z_i, so R z_i z_{i+1} *)
              rewrite <- Heq in HR_j1_i1.
              (* R z_{i+1} z_i and R z_i z_{i+1} → z_i = z_{i+1} by antisymm *)
              assert (Heq_i_i1 : Nat.iter i step x = Nat.iter (i+1) step x)
                by exact (poset_antisym _ _ HR_j1_i1 HR_i1_i).
              (* But z_i ≠ z_{i+1} *)
              exact (Hdistinct_succ i
                (Nat.lt_le_trans _ _ _ Hi_lt_Sj' HSj'_le)
                (eq_sym Heq_i_i1)).
        }
        (* Now: the map k ↦ iter k step x is injective from {0,...,nx} to sub *)
        (* But |{0,...,nx}| = nx+1 > nx = |sub|, contradiction *)
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
    }

    (* Chain property *)
    assert (Hf_chain : forall a, In A la a ->
        IsChain R (fun x => In A sub x /\ f x = a)).
    {
      intros a Ha.
      split.
      - apply Inhabited_intro with a.
        split. exact (Hincl_la a Ha).
        unfold f. exact (Hf_la a Ha).
      - intros x y [Hx_sub Hx_f] [Hy_sub Hy_f].
        unfold f in Hx_f, Hy_f.
        (* We need R x y or R y x *)
        (* Use depth-based argument *)
        (* depth(z) = depth_aux m_aug nx z *)
        set (depth := fun z => depth_aux m_aug nx z).

        (* Key properties of depth_aux *)
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

        (* chain_root_aux with depth fuel reaches la *)
        assert (Hroot_depth : forall k z, In A sub z ->
            depth_aux m_aug k z <= k ->
            chain_root_aux m_aug (depth_aux m_aug k z) z = chain_root_aux m_aug k z).
        { intro k. induction k as [| k' IHk].
          - intros z _ _. reflexivity.
          - intros z Hz Hle. simpl.
            destruct (m_aug z) as [p | d] eqn:Hzm.
            + simpl depth_aux.
              assert (Hp_sub : In A sub p).
              { assert (Hm_in : In (sum A A) (nbrs_aug z) (m_aug z)) by exact (Hm_nbrs z Hz).
                rewrite Hzm in Hm_in. exact (proj1 Hm_in). }
              assert (Hle' : depth_aux m_aug k' p <= k').
              { assert (Hdeq : depth_aux m_aug (S k') z = S (depth_aux m_aug k' p))
                  by (simpl depth_aux; rewrite Hzm; reflexivity).
                lia. }
              transitivity (chain_root_aux m_aug (depth_aux m_aug k' p) p).
              * simpl chain_root_aux. rewrite Hzm. simpl. reflexivity.
              * exact (IHk p Hp_sub Hle').
            + simpl depth_aux. reflexivity. }

        (* depth ≤ nx *)
        assert (Hdepth_le_gen : forall k (z : A), depth_aux m_aug k z <= k).
        { intro k. induction k as [| k' IHk].
          - intro z. simpl. apply Nat.le_refl.
          - intro z. simpl. destruct (m_aug z) as [p | d].
            + exact (le_n_S _ _ (IHk p)).
            + apply Nat.le_0_l. }
        assert (Hdepth_le : forall z, In A sub z -> depth z <= nx).
        { intros z _. unfold depth. exact (Hdepth_le_gen nx z). }

        (* For z in fiber(a): chain_root_aux nx z = a implies depth-based stepping works *)
        (* Prove: forall z ∈ sub with f z = a, depth z steps reaches a *)
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
                (* Hfz : chain_root_aux m_aug nx' p = a, goal: chain_root_aux m_aug (S nx') p = a *)
                assert (Hp_sub : In A sub p) by exact (proj1 Hm_info).
                rewrite (Hiter_eq2 (S nx') p Hp_sub).
                rewrite Nat.iter_succ.
                rewrite <- (Hiter_eq2 nx' p Hp_sub).
                rewrite Hfz.
                destruct (Hla_dummy a Ha) as [k_a [_ Hma]].
                unfold step. rewrite Hma. reflexivity.
            + exact (proj2 Hm_info).
          - exact (Hdummy_means_la z Hz (ex_intro _ d Hzm)). }

        (* depth_aux is stable under +1 fuel for fiber elements *)
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
              { assert (Hm_in : In (sum A A) (nbrs_aug z) (m_aug z)) by exact (Hm_nbrs z Hz).
                rewrite Hzm in Hm_in. exact (proj1 Hm_in). }
              simpl depth_aux. rewrite Hzm.
              rewrite (IHk z' Hz'_sub Hcr). reflexivity.
            + simpl depth_aux. rewrite Hzm. reflexivity. }

        (* depth of successor = depth of element - 1 for fiber elements *)
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

        (* Main chain property: prove by induction on depth *)
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
    }

    exact (ex_intro _ f (conj Hf_assign Hf_chain)).
  Qed.

End HallKernel.

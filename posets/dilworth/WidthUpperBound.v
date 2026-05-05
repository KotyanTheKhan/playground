From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices upper_bound.HallDefect.

Local Lemma Nat_le_of_succ_le (n m : nat) : Datatypes.S n <= m -> n <= m.
Proof. lia. Qed.

Section DilworthBackward.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Local Notation StrictSucc := (HallDefect.StrictSucc R).
  Local Notation StrictPred := (HallDefect.StrictPred R).

  (* ========================================================================= *)
  (* Chain root auxiliary functions                                            *)
  (* ========================================================================= *)

  Fixpoint chain_root_aux (m : A -> sum A A) (fuel : nat) (x : A) : A :=
    match fuel with
    | 0 => x
    | S k => match m x with
             | inr _ => x
             | inl y => chain_root_aux m k y
             end
    end.

  Fixpoint depth_aux (m : A -> sum A A) (fuel : nat) (x : A) : nat :=
    match fuel with
    | 0 => 0
    | S k => match m x with
             | inr _ => 0
             | inl y => S (depth_aux m k y)
             end
    end.

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
          (fun z => match z with inl y => In A sub y | inr _ => False end) nx).
      { clear - Hcard_sub.
        induction Hcard_sub as [| S' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split. intro Hz. inversion Hz. intro Hz. destruct z as [y|b]; simpl in Hz; inversion Hz.
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
      }
      assert (HcardInr : cardinal (sum A A)
          (fun z => match z with inl _ => False | inr a => In A la a end) w).
      { clear - Hcard_la.
        induction Hcard_la as [| la' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split. intro Hz. inversion Hz. intro Hz. destruct z as [y|b]; simpl in Hz; inversion Hz.
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl _ => False | inr a => In A la' a end)
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
      }
      assert (HcardY : cardinal (sum A A) Y (nx + w)).
      { apply (cardinal_extensional_poly (sum A A)
            (Union (sum A A)
              (fun z => match z with inl y => In A sub y | inr _ => False end)
              (fun z => match z with inl _ => False | inr a => In A la a end))).
        - intro z. split; intro Hz.
          + (* Union ... z -> Y z *)
            unfold Y. destruct z as [y | a].
            * inversion Hz as [u Hu Heq | u Hu Heq]; subst u; simpl in Hu.
              -- exact Hu.
              -- exact (False_rect _ Hu).
            * inversion Hz as [u Hu Heq | u Hu Heq]; subst u; simpl in Hu.
              -- exact (False_rect _ Hu).
              -- exact Hu.
          + (* Y z -> Union ... z *)
            unfold Y in Hz. destruct z as [y | a].
            * apply Union_introl. exact Hz.
            * apply Union_intror. exact Hz.
        - apply cardinal_disjoint_union_gen.
          + intros z Hl Hr. destruct z; simpl in *; [exact Hr | exact Hl].
          + exact HcardInl.
          + exact HcardInr. }
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
          (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end) nP).
      { clear - HcardSP.
        induction HcardSP as [| SP' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split; intro Hz. inversion Hz. destruct z as [y|b]; simpl in Hz; [inversion Hz | inversion Hz].
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl y => In A SP' y | inr _ => False end)
                (inl a))).
          + intro z. split; intro Hz.
            * destruct Hz as [z' Hz' | z' Hz'].
              -- simpl in Hz'. destruct z' as [y | b].
                 ++ apply Union_introl. exact Hz'.
                 ++ exact (False_rect _ Hz').
              -- inversion Hz'. subst z'. simpl. apply Union_intror. apply In_singleton.
            * destruct z as [y | b].
              -- simpl in Hz. destruct Hz as [z' Hz' | z' Hz'].
                 ++ apply Union_introl. exact Hz'.
                 ++ inversion Hz'. subst z'. apply Union_intror. apply In_singleton.
              -- simpl in Hz. exact (False_rect _ Hz).
          + apply card_add. exact IH.
            intro Hcontra. exact (Ha_notin Hcontra). }
      (* Cardinal of inr-image(la) *)
      assert (HcardInrLa : cardinal (sum A A)
          (fun z => match z with inl _ => False | inr a => In A la a end) w).
      { clear - Hcard_la.
        induction Hcard_la as [| la' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split; intro Hz. inversion Hz. destruct z as [y|b]; simpl in Hz; [inversion Hz | inversion Hz].
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl _ => False | inr a => In A la' a end)
                (inr a))).
          + intro z. split; intro Hz.
            * destruct Hz as [z' Hz' | z' Hz'].
              -- simpl in Hz'. destruct z' as [y | b].
                 ++ exact (False_rect _ Hz').
                 ++ apply Union_introl. exact Hz'.
              -- inversion Hz'. subst z'. apply Union_intror. apply In_singleton.
            * destruct z as [y | b].
              -- simpl in Hz. exact (False_rect _ Hz).
              -- simpl in Hz. destruct Hz as [z' Hz' | z' Hz'].
                 ++ apply Union_introl. exact Hz'.
                 ++ inversion Hz'. subst z'. apply Union_intror. apply In_singleton.
          + apply card_add. exact IH.
            intro Hcontra. exact (Ha_notin Hcontra). }
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

  Lemma below_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R x (f x)) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Hbelow HfinSub.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [HinhLa HincompLa].
    destruct (finite_cardinal A sub HfinSub) as [nx Hcard_sub].

    (* Augmented bipartite graph: L = sub, R_type = sum A A *)
    (* nbrs_aug(x) = {inl y | y ∈ sub, R x y, x ≠ y} ∪ {inr a | a ∈ la} *)
    set (nbrs_aug := fun (x : A) (z : sum A A) =>
      match z with
      | inl y => In A sub y /\ R x y /\ x <> y
      | inr a => In A la a
      end).

    set (Y := fun (z : sum A A) =>
      match z with
      | inl y => In A sub y
      | inr a => In A la a
      end).

    assert (HfinY : Finite (sum A A) Y).
    {
      assert (HcardInl : cardinal (sum A A)
          (fun z => match z with inl y => In A sub y | inr _ => False end) nx).
      { clear - Hcard_sub.
        induction Hcard_sub as [| S' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split; intro Hz. inversion Hz. destruct z as [y|b]; simpl in Hz; [inversion Hz | inversion Hz].
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl y => In A S' y | inr _ => False end)
                (inl a))).
          + intro z. split; intro Hz.
            * unfold Add in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
              -- destruct z as [y | b].
                 ++ apply Union_introl. exact Hz'.
                 ++ exact Hz'.
              -- inversion Hz'. subst. simpl. apply Union_intror. apply In_singleton.
            * unfold Add. destruct z as [y | b].
              -- simpl in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
                 ++ apply Union_introl. exact Hz'.
                 ++ inversion Hz'. apply Union_intror. apply In_singleton.
              -- simpl in Hz. exact (False_rect _ Hz).
          + apply card_add. exact IH.
            intro Hcontra. simpl in Hcontra.
            exact (Ha_notin Hcontra). }
      assert (HcardInr : cardinal (sum A A)
          (fun z => match z with inl _ => False | inr a => In A la a end) w).
      { clear - Hcard_la.
        induction Hcard_la as [| la' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split; intro Hz. inversion Hz. destruct z as [y|b]; simpl in Hz; [inversion Hz | inversion Hz].
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl _ => False | inr a => In A la' a end)
                (inr a))).
          + intro z. split; intro Hz.
            * unfold Add in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
              -- destruct z as [y | b].
                 ++ exact Hz'.
                 ++ apply Union_introl. exact Hz'.
              -- inversion Hz'. subst. simpl. apply Union_intror. apply In_singleton.
            * unfold Add. destruct z as [y | b].
              -- simpl in Hz. exact (False_rect _ Hz).
              -- simpl in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
                 ++ apply Union_introl. exact Hz'.
                 ++ inversion Hz'. apply Union_intror. apply In_singleton.
          + apply card_add. exact IH.
            intro Hcontra. simpl in Hcontra.
            exact (Ha_notin Hcontra). }
      assert (HcardY : cardinal (sum A A) Y (nx + w)).
      { apply (cardinal_extensional_poly (sum A A)
            (Union (sum A A)
              (fun z => match z with inl y => In A sub y | inr _ => False end)
              (fun z => match z with inl _ => False | inr a => In A la a end))).
        - intro z. split; intro Hz.
          + destruct Hz as [z' Hz' | z' Hz']; subst.
            * unfold Y. destruct z' as [y | a]; simpl in Hz'.
              -- exact Hz'.
              -- exact (False_rect _ Hz').
            * unfold Y. destruct z' as [y | a]; simpl in Hz'.
              -- exact (False_rect _ Hz').
              -- exact Hz'.
          + unfold Y in Hz. destruct z as [y | a]; simpl in Hz.
            * apply Union_introl. exact Hz.
            * apply Union_intror. exact Hz.
        - apply cardinal_disjoint_union_gen.
          + intros z Hl Hr. destruct z. exact Hr. exact Hl.
          + exact HcardInl.
          + exact HcardInr. }
      exact (cardinal_finite (sum A A) Y (nx + w) HcardY).
    }

    assert (HinhR : inhabited (sum A A)).
    { destruct HinhLa as [a Ha]. exact (inhabits (inr a)). }

    assert (Hnbrs_Y : forall x z, In A sub x -> In (sum A A) (nbrs_aug x) z -> In (sum A A) Y z).
    { intros x z Hx Hz. unfold nbrs_aug in Hz. unfold Y.
      destruct z as [y | a].
      - exact (proj1 Hz).
      - exact Hz. }

    (* Hall's condition for the successor version (using StrictSucc and dilworth_hall_defect) *)
    assert (Hhall : HallCondition sub nbrs_aug).
    {
      intros S ns nn HinclS HcardS HcardNS.
      destruct ns as [| ns'].
      { lia. }
      assert (HinhS : Inhabited A S).
      { inversion HcardS as [| S0 m Hm x Hx_notin]. subst.
        apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
      assert (HfinSS : Finite A (StrictSucc sub S)).
      { apply (Finite_downward_closed A sub HfinSub). intros y Hy. exact (proj1 Hy). }
      destruct (finite_cardinal A (StrictSucc sub S) HfinSS) as [nS HcardSS].
      assert (Hset_eq : set_neighbors nbrs_aug S =
          Union (sum A A)
            (fun z => match z with inl y => In A (StrictSucc sub S) y | inr _ => False end)
            (fun z => match z with inl _ => False | inr a => In A la a end)).
      { apply Extensionality_Ensembles. intro z. split.
        - intros [x [Hx Hz]]. unfold nbrs_aug in Hz. destruct z as [y | a].
          + apply Union_introl. unfold HallDefect.StrictSucc.
            exact (conj (proj1 Hz) (ex_intro _ x (conj Hx (conj (proj1 (proj2 Hz)) (proj2 (proj2 Hz)))))).
          + apply Union_intror. exact Hz.
        - intro Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
          + destruct z as [y | a]. 2: exact (False_rect _ Hz').
            simpl in Hz'. unfold HallDefect.StrictSucc in Hz'.
            destruct Hz' as [Hy [x [Hx [HRxy Hne]]]].
            exists x. split. exact Hx. unfold nbrs_aug.
            exact (conj Hy (conj HRxy Hne)).
          + destruct z as [y | a]. exact (False_rect _ Hz').
            simpl in Hz'.
            destruct HinhS as [x0 Hx0].
            exists x0. split. exact Hx0. unfold nbrs_aug. exact Hz'. }
      assert (HcardInlS : cardinal (sum A A)
          (fun z => match z with inl y => In A (StrictSucc sub S) y | inr _ => False end) nS).
      { clear - HcardSS.
        induction HcardSS as [| SS' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split; intro Hz. inversion Hz. destruct z as [y|b]; simpl in Hz; [inversion Hz | inversion Hz].
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl y => In A SS' y | inr _ => False end)
                (inl a))).
          + intro z. split; intro Hz.
            * unfold Add in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
              -- destruct z as [y | b].
                 ++ apply Union_introl. exact Hz'.
                 ++ exact Hz'.
              -- inversion Hz'. subst. simpl. apply Union_intror. apply In_singleton.
            * unfold Add. destruct z as [y | b].
              -- simpl in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
                 ++ apply Union_introl. exact Hz'.
                 ++ inversion Hz'. apply Union_intror. apply In_singleton.
              -- simpl in Hz. exact (False_rect _ Hz).
          + apply card_add. exact IH.
            intro Hcontra. simpl in Hcontra.
            exact (Ha_notin Hcontra). }
      assert (HcardInrLa : cardinal (sum A A)
          (fun z => match z with inl _ => False | inr a => In A la a end) w).
      { clear - Hcard_la.
        induction Hcard_la as [| la' k Hcard' IH a Ha_notin].
        - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
          + intro z. split; intro Hz. inversion Hz. destruct z as [y|b]; simpl in Hz; [inversion Hz | inversion Hz].
          + apply card_empty.
        - apply (cardinal_extensional_poly (sum A A)
              (Add (sum A A)
                (fun z => match z with inl _ => False | inr a => In A la' a end)
                (inr a))).
          + intro z. split; intro Hz.
            * unfold Add in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
              -- destruct z as [y | b].
                 ++ exact Hz'.
                 ++ apply Union_introl. exact Hz'.
              -- inversion Hz'. subst. simpl. apply Union_intror. apply In_singleton.
            * unfold Add. destruct z as [y | b].
              -- simpl in Hz. exact (False_rect _ Hz).
              -- simpl in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
                 ++ apply Union_introl. exact Hz'.
                 ++ inversion Hz'. apply Union_intror. apply In_singleton.
          + apply card_add. exact IH.
            intro Hcontra. simpl in Hcontra.
            exact (Ha_notin Hcontra). }
      assert (HcardUnion : cardinal (sum A A)
          (Union (sum A A)
            (fun z => match z with inl y => In A (StrictSucc sub S) y | inr _ => False end)
            (fun z => match z with inl _ => False | inr a => In A la a end))
          (nS + w)).
      { apply cardinal_disjoint_union_gen.
        - intros z Hl Hr. destruct z. exact Hr. exact Hl.
        - exact HcardInlS.
        - exact HcardInrLa. }
      assert (Hnn_eq : nn = nS + w).
      { apply (cardinal_unicity (sum A A) (set_neighbors nbrs_aug S)).
        - exact HcardNS.
        - apply (cardinal_extensional_poly (sum A A)
              (Union (sum A A)
                (fun z => match z with inl y => In A (StrictSucc sub S) y | inr _ => False end)
                (fun z => match z with inl _ => False | inr a => In A la a end))).
          + intro z. rewrite <- Hset_eq. tauto.
          + exact HcardUnion. }
      (* Use dilworth_hall_defect for Below *)
      (* For below: sub ⊆ Below(la), so we use dilworth_hall_defect directly *)
      (* dilworth_hall_defect works for sub ⊆ Above(la). But sub ⊆ Below(la). *)
      (* We need the symmetric version. Let me use it: *)
      (* Actually dilworth_hall_defect_pred was for Above and StrictPred. *)
      (* For Below and StrictSucc: we use dilworth_hall_defect directly! *)
      (* Because dilworth_hall_defect says: for sub ⊆ Above(la), ∀S: |S| ≤ |StrictSucc(sub,S)| + w *)
      (* Here sub ⊆ Below(la), and nbrs are StrictSucc. So we need:
         |S| ≤ |StrictSucc(sub,S)| + w for sub ⊆ Below(la) *)
      (* Let's prove this directly analogously *)
      (* Actually dilworth_hall_defect uses Above and StrictSucc. For Below we need the symmetric lemma.
         But we didn't prove a "dilworth_hall_defect_below" lemma.
         Wait - dilworth_hall_defect says:
           IsLargestAntichain R sub la w -> Included sub (Above la) ->
           ∀S ⊆ sub, |S| ≤ |StrictSucc sub S| + w.
         For our below case we have: IsLargestAntichain R sub la w, Included sub (Below la).
         We need: ∀S ⊆ sub, |S| ≤ |StrictSucc sub S| + w.
         But dilworth_hall_defect requires Included sub (Above la), not Below!

         Hmm, this is a problem. We need a "below" version.
         Actually let me re-examine. dilworth_hall_defect proves |S| ≤ |StrictSucc(sub,S)| + w
         where StrictSucc(sub,S)(y) = y ∈ sub ∧ ∃x ∈ S, R x y ∧ x ≠ y.
         For sub ⊆ Below(la) and Hall matching going "up" (R x y with y = succ), this should work
         WITHOUT needing Habove. Let me re-read dilworth_hall_defect...

         Actually it uses `Hmax` (IsLargestAntichain) and `HinclS` (S ⊆ sub ⊆ Below(la) via Hbelow).
         The proof of M being an antichain uses: if R x y with x,y ∈ M ⊆ S ⊆ sub,
         then y ∈ StrictSucc(sub,S) since x ∈ S, R x y, x ≠ y.
         This does NOT require Habove! Let me check the proof of dilworth_hall_defect again...

         Looking at the proof: it uses:
         - HinclS (S ⊆ sub)
         - Hmax (largest antichain bound)
         but NOT Habove directly in the M-antichain proof.
         Wait, actually Habove appears in `Hmax`:
           Hmax M _ antichain HinclS HcardM
         where the second arg should be Included M sub (not the full poset).
         And HinclS x (proj1 HxM) gives M ⊆ sub ⊆ Above(la)... no, it just gives M ⊆ sub.
         And Hmax requires Included s sub (from IsLargestAntichain), not Above.

         Actually Habove is NOT used in dilworth_hall_defect - let me verify:
         The proof only uses:
           destruct Hla as [_ Hincl_la Hcard_la Hmax]
         And Hmax is: forall s n, IsAntichain s -> Included s sub -> cardinal s n -> n ≤ w.
         So Hmax needs Included M sub, not sub ⊆ Above.

         So dilworth_hall_defect actually does NOT use Habove! Let me re-read... *)
      (* Yes! dilworth_hall_defect does not use Habove at all. The Habove appears in the signature
         but looking at the proof: `destruct Hla as [_ Hincl_la Hcard_la Hmax]` and never uses Habove. *)
      (* So we can use dilworth_hall_defect directly! *)
      assert (Hns_le : Datatypes.S ns' <= nS + w).
      { apply (dilworth_hall_defect R sub la w Hla' S (Datatypes.S ns') nS).
        - exact HinclS.
        - exact HcardS.
        - exact HcardSS. }
      lia.
    }

    destruct (hall_marriage_theorem sub Y nx nbrs_aug Hcard_sub HfinY HinhR
                (fun x z Hx Hz => Hnbrs_Y x z Hx Hz) Hhall)
      as [m_aug [Hm_Y [Hm_nbrs Hm_inj]]].

    (* la-elements → m_aug returns inr *)
    assert (Hla_dummy : forall a, In A la a ->
        exists k, In A la k /\ m_aug a = inr k).
    {
      intros a Ha.
      assert (Ha_sub : In A sub a) by exact (Hincl_la a Ha).
      assert (Hm_in : In (sum A A) (nbrs_aug a) (m_aug a)) by exact (Hm_nbrs a Ha_sub).
      unfold nbrs_aug in Hm_in.
      destruct (m_aug a) as [y | k] eqn:Hma.
      - destruct Hm_in as [Hy_sub [HRay Hyne]].
        exfalso.
        assert (Hmax_a : forall z, In A sub z -> R a z -> z = a).
        { intros z Hz HRaz.
          destruct (Hbelow z Hz) as [c [Hc_la Hzc]].
          assert (Hac : R a c) by exact (poset_trans a z c HRaz Hzc).
          assert (Haeqc : a = c) by exact (HincompLa a c Ha Hc_la (or_introl Hac)).
          subst c. exact (poset_antisym z a Hzc HRaz). }
        exact (Hyne (eq_sym (Hmax_a y Hy_sub HRay))).
      - exact (ex_intro _ k (conj Hm_in eq_refl)).
    }

    assert (Hdummy_means_la : forall z, In A sub z -> (exists d, m_aug z = inr d) -> In A la z).
    {
      intros z Hz [d Hm_z].
      assert (Hd_la : In A la d).
      { assert (Hm_in : In (sum A A) (nbrs_aug z) (m_aug z)) by exact (Hm_nbrs z Hz).
        rewrite Hm_z in Hm_in. exact Hm_in. }
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
    }

    set (f := fun x => chain_root_aux m_aug nx x).

    assert (Hf_la : forall a, In A la a -> chain_root_aux m_aug nx a = a).
    {
      intros a Ha.
      destruct (Hla_dummy a Ha) as [k [_ Hma]].
      destruct nx as [| nx'].
      - simpl. reflexivity.
      - simpl. rewrite Hma. reflexivity.
    }

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

    assert (Hstep_R : forall z, In A sub z ->
        match m_aug z with
        | inl y => In A sub y /\ R z y /\ z <> y
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

    assert (Hiter_sub : forall k, k <= nx -> forall x0, In A sub x0 ->
        In A sub (Nat.iter k step x0)).
    {
      intros k Hk x0 Hx0.
      rewrite <- Hiter_eq2 by exact Hx0.
      exact (Hsteps_in_sub k x0 Hx0 Hk).
    }

    assert (Hf_assign : forall x, In A sub x -> In A la (f x) /\ R x (f x)).
    {
      intro x. intro Hx.
      unfold f.
      rewrite (Hiter_eq2 nx x Hx).

      assert (Hiter_sub_x : forall k, k <= nx -> In A sub (Nat.iter k step x))
        by exact (fun k Hk => Hiter_sub k Hk x Hx).

      assert (HRdesc_succ : forall k, k < nx ->
          match m_aug (Nat.iter k step x) with
          | inl _ => R (Nat.iter k step x) (Nat.iter (S k) step x) /\
                     Nat.iter k step x <> Nat.iter (S k) step x
          | inr _ => True
          end).
      {
        intros k Hk.
        assert (Hzk_sub : In A sub (Nat.iter k step x))
          by exact (Hiter_sub_x k (Nat.lt_le_incl _ _ Hk)).
        assert (Hstep_k := Hstep_R (Nat.iter k step x) Hzk_sub).
        destruct (m_aug (Nat.iter k step x)) as [y | d] eqn:Hm.
        - simpl in Hstep_k.
          assert (Hstep_eq : step (Nat.iter k step x) = y).
          { unfold step at 1. rewrite Hm. reflexivity. }
          rewrite Nat.iter_succ. rewrite Hstep_eq.
          split. exact (proj1 (proj2 Hstep_k)). exact (proj2 (proj2 Hstep_k)).
        - exact I.
      }

      destruct (classic (exists k, k <= nx /\ match m_aug (Nat.iter k step x) with inr _ => True | inl _ => False end)) as [Hstop | Hnostop].
      {
        destruct Hstop as [k0 [Hk0_le Hstop]].
        assert (Hstable : forall j, Nat.iter (k0 + j) step x = Nat.iter k0 step x).
        {
          intro j. induction j as [| j' IHj].
          - rewrite Nat.add_0_r. reflexivity.
          - rewrite Nat.add_succ_r. rewrite Nat.iter_succ. rewrite IHj.
            unfold step at 1. destruct (m_aug (Nat.iter k0 step x)) as [y | d].
            + exact (False_rect _ Hstop).
            + reflexivity.
        }
        assert (Hk0_plus : nx = k0 + (nx - k0)) by lia.
        rewrite Hk0_plus. rewrite (Hstable (nx - k0)).
        assert (Hk0_sub : In A sub (Nat.iter k0 step x)) by exact (Hiter_sub_x k0 Hk0_le).
        assert (Hm_k0 : In (sum A A) (nbrs_aug (Nat.iter k0 step x)) (m_aug (Nat.iter k0 step x)))
          by exact (Hm_nbrs (Nat.iter k0 step x) Hk0_sub).
        unfold nbrs_aug in Hm_k0.
        destruct (m_aug (Nat.iter k0 step x)) as [y | a] eqn:Heq_k0.
        - exact (False_rect _ Hstop).
        - split.
          { exact (Hdummy_means_la (Nat.iter k0 step x) Hk0_sub (ex_intro _ a Heq_k0)). }
          assert (Hlocal_asc : forall j m, j + m <= nx ->
              R (Nat.iter j step x) (Nat.iter (j + m) step x)).
          {
            intros j m. induction m as [| m' IHm].
            - intros _. rewrite Nat.add_0_r. apply poset_refl.
            - intro Hle.
              assert (Hjm'_le : j + m' <= nx) by lia.
              assert (Hiter_sub' : In A sub (Nat.iter (j + m') step x))
                by exact (Hiter_sub (j + m') Hjm'_le x Hx).
              assert (Hstep_info' := Hstep_R (Nat.iter (j + m') step x) Hiter_sub').
              replace (j + Datatypes.S m') with (Datatypes.S (j + m')) by lia.
              rewrite Nat.iter_succ.
              destruct (m_aug (Nat.iter (j + m') step x)) as [y' | d'] eqn:Hm'.
              + assert (Hstep_val' : step (Nat.iter (j + m') step x) = y').
                { unfold step at 1. rewrite Hm'. reflexivity. }
                rewrite Hstep_val'.
                apply (poset_trans (Nat.iter j step x) (Nat.iter (j + m') step x) y').
                * exact (IHm Hjm'_le).
                * exact (proj1 (proj2 Hstep_info')).
              + assert (Hstep_val' : step (Nat.iter (j + m') step x) = Nat.iter (j + m') step x).
                { unfold step at 1. rewrite Hm'. reflexivity. }
                rewrite Hstep_val'. exact (IHm Hjm'_le).
          }
          assert (Hasc : forall k, k <= k0 -> R (Nat.iter k step x) (Nat.iter k0 step x)).
          {
            intros k Hk_le.
            replace k0 with (k + (k0 - k)) by lia.
            apply Hlocal_asc. lia.
          }
          exact (Hasc 0 (Nat.le_0_l k0)).
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
        assert (Hdistinct : forall i j, i < j -> j <= nx ->
            Nat.iter i step x <> Nat.iter j step x).
        {
          intros i j Hi_lt_j Hj_le.
          intro Heq.
          assert (HR_asc : forall a b, a < b -> b <= nx ->
              R (Nat.iter a step x) (Nat.iter b step x)).
          { intros a b Hab Hb_le.
            induction b as [| b'].
            - lia.
            - destruct (Nat.eq_dec a b') as [Hab' | Hab'].
              + subst b'.
                { pose proof (Hallnotfixed a (Nat.lt_le_incl _ _ Hb_le)) as Hfix.
                  pose proof (HRdesc_succ a Hb_le) as HRd.
                  destruct (m_aug (Nat.iter a step x)) as [y | d].
                  - exact (proj1 HRd).
                  - contradiction. }
              + assert (Ha_lt_b' : a < b') by lia.
                assert (Hb'_le : b' <= nx) by lia.
                apply (poset_trans (Nat.iter a step x) (Nat.iter b' step x) (Nat.iter (S b') step x)).
                * exact (IHb' Ha_lt_b' Hb'_le).
                * { pose proof (Hallnotfixed b' Hb'_le) as Hfix.
                    pose proof (HRdesc_succ b' Hb_le) as HRd.
                    destruct (m_aug (Nat.iter b' step x)) as [y | d].
                    - exact (proj1 HRd).
                    - contradiction. } }
          assert (Hdist_succ : forall k, k < nx ->
              Nat.iter k step x <> Nat.iter (k+1) step x).
          { intros k Hk.
            assert (Hfixed_k := Hallnotfixed k (Nat.lt_le_incl _ _ Hk)).
            replace (k + 1) with (Datatypes.S k) by lia.
            rewrite Nat.iter_succ. unfold step at 2.
            assert (Hzk_sub : In A sub (Nat.iter k step x))
              by exact (Hiter_sub_x k (Nat.lt_le_incl _ _ Hk)).
            assert (Hstep_k := Hstep_R (Nat.iter k step x) Hzk_sub).
            destruct (m_aug (Nat.iter k step x)) as [y | d].
            - exact (proj2 (proj2 Hstep_k)).
            - exact (False_rect _ Hfixed_k). }
          (* Same contradiction as above case *)
          assert (HR_i_j : R (Nat.iter i step x) (Nat.iter j step x))
            by exact (HR_asc i j Hi_lt_j Hj_le).
          assert (HR_i1_i : R (Nat.iter i step x) (Nat.iter (S i) step x)).
          { pose proof (Hallnotfixed i (Nat.lt_le_incl _ _ (Nat.lt_le_trans _ _ _ Hi_lt_j Hj_le))) as Hfi.
            pose proof (HRdesc_succ i (Nat.lt_le_trans _ _ _ Hi_lt_j Hj_le)) as HRd.
            destruct (m_aug (Nat.iter i step x)) as [y | d]; [exact (proj1 HRd) | contradiction]. }
          assert (HR_i1_j : R (Nat.iter (S i) step x) (Nat.iter j step x)).
          { destruct (Nat.eq_dec (S i) j) as [Heq'|Hne].
            - subst. apply poset_refl.
            - apply HR_asc; lia. }
          rewrite <- Heq in HR_i1_j.
          assert (Heq_i_Si : Nat.iter i step x = Nat.iter (S i) step x)
            by exact (poset_antisym _ _ HR_i1_i HR_i1_j).
          replace (S i) with (i + 1) in Heq_i_Si by lia.
          exact (Hdist_succ i (Nat.lt_le_trans _ _ _ Hi_lt_j Hj_le) Heq_i_Si).
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
            + exact (Hiter_sub_x k Hk).
            + reflexivity.
          - intros i j y Hi Hj _ Heqi Heqj. subst.
            destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
            + exact (False_rect _ (Hdistinct i j Hij Hj Heqj)).
            + exact Hij.
            + exact (False_rect _ (Hdistinct j i Hij Hi (eq_sym Heqj))).
          - exact HcardRange.
          - exact Hcard_sub. }
        exact (Nat.lt_irrefl nx (Nat.lt_le_trans _ _ _ (Nat.lt_succ_diag_r nx) Hle)).
      }
    }

    assert (Hf_chain : forall a, In A la a ->
        IsChain R (fun x => In A sub x /\ f x = a)).
    {
      intros a Ha.
      split.
      - apply Inhabited_intro with a.
        split. exact (Hincl_la a Ha).
        unfold f. rewrite (Hiter_eq2 nx a (Hincl_la a Ha)).
        destruct (Hla_dummy a Ha) as [k_a [_ Hma]].
        assert (Hstep_a : step a = a).
        { unfold step. rewrite Hma. reflexivity. }
        assert (Hiter_a : forall k, Nat.iter k step a = a).
        { intro k. induction k as [| k' IHk].
          - reflexivity.
          - rewrite Nat.iter_succ. rewrite IHk. exact Hstep_a. }
        exact (Hiter_a nx).
      - intros x y [Hx_sub Hx_f] [Hy_sub Hy_f].
        unfold f in Hx_f, Hy_f.
        set (depth := fun z => depth_aux m_aug nx z).

        assert (Hstep_to_succ : forall z, In A sub z ->
            chain_root_aux m_aug nx z = a ->
            match m_aug z with
            | inl y => In A sub y /\ chain_root_aux m_aug nx y = a /\ R z y /\ z <> y
            | inr _ => In A la z
            end).
        { intros z Hz Hfz.
          assert (Hm_info := Hstep_R z Hz).
          destruct (m_aug z) as [yz | d] eqn:Hzm.
          - simpl in Hm_info.
            split. exact (proj1 Hm_info).
            split.
            + destruct nx as [| nx'] eqn:Hnx.
              * inversion Hcard_sub. subst. inversion Hz.
              * simpl chain_root_aux in Hfz. rewrite Hzm in Hfz.
                assert (Hyz_sub : In A sub yz) by exact (proj1 Hm_info).
                rewrite (Hiter_eq2 (S nx') yz Hyz_sub).
                rewrite Nat.iter_succ.
                rewrite <- (Hiter_eq2 nx' yz Hyz_sub).
                rewrite Hfz.
                destruct (Hla_dummy a Ha) as [k_a [_ Hma]].
                unfold step. rewrite Hma. reflexivity.
            + exact (proj2 Hm_info).
          - exact (Hdummy_means_la z Hz (ex_intro _ d Hzm)). }

        assert (Hdepth_inr_b : forall k z,
            match m_aug z with inr _ => True | inl _ => False end ->
            depth_aux m_aug k z = 0).
        { intros k z Hinr. induction k as [| k' IHk].
          - reflexivity.
          - simpl. destruct (m_aug z). exact (False_rect _ Hinr). reflexivity. }

        assert (Hdepth_inl_b : forall k z z',
            m_aug z = inl z' ->
            depth_aux m_aug (S k) z = S (depth_aux m_aug k z')).
        { intros k z z' Hmz.
          simpl depth_aux. rewrite Hmz. reflexivity. }

        assert (Hdepth_stable_b : forall k (z : A), In A sub z ->
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

        assert (Hfiber_depth_succ : forall z sz, In A sub z ->
            chain_root_aux m_aug nx z = a ->
            m_aug z = inl sz -> In A sub sz ->
            depth z = S (depth sz)).
        { intros z sz Hz Hcrz Hmz Hsz_sub.
          unfold depth.
          destruct nx as [| nx_prev] eqn:Hnx.
          - simpl chain_root_aux in Hcrz. subst z.
            destruct (Hla_dummy a Ha) as [ka [_ Hma]]. rewrite Hma in Hmz. discriminate Hmz.
          - assert (Hcrsz : chain_root_aux m_aug nx_prev sz = a).
            { simpl chain_root_aux in Hcrz. rewrite Hmz in Hcrz. exact Hcrz. }
            rewrite (Hdepth_inl_b nx_prev z sz Hmz).
            rewrite <- (Hdepth_stable_b nx_prev sz Hsz_sub Hcrsz).
            reflexivity. }

        assert (Hclaim : forall k v, In A sub v -> chain_root_aux m_aug nx v = a ->
            depth v = k ->
            forall x0, In A sub x0 -> chain_root_aux m_aug nx x0 = a ->
            depth x0 <= k -> R v x0).
        { intro k. induction k as [| k' IHk].
          - intros v Hv Hfv Hdv x0 Hx0 Hfx0 Hdx0.
            assert (Hv_la : In A la v).
            { unfold depth in Hdv.
              destruct nx as [| nx'].
              - simpl in Hdv. simpl in Hfv. subst v. exact Ha.
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
            assert (Hx0_la : In A la x0).
            { unfold depth in Hdx0.
              destruct nx as [| nx''].
              - simpl in Hfx0. subst x0. exact Ha.
              - simpl in Hdx0. destruct (m_aug x0) as [z'' | d''] eqn:Hx0m.
                + lia.
                + exact (Hdummy_means_la x0 Hx0 (ex_intro _ d'' Hx0m)). }
            assert (Hx0eqa : x0 = a).
            { rewrite (Hiter_eq2 nx x0 Hx0) in Hfx0.
              assert (Hstep_x0 : step x0 = x0).
              { unfold step. destruct (Hla_dummy x0 Hx0_la) as [k_x [_ Hmx]]. rewrite Hmx. reflexivity. }
              assert (Hiter_x0 : forall j, Nat.iter j step x0 = x0).
              { intro j. induction j. reflexivity. rewrite Nat.iter_succ. rewrite IHj. exact Hstep_x0. }
              rewrite Hiter_x0 in Hfx0. exact Hfx0. }
            subst x0. apply poset_refl.
          - intros v Hv Hfv Hdv x0 Hx0 Hfx0 Hdx0.
            assert (Hstep_v := Hstep_to_succ v Hv Hfv).
            assert (Hstep_x0 := Hstep_to_succ x0 Hx0 Hfx0).
            unfold depth in Hdv.
            destruct (m_aug v) as [sv | dv] eqn:Hvm.
            + destruct Hstep_v as [Hsv_sub [Hsv_f [HRv_sv Hvne]]].
              assert (Hd_sv : depth sv = k').
              { assert (Hfdv := Hfiber_depth_succ v sv Hv Hfv Hvm Hsv_sub).
                unfold depth in Hfdv. rewrite Hfdv in Hdv.
                injection Hdv as Hdv'. unfold depth. exact Hdv'. }
              unfold depth in Hdx0.
              destruct (m_aug x0) as [sx0 | dx0] eqn:Hx0m.
              * destruct Hstep_x0 as [Hsx0_sub [Hsx0_f [HRx0_sx0 Hx0ne]]].
                assert (Hd_sx0 : depth sx0 <= k').
                { assert (Hfdx0 := Hfiber_depth_succ x0 sx0 Hx0 Hfx0 Hx0m Hsx0_sub).
                  unfold depth in Hfdx0. rewrite Hfdx0 in Hdx0. unfold depth. lia. }
                destruct (Nat.eq_dec (depth_aux m_aug nx x0) (S k')) as [Heq_dx0 | Hne_dx0].
                -- assert (Hd_sx0_eq : depth sx0 = k').
                   { assert (Hfdx0 := Hfiber_depth_succ x0 sx0 Hx0 Hfx0 Hx0m Hsx0_sub).
                     unfold depth in Hfdx0. unfold depth. lia. }
                   assert (HR_sv_sx0 : R sv sx0) by exact (IHk sv Hsv_sub Hsv_f Hd_sv sx0 Hsx0_sub Hsx0_f Hd_sx0).
                   assert (HR_sx0_sv : R sx0 sv).
                   { apply (IHk sx0 Hsx0_sub Hsx0_f Hd_sx0_eq sv Hsv_sub Hsv_f).
                     rewrite Hd_sv. apply Nat.le_refl. }
                   assert (Hsx0_eq_sv : sx0 = sv) by exact (poset_antisym _ _ HR_sx0_sv HR_sv_sx0).
                   assert (Hm_eq : m_aug x0 = m_aug v) by (rewrite Hx0m, Hvm, Hsx0_eq_sv; reflexivity).
                   assert (Hx0_eq_v : x0 = v) by exact (Hm_inj x0 v Hx0 Hv Hm_eq).
                   subst v. apply poset_refl.
                -- assert (Hdx0_le_k' : depth_aux m_aug nx x0 <= k').
                   { unfold depth in Hdx0. lia. }
                   assert (HR_sv_x0 : R sv x0) by exact (IHk sv Hsv_sub Hsv_f Hd_sv x0 Hx0 Hfx0 Hdx0_le_k').
                   exact (poset_trans v sv x0 HRv_sv HR_sv_x0).
              * assert (Hx0_la : In A la x0).
                { exact (Hdummy_means_la x0 Hx0 (ex_intro _ dx0 Hx0m)). }
                assert (Hx0eqa : x0 = a).
                { rewrite (Hiter_eq2 nx x0 Hx0) in Hfx0.
                  assert (Hstep_x0' : step x0 = x0).
                  { unfold step. destruct (Hla_dummy x0 Hx0_la) as [k_x [_ Hmx]]. rewrite Hmx. reflexivity. }
                  assert (Hiter_x0 : forall j, Nat.iter j step x0 = x0).
                  { intro j. induction j. reflexivity. rewrite Nat.iter_succ. rewrite IHj. exact Hstep_x0'. }
                  rewrite Hiter_x0 in Hfx0. exact Hfx0. }
                subst x0.
                assert (HRvf := proj2 (Hf_assign v Hv)).
                unfold f in HRvf. rewrite Hfv in HRvf. exact HRvf.
            + assert (Hv_inr : match m_aug v with inr _ => True | inl _ => False end)
                by (rewrite Hvm; exact I).
              rewrite (Hdepth_inr_b nx v Hv_inr) in Hdv. discriminate Hdv.
        }

        destruct (classic (depth x <= depth y)) as [Hdxy | Hlt].
        + right. exact (Hclaim (depth y) y Hy_sub Hy_f eq_refl x Hx_sub Hx_f Hdxy).
        + left. assert (Hdyx : depth y < depth x) by lia.
          exact (Hclaim (depth x) x Hx_sub Hx_f eq_refl y Hy_sub Hy_f (Nat.lt_le_incl _ _ Hdyx)).
    }

    exact (ex_intro _ f (conj Hf_assign Hf_chain)).
  Qed.

  Lemma chain_cover_of_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    Finite A sub ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w Hla Hbelow HfinSub.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    destruct (constructive_indefinite_description _
               (below_chain_assignment_exists sub la w Hla' Hbelow HfinSub))
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
    Finite A sub ->
    IsChainCover R (Intersection A (Below R la) sub) cover_b ->
    cardinal (Ensemble A) cover_b w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w _cover_b Hla Habove HfinSub _ _.
    exact (chain_cover_of_above sub la w Hla Habove HfinSub).
  Qed.

  Lemma extend_cover_below : forall (sub la : Ensemble A) w
      (cover_a : Ensemble (Ensemble A)),
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    Finite A sub ->
    IsChainCover R (Intersection A (Above R la) sub) cover_a ->
    cardinal (Ensemble A) cover_a w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros sub la w _cover_a Hla Hbelow HfinSub _ _.
    exact (chain_cover_of_below sub la w Hla Hbelow HfinSub).
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
    { exact (antichain_lb_for_chain_cover R sub la w m merged
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
    assert (HfinSub : Finite A sub) by exact (cardinal_finite A sub n Hcard).
    assert (Hwn : w <= n) by exact (la_card_le_sub R sub la n w Hcard Hla).
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
      { destruct (below_card_lt R sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below R sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (extend_cover_above sub la w cover_b Hla Habove HfinSub Hcover_b Hcard_b). } }
    { destruct (excluded_middle_informative (Included A sub (Below R la))) as [Hbelow | Hnotbelow].
      { destruct (above_card_lt R sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above R sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        exact (extend_cover_below sub la w cover_a Hla Hbelow HfinSub Hcover_a Hcard_a). }
      { destruct (above_card_lt R sub la n w Hcard Hwn_lt Hla Hnotabove) as [na [Hna_card Hna_lt]].
        destruct (below_card_lt R sub la n w Hcard Hwn_lt Hla Hnotbelow) as [nb [Hnb_card Hnb_lt]].
        destruct (IH na (Intersection A (Above R la) sub) la w Hna_lt Hna_card
                      (la_largest_in_above R sub la w Hla))
          as [cover_a [Hcover_a Hcard_a]].
        destruct (IH nb (Intersection A (Below R la) sub) la w Hnb_lt Hnb_card
                      (la_largest_in_below R sub la w Hla))
          as [cover_b [Hcover_b Hcard_b]].
        exact (merge_above_below_covers sub la w cover_a cover_b Hla
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

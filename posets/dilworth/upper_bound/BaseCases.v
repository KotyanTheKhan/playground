(* Base cases for DilworthB:
   - empty/singleton antichains and width 0/1
   - the trivial singleton chain cover
   - the cardinality of a fiber-style chain cover (used to count |cover| = w
     in the assignment-derived chain cover). *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions CardinalLemmas.

Section BaseCases.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

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

End BaseCases.

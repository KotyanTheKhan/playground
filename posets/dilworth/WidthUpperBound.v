From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
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
    IsLargestAntichain R la w ->
    Inhabited A (Above R la) ->
    forall s n, IsAntichain R s -> Included A s (Above R la) -> 
                cardinal A s n -> n <= w.
  Proof.
    intros la w Hla Hinhab_above s n Hs Hincl Hcard_s.
    destruct Hla as [Hanti Hcard Hmax].
    apply (Hmax s n Hs Hcard_s).
  Qed.

  Lemma largest_antichain_in_Below : forall la w,
    IsLargestAntichain R la w ->
    Inhabited A (Below R la) ->
    forall s n, IsAntichain R s -> Included A s (Below R la) -> 
                cardinal A s n -> n <= w.
  Proof.
    intros la w Hla Hinhab_below s n Hs Hincl Hcard_s.
    destruct Hla as [Hanti Hcard Hmax].
    apply (Hmax s n Hs Hcard_s).
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

  (** Key lemma: If width = 1, then the entire poset is a chain *)
  Lemma width_one_implies_chain : forall (s : Ensemble A),
    IsLargestAntichain R s 1 ->
    IsChain R (Full_set A).
  Proof.
    intros s Hla.
    destruct Hla as [Ha Hcard Hmaximal].
    destruct Ha as [Hinhab Hanti].
    split.
    - destruct Hinhab as [a Ha].
      apply Inhabited_intro with a.
      apply Full_intro.
    - intros x y _ _.
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
      { apply (Hmaximal pair 2 Hanti_pair Hcard_pair). }
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

  Lemma dilworth_inductive_step : forall (la : Ensemble A) (w : nat),
    w >= 2 ->
    IsLargestAntichain R la w ->
    (forall (la' : Ensemble A) (w' : nat),
      w' < w ->
      IsLargestAntichain R la' w' ->
      { cover : Ensemble (Ensemble A) | IsChainCover R cover /\ cardinal (Ensemble A) cover w' }) ->
    { cover : Ensemble (Ensemble A) | IsChainCover R cover /\ cardinal (Ensemble A) cover w }.
  Proof.
  Admitted.

  (* ========================================================================= *)
  (* Backward Direction: DilworthB                                             *)
  (* ========================================================================= *)

  Lemma DilworthB : forall w la,
    IsLargestAntichain R la w ->
    { cover : Ensemble (Ensemble A) | IsChainCover R cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    refine (Fix lt_wf (fun w => forall la,
      IsLargestAntichain R la w ->
      { cover : Ensemble (Ensemble A) | IsChainCover R cover /\ cardinal (Ensemble A) cover w })
      (fun w IH la Hla => _)).
    
    destruct w as [| w'].
    - (* w = 0: empty antichain - contradiction *)
      exfalso.
      apply (empty_antichain_contradiction la).
      + destruct Hla; assumption.
      + destruct Hla as [_ Hc _]; assumption.
      
    - (* w = S w' *)
      destruct w' as [| w''].
      + (* w = 1: singleton antichain *)
        exists (Singleton (Ensemble A) (Full_set A)).
        destruct Hla as [Hanti Hcard_w Hmax].
        split.
        * constructor.
          -- intros c Hc. inversion Hc. subst c.
             apply (width_one_implies_chain la).
             constructor; [exact Hanti | exact Hcard_w | exact Hmax].
          -- intros c Hc. inversion Hc. subst c.
             intros x Hx. apply Full_intro.
          -- intros x Hx.
             exists (Full_set A). split.
             ++ apply In_singleton.
             ++ apply Full_intro.
        * replace 1 with (S 0) by reflexivity.
          apply (cardinal_extensional_poly (Ensemble A) (Add (Ensemble A) (Empty_set (Ensemble A)) (Full_set A)) (Singleton (Ensemble A) (Full_set A)) 1).
          -- intro X. split; intro HX.
             ++ unfold Add in HX. inversion HX as [X' HX' | X' HX']; subst.
                ** inversion HX'.
                ** inversion HX'. apply In_singleton.
             ++ inversion HX. subst X. unfold Add. apply Union_intror. apply In_singleton.
          -- apply card_add; [apply card_empty; intros X HX; inversion HX | intro Hcontra; inversion Hcontra].
          
      + (* w = S (S w''): use inductive step *)
        eapply dilworth_inductive_step.
        * lia.
        * exact Hla.
        * intros la' w_prime Hw_prime Hla'.
          apply (IH w_prime Hw_prime la' Hla').
  Qed.



End DilworthBackward.

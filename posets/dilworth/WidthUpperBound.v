From Stdlib Require Import Ensembles Finite_sets Classical ClassicalEpsilon Lia Arith Wf_nat.
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

  Definition MIN (sub : Ensemble A) : Ensemble A :=
    fun x => In A sub x /\ forall y, In A sub y -> R y x -> y = x.

  Definition MAX (sub : Ensemble A) : Ensemble A :=
    fun x => In A sub x /\ forall y, In A sub y -> R x y -> y = x.

  Lemma la_intersect_Above_Below : forall (sub la : Ensemble A),
    Included A la sub ->
    IsAntichain R la ->
    Intersection A (Above R la) (Below R la) = la.
  Proof.
    intros sub la Hincl Hanti.
    apply Extensionality_Ensembles.
    intro x. split; intro Hx.
    - destruct Hx as [x H_above H_below].
      unfold Above in H_above. unfold Below in H_below.
      destruct H_above as [y1 [Hy1 Ry1x]].
      destruct H_below as [y2 [Hy2 Rxy2]].
      destruct Hanti as [Hinhab Hanti_incomp].
      assert (Ry1y2 : R y1 y2).
      { apply poset_trans with (y := x); assumption. }
      assert (y1 = y2).
      { apply Hanti_incomp; [assumption | assumption | left; assumption]. }
      subst y2.
      assert (y1 = x).
      { apply poset_antisym; assumption. }
      subst x. exact Hy1.
    - split.
      + unfold Above. exists x. split; [assumption | apply poset_refl].
      + unfold Below. exists x. split; [assumption | apply poset_refl].
  Qed.



  Lemma MIN_is_antichain : forall sub,
    Inhabited A (MIN sub) ->
    IsAntichain R (MIN sub).
  Proof.
    intros sub Hinhab. split.
    - exact Hinhab.
    - intros x y Hx Hy Hcomp.
      destruct Hx as [Hx_in_sub Hx_min].
      destruct Hy as [Hy_in_sub Hy_min].
      destruct Hcomp as [Rxy | Ryx].
      + apply Hy_min; [exact Hx_in_sub | exact Rxy].
      + symmetry. apply Hx_min; [exact Hy_in_sub | exact Ryx].
  Qed.

  Lemma MAX_is_antichain : forall sub,
    Inhabited A (MAX sub) ->
    IsAntichain R (MAX sub).
  Proof.
    intros sub Hinhab. split.
    - exact Hinhab.
    - intros x y Hx Hy Hcomp.
      destruct Hx as [Hx_in_sub Hx_max].
      destruct Hy as [Hy_in_sub Hy_max].
      destruct Hcomp as [Rxy | Ryx].
      + symmetry. apply Hx_max; [exact Hy_in_sub | exact Rxy].
      + apply Hy_max; [exact Hx_in_sub | exact Ryx].
  Qed.

  Lemma Above_is_sub_implies_MIN : forall (sub la : Ensemble A),
    Included A la sub ->
    IsAntichain R la ->
    Intersection A sub (Above R la) = sub ->
    Included A la (MIN sub).
  Proof.
    intros sub la Hincl Hanti Heq.
    intros x Hx.
    split; [apply Hincl; exact Hx |].
    intros y Hy_in Ryx.
    assert (Hy_above: In A (Above R la) y).
    {
      assert (Hy_inter: In A (Intersection A sub (Above R la)) y).
      { rewrite Heq. exact Hy_in. }
      destruct Hy_inter as [y' Hy_in_sub Hy_above_loc]. exact Hy_above_loc.
    }
    unfold Above in Hy_above.
    destruct Hy_above as [z [Hz Rzy]].
    destruct Hanti as [Hinhab Hanti_incomp].
    assert (Rzx : R z x).
    { apply poset_trans with (y := y); [exact Rzy | exact Ryx]. }
    assert (Hzx : z = x).
    { apply Hanti_incomp; [exact Hz | exact Hx | left; exact Rzx]. }
    rewrite Hzx in Rzy.
    symmetry. apply poset_antisym; [exact Rzy | exact Ryx].
  Qed.

  Lemma Below_is_sub_implies_MAX : forall (sub la : Ensemble A),
    Included A la sub ->
    IsAntichain R la ->
    Intersection A sub (Below R la) = sub ->
    Included A la (MAX sub).
  Proof.
    intros sub la Hincl Hanti Heq.
    intros x Hx.
    split; [apply Hincl; exact Hx |].
    intros y Hy_in Rxy.
    assert (Hy_below: In A (Below R la) y).
    {
      assert (Hy_inter: In A (Intersection A sub (Below R la)) y).
      { rewrite Heq. exact Hy_in. }
      destruct Hy_inter as [y' Hy_in_sub Hy_below_loc]. exact Hy_below_loc.
    }
    unfold Below in Hy_below.
    destruct Hy_below as [z [Hz Ryz]].
    destruct Hanti as [Hinhab Hanti_incomp].
    assert (Rxz : R x z).
    { apply poset_trans with (y := y); [exact Rxy | exact Ryz]. }
    assert (Hxz : x = z).
    { apply Hanti_incomp; [exact Hx | exact Hz | left; exact Rxz]. }
    rewrite <- Hxz in Ryz.
    apply poset_antisym; [exact Ryz | exact Rxy].
  Qed.

  Lemma maximal_antichain_in_MIN : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A la (MIN sub) ->
    MIN sub = la.
  Proof.
    intros sub la w Hla Hincl.
    destruct Hla as [Hanti Hla_sub Hcard Hmax].
    apply Extensionality_Ensembles.
    intro z. split; intro Hz.
    - apply NNPP. intro Hz_not_la.
      assert (Hanti_add : IsAntichain R (Add A la z)).
      {
        split.
        - apply Inhabited_intro with z. unfold Add. apply Union_intror. apply In_singleton.
        - intros x y Hx Hy Hcomp.
          unfold Add in Hx, Hy.
          inversion Hx as [x' x_la | x' x_z]; inversion Hy as [y' y_la | y' y_z]; subst.
          + destruct Hanti as [Hinhab Hanti_incomp]. apply Hanti_incomp; [exact x_la | exact y_la | exact Hcomp].
          + inversion y_z; subst.
            assert (x_min: In A (MIN sub) x). { apply Hincl. exact x_la. }
            destruct x_min as [_ Hx_is_min].
            destruct Hz as [Hz_sub Hz_is_min].
            destruct Hcomp as [Rxz | Rzx].
            * apply Hz_is_min; [apply Hla_sub; exact x_la | exact Rxz].
            * symmetry. apply Hx_is_min; [exact Hz_sub | exact Rzx].
          + inversion x_z; subst.
            assert (y_min: In A (MIN sub) y). { apply Hincl. exact y_la. }
            destruct y_min as [_ Hy_is_min].
            destruct Hz as [Hz_sub Hz_is_min].
            destruct Hcomp as [Rzy | Ryz].
            * apply Hy_is_min; [exact Hz_sub | exact Rzy].
            * symmetry. apply Hz_is_min; [apply Hla_sub; exact y_la | exact Ryz].
          + inversion x_z; inversion y_z; subst; reflexivity.
      }
      assert (Hcard_add : cardinal A (Add A la z) (S w)).
      { apply card_add; [exact Hcard | exact Hz_not_la]. }
      assert (Hcontra: S w <= w).
      { apply Hmax with (s := Add A la z).
        - exact Hanti_add.
        - intros x Hx. unfold Add in Hx. inversion Hx as [x' x_la | x' x_z]; subst.
          + apply Hla_sub; exact x_la.
          + inversion x_z; subst. destruct Hz as [Hz_sub _]. exact Hz_sub.
        - exact Hcard_add.
      }
      lia.
    - apply Hincl; exact Hz.
  Qed.

  Lemma maximal_antichain_in_MAX : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A la (MAX sub) ->
    MAX sub = la.
  Proof.
    intros sub la w Hla Hincl.
    destruct Hla as [Hanti Hla_sub Hcard Hmax].
    apply Extensionality_Ensembles.
    intro z. split; intro Hz.
    - apply NNPP. intro Hz_not_la.
      assert (Hanti_add : IsAntichain R (Add A la z)).
      {
        split.
        - apply Inhabited_intro with z. unfold Add. apply Union_intror. apply In_singleton.
        - intros x y Hx Hy Hcomp.
          unfold Add in Hx, Hy.
          inversion Hx as [x' x_la | x' x_z]; inversion Hy as [y' y_la | y' y_z]; subst.
          + destruct Hanti as [Hinhab Hanti_incomp]. apply Hanti_incomp; [exact x_la | exact y_la | exact Hcomp].
          + inversion y_z; subst.
            assert (x_max: In A (MAX sub) x). { apply Hincl. exact x_la. }
            destruct x_max as [_ Hx_is_max].
            destruct Hz as [Hz_sub Hz_is_max].
            destruct Hcomp as [Rxz | Rzx].
            * symmetry. apply Hx_is_max; [exact Hz_sub | exact Rxz].
            * apply Hz_is_max; [apply Hla_sub; exact x_la | exact Rzx].
          + inversion x_z; subst.
            assert (y_max: In A (MAX sub) y). { apply Hincl. exact y_la. }
            destruct y_max as [_ Hy_is_max].
            destruct Hz as [Hz_sub Hz_is_max].
            destruct Hcomp as [Rzy | Ryz].
            * symmetry. apply Hz_is_max; [apply Hla_sub; exact y_la | exact Rzy].
            * apply Hy_is_max; [exact Hz_sub | exact Ryz].
          + inversion x_z; inversion y_z; subst; reflexivity.
      }
      assert (Hcard_add : cardinal A (Add A la z) (S w)).
      { apply card_add; [exact Hcard | exact Hz_not_la]. }
      assert (Hcontra: S w <= w).
      { apply Hmax with (s := Add A la z).
        - exact Hanti_add.
        - intros x Hx. unfold Add in Hx. inversion Hx as [x' x_la | x' x_z]; subst.
          + apply Hla_sub; exact x_la.
          + inversion x_z; subst. destruct Hz as [Hz_sub _]. exact Hz_sub.
        - exact Hcard_add.
      }
      lia.
    - apply Hincl; exact Hz.
  Qed.

  Lemma Above_strict_subset_if_not_MIN : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    la <> MIN sub ->
    exists z, In A sub z /\ ~ In A (Intersection A sub (Above R la)) z.
  Proof.
    intros sub la w Hla Hneq.
    pose proof Hla as Hla_copy.
    destruct Hla_copy as [Hanti Hla_sub Hcard Hmax].
    apply strict_subset_exists_diff with (A_set := Intersection A sub (Above R la)) (B := sub).
    - intros x Hx. destruct Hx as [y Hx_sub Hx_above]. exact Hx_sub.
    - intro Heq. apply Hneq. symmetry.
      apply maximal_antichain_in_MIN with (w := w).
      + exact Hla.
      + apply Above_is_sub_implies_MIN; try assumption.
  Qed.

  Lemma Below_strict_subset_if_not_MAX : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    la <> MAX sub ->
    exists z, In A sub z /\ ~ In A (Intersection A sub (Below R la)) z.
  Proof.
    intros sub la w Hla Hneq.
    pose proof Hla as Hla_copy.
    destruct Hla_copy as [Hanti Hla_sub Hcard Hmax].
    apply strict_subset_exists_diff with (A_set := Intersection A sub (Below R la)) (B := sub).
    - intros x Hx. destruct Hx as [y Hx_sub Hx_below]. exact Hx_sub.
    - intro Heq. apply Hneq. symmetry.
      apply maximal_antichain_in_MAX with (w := w).
      + exact Hla.
      + apply Below_is_sub_implies_MAX; try assumption.
  Qed.

  Lemma la_is_largest_in_sub_above : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    IsLargestAntichain R (Intersection A sub (Above R la)) la w.
  Proof.
    intros sub la w Hla.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    split.
    - exact Hanti.
    - intros x Hx. split.
      + apply Hincl. exact Hx.
      + unfold Above. exists x. split; [exact Hx | apply poset_refl].
    - exact Hcard.
    - intros s n_s Hs_anti Hs_incl Hs_card.
      apply Hmax with (s := s); try assumption.
      intros x Hx. destruct (Hs_incl x Hx) as [x' Hx_sub _]. exact Hx_sub.
  Qed.

  Lemma la_is_largest_in_sub_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    IsLargestAntichain R (Intersection A sub (Below R la)) la w.
  Proof.
    intros sub la w Hla.
    destruct Hla as [Hanti Hincl Hcard Hmax].
    split.
    - exact Hanti.
    - intros x Hx. split.
      + apply Hincl. exact Hx.
      + unfold Below. exists x. split; [exact Hx | apply poset_refl].
    - exact Hcard.
    - intros s n_s Hs_anti Hs_incl Hs_card.
      apply Hmax with (s := s); try assumption.
      intros x Hx. destruct (Hs_incl x Hx) as [x' Hx_sub _]. exact Hx_sub.
  Qed.

  (* ========================================================================= *)
  (* Finite Poset Lemmas                                                      *)
  (* ========================================================================= *)

  (** Bridge: Subtract A sub x has the same cardinality as cardinal_remove result *)
  Lemma cardinal_subtract_elem : forall (sub : Ensemble A) n x,
    In A sub x ->
    cardinal A sub (S n) ->
    cardinal A (Subtract A sub x) n.
  Proof.
    intros sub n x Hx Hcard.
    apply cardinal_extensional_poly with (A_set := fun y => In A sub y /\ y <> x).
    - intro y. unfold Subtract, Setminus. split.
      + intros [H1 H2]. split. exact H1. intro Hc. apply H2. inversion Hc. reflexivity.
      + intros [H1 H2]. split. exact H1. intro Hc. apply H2. subst. apply In_singleton.
    - exact (cardinal_remove A sub x n Hx Hcard).
  Qed.

  (** Helper: In Subtract characterization *)
  Lemma in_subtract_iff : forall (sub : Ensemble A) x y,
    In A (Subtract A sub x) y <-> (In A sub y /\ y <> x).
  Proof.
    intros sub x y. unfold Subtract, Setminus. split.
    - intros [H1 H2]. split. exact H1. intro Heq. apply H2. subst. apply In_singleton.
    - intros [H1 H2]. split. exact H1. intro Hc. apply H2. inversion Hc. reflexivity.
  Qed.

  (** If R x y and x ≠ y and x ∈ sub, then y is not minimal in sub *)
  Lemma not_in_MIN_from_R : forall (sub : Ensemble A) x y,
    In A sub x -> R x y -> x <> y -> ~ In A (MIN sub) y.
  Proof.
    intros sub x y Hx Rxy Hne Hmin.
    destruct Hmin as [_ Hmin_prop].
    specialize (Hmin_prop x Hx Rxy).
    exact (Hne Hmin_prop).
  Qed.

  (** If R x y and x ≠ y and y ∈ sub, then x is not maximal in sub *)
  Lemma not_in_MAX_from_R : forall (sub : Ensemble A) x y,
    In A sub y -> R x y -> x <> y -> ~ In A (MAX sub) x.
  Proof.
    intros sub x y Hy Rxy Hne Hmax.
    destruct Hmax as [_ Hmax_prop].
    specialize (Hmax_prop y Hy Rxy).
    exact (Hne (eq_sym Hmax_prop)).
  Qed.

  (** A subset of an antichain (with Inhabited hypothesis) is an antichain *)
  Lemma subtract_antichain : forall (la : Ensemble A) x,
    IsAntichain R la ->
    Inhabited A (Subtract A la x) ->
    IsAntichain R (Subtract A la x).
  Proof.
    intros la x Hanti Hinhab.
    destruct Hanti as [_ Hanti_incomp].
    constructor.
    - exact Hinhab.
    - intros a b Ha Hb Hcomp.
      apply in_subtract_iff in Ha. destruct Ha as [Ha_in _].
      apply in_subtract_iff in Hb. destruct Hb as [Hb_in _].
      apply Hanti_incomp; assumption.
  Qed.

  (** In a finite subposet, every element is below some maximal element *)
  Lemma exists_max_above : forall n (sub : Ensemble A) x,
    cardinal A sub n ->
    In A sub x ->
    exists y, In A (MAX sub) y /\ R x y.
  Proof.
    induction n as [| k IH]; intros sub x Hcard Hx.
    - (* n = 0: empty, contradiction *)
      inversion Hcard. subst. inversion Hx.
    - (* n = S k *)
      destruct (classic (In A (MAX sub) x)) as [Hmax | Hnmax].
      + (* x is already maximal *)
        exists x. split; [exact Hmax | apply poset_refl].
      + (* x is not maximal: find strict successor z *)
        assert (Hnmax_prop : exists z, In A sub z /\ R x z /\ z <> x).
        { unfold MAX in Hnmax.
          assert (Hnotand : ~ (In A sub x /\ forall y, In A sub y -> R x y -> y = x)).
          { exact Hnmax. }
          apply not_and_or in Hnotand.
          destruct Hnotand as [Habs | Hnot_max].
          - contradiction.
          - apply not_all_ex_not in Hnot_max.
            destruct Hnot_max as [z Hz].
            apply imply_to_and in Hz. destruct Hz as [Hz_sub Hnot].
            apply imply_to_and in Hnot. destruct Hnot as [Rxz Hne].
            exists z. exact (conj Hz_sub (conj Rxz (fun H => Hne H))). }
        destruct Hnmax_prop as [z [Hz_sub [Rxz Hz_ne]]].
        (* Apply IH to sub' = Subtract sub x with element z *)
        assert (Hcard' : cardinal A (Subtract A sub x) k).
        { apply cardinal_subtract_elem; assumption. }
        assert (Hz_sub' : In A (Subtract A sub x) z).
        { apply in_subtract_iff. exact (conj Hz_sub Hz_ne). }
        destruct (IH (Subtract A sub x) z Hcard' Hz_sub') as [y [Hy_max Rzy]].
        exists y.
        split.
        * (* Show y ∈ MAX sub *)
          destruct Hy_max as [Hy_sub' Hy_max_prop].
          apply in_subtract_iff in Hy_sub'. destruct Hy_sub' as [Hy_sub Hy_ne_x].
          split.
          -- exact Hy_sub.
          -- intros w Hw_sub Ryw.
             destruct (classic (w = x)) as [Heq | Hne].
             ++ (* w = x: R y x leads to y = x, contradiction *)
                subst w.
                assert (Rxy : R x y).
                { apply poset_trans with (y := z); assumption. }
                assert (Hyx : y = x).
                { apply poset_antisym; assumption. }
                exact (False_ind _ (Hy_ne_x Hyx)).
             ++ (* w ≠ x: w ∈ sub', apply Hy_max_prop *)
                assert (Hw_sub' : In A (Subtract A sub x) w).
                { apply in_subtract_iff. exact (conj Hw_sub Hne). }
                exact (Hy_max_prop w Hw_sub' Ryw).
        * (* R x y by transitivity *)
          apply poset_trans with (y := z); assumption.
  Qed.

  (** In a finite subposet, every element is above some minimal element *)
  Lemma exists_min_below : forall n (sub : Ensemble A) x,
    cardinal A sub n ->
    In A sub x ->
    exists y, In A (MIN sub) y /\ R y x.
  Proof.
    induction n as [| k IH]; intros sub x Hcard Hx.
    - inversion Hcard. subst. inversion Hx.
    - destruct (classic (In A (MIN sub) x)) as [Hmin | Hnmin].
      + exists x. split; [exact Hmin | apply poset_refl].
      + assert (Hnmin_prop : exists z, In A sub z /\ R z x /\ z <> x).
        { unfold MIN in Hnmin.
          assert (Hnotand : ~ (In A sub x /\ forall y, In A sub y -> R y x -> y = x)).
          { exact Hnmin. }
          apply not_and_or in Hnotand.
          destruct Hnotand as [Habs | Hnot_min].
          - contradiction.
          - apply not_all_ex_not in Hnot_min.
            destruct Hnot_min as [z Hz].
            apply imply_to_and in Hz. destruct Hz as [Hz_sub Hnot].
            apply imply_to_and in Hnot. destruct Hnot as [Rzx Hne].
            exists z. exact (conj Hz_sub (conj Rzx (fun H => Hne H))). }
        destruct Hnmin_prop as [z [Hz_sub [Rzx Hz_ne]]].
        assert (Hcard' : cardinal A (Subtract A sub x) k).
        { apply cardinal_subtract_elem; assumption. }
        assert (Hz_sub' : In A (Subtract A sub x) z).
        { apply in_subtract_iff. exact (conj Hz_sub Hz_ne). }
        destruct (IH (Subtract A sub x) z Hcard' Hz_sub') as [y [Hy_min Ryz]].
        exists y.
        split.
        * destruct Hy_min as [Hy_sub' Hy_min_prop].
          apply in_subtract_iff in Hy_sub'. destruct Hy_sub' as [Hy_sub Hy_ne_x].
          split.
          -- exact Hy_sub.
          -- intros w Hw_sub Rwx.
             destruct (classic (w = x)) as [Heq | Hne].
             ++ subst w.
                assert (Ryx : R y x).
                { apply poset_trans with (y := z); assumption. }
                assert (Hxy : y = x).
                { apply poset_antisym; assumption. }
                exact (False_ind _ (Hy_ne_x Hxy)).
             ++ assert (Hw_sub' : In A (Subtract A sub x) w).
                { apply in_subtract_iff. exact (conj Hw_sub Hne). }
                exact (Hy_min_prop w Hw_sub' Rwx).
        * apply poset_trans with (y := z); assumption.
  Qed.

  Lemma merge_covers : forall (sub la : Ensemble A) (w : nat) C_above C_below,
    IsLargestAntichain R sub la w ->
    IsChainCover R (Intersection A sub (Above R la)) C_above ->
    cardinal (Ensemble A) C_above w ->
    IsChainCover R (Intersection A sub (Below R la)) C_below ->
    cardinal (Ensemble A) C_below w ->
    exists C_merged, IsChainCover R sub C_merged /\ cardinal (Ensemble A) C_merged w.
  Proof.
    admit.
  Admitted.

  Lemma dilworth_case1 : forall n (sub la : Ensemble A) (w : nat),
    cardinal A sub n ->
    w >= 2 ->
    IsLargestAntichain R sub la w ->
    la <> MIN sub ->
    la <> MAX sub ->
    (forall n' (sub' la' : Ensemble A) (w' : nat),
       n' < n -> cardinal A sub' n' ->
       IsLargestAntichain R sub' la' w' ->
       {cover : Ensemble (Ensemble A) | IsChainCover R sub' cover /\ cardinal (Ensemble A) cover w'}) ->
    {cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w}.
  Proof.
    intros n sub la w Hsub_card Hw Hla Hneq_min Hneq_max IH.
    
    assert (H_above_strict : exists z, In A sub z /\ ~ In A (Intersection A sub (Above R la)) z).
    { apply Above_strict_subset_if_not_MIN with (w := w); auto. }
    assert (H_above_incl : Included A (Intersection A sub (Above R la)) sub).
    { intros x Hx. destruct Hx as [x' Hsub _]. exact Hsub. }
    assert (H_exists_m_above : exists m, cardinal A (Intersection A sub (Above R la)) m).
    { apply subset_has_cardinal with (B := sub) (n := n); auto. }
    apply constructive_indefinite_description in H_exists_m_above.
    destruct H_exists_m_above as [m_above Hm_above].
    assert (Hm_above_lt : m_above < n).
    { apply strict_subset_cardinal with (U := A) (A_set := Intersection A sub (Above R la)) (B := sub).
      - exact H_above_incl.
      - exact H_above_strict.
      - exact Hm_above.
      - exact Hsub_card. }
      
    assert (H_below_strict : exists z, In A sub z /\ ~ In A (Intersection A sub (Below R la)) z).
    { apply Below_strict_subset_if_not_MAX with (w := w); auto. }
    assert (H_below_incl : Included A (Intersection A sub (Below R la)) sub).
    { intros x Hx. destruct Hx as [x' Hsub _]. exact Hsub. }
    assert (H_exists_m_below : exists m, cardinal A (Intersection A sub (Below R la)) m).
    { apply subset_has_cardinal with (B := sub) (n := n); auto. }
    apply constructive_indefinite_description in H_exists_m_below.
    destruct H_exists_m_below as [m_below Hm_below].
    assert (Hm_below_lt : m_below < n).
    { apply strict_subset_cardinal with (U := A) (A_set := Intersection A sub (Below R la)) (B := sub).
      - exact H_below_incl.
      - exact H_below_strict.
      - exact Hm_below.
      - exact Hsub_card. }
      
    assert (Hla_above : IsLargestAntichain R (Intersection A sub (Above R la)) la w).
    { apply la_is_largest_in_sub_above; exact Hla. }
    destruct (IH m_above (Intersection A sub (Above R la)) la w Hm_above_lt Hm_above Hla_above) as [C_above H_C_above].
    
    assert (Hla_below : IsLargestAntichain R (Intersection A sub (Below R la)) la w).
    { apply la_is_largest_in_sub_below; exact Hla. }
    destruct (IH m_below (Intersection A sub (Below R la)) la w Hm_below_lt Hm_below Hla_below) as [C_below H_C_below].

    destruct H_C_above as [Hcov_above Hcard_above].
    destruct H_C_below as [Hcov_below Hcard_below].
    assert (H_merge: exists C_merged, IsChainCover R sub C_merged /\ cardinal (Ensemble A) C_merged w).
    { apply merge_covers with (la := la) (C_above := C_above) (C_below := C_below); auto. }
    
    apply constructive_indefinite_description in H_merge.
    exact H_merge.
  Qed.

  (* This lemma will be replaced by exists_comparable_min_max_ne in Block 4.
     Stub with admit until then. *)
  Lemma exists_comparable_min_max : forall (sub la : Ensemble A) (w n : nat),
    cardinal A sub n ->
    w >= 2 ->
    IsLargestAntichain R sub la w ->
    (forall la_ex : Ensemble A, IsLargestAntichain R sub la_ex w -> la_ex = MIN sub \/ la_ex = MAX sub) ->
    exists x y, In A (MIN sub) x /\ In A (MAX sub) y /\ x <> y /\ R x y.
  Proof.
    admit.
  Admitted.

  Lemma width_decreases_when_removing_extremes : forall (sub la : Ensemble A) (w n : nat) (x y : A),
    cardinal A sub n ->
    w >= 2 ->
    IsLargestAntichain R sub la w ->
    In A (MIN sub) x ->
    In A (MAX sub) y ->
    x <> y ->
    R x y ->
    (forall la_ex : Ensemble A, IsLargestAntichain R sub la_ex w -> la_ex = MIN sub \/ la_ex = MAX sub) ->
    exists la', IsLargestAntichain R (Subtract A (Subtract A sub x) y) la' (w - 1).
  Proof.
    intros sub la w n x y Hcard_n Hw Hla Hsub_x Hsub_y Hneq_xy Hxy H_extremal.
    assert (H_la_choice : la = MIN sub \/ la = MAX sub).
    { apply H_extremal. assumption. }
    destruct H_la_choice as [Hla_min | Hla_max].
    - (* la = MIN sub *)
      exists (Subtract A la x).
      admit.
    - (* la = MAX sub *)
      exists (Subtract A la y).
      admit.
  Admitted.

  Lemma add_chain_to_cover : forall (sub : Ensemble A) (w n : nat) (x y : A) C_reduced,
    cardinal A sub n ->
    w >= 2 ->
    In A sub x ->
    In A sub y ->
    x <> y ->
    R x y ->
    IsChainCover R (Subtract A (Subtract A sub x) y) C_reduced ->
    cardinal (Ensemble A) C_reduced (w - 1) ->
    exists C_full, IsChainCover R sub C_full /\ cardinal (Ensemble A) C_full w.
  Proof.
    intros sub w n x y C_reduced Hcard_n Hw Hsub_x Hsub_y Hneq Hxy Hcov_reduced Hcard_reduced.
    exists (Add (Ensemble A) C_reduced (Couple A x y)).
    split.
    - (* IsChainCover *)
      destruct Hcov_reduced as [Hchains Hincluded Hcovers].
      constructor.
      + (* chain_cover_chains *)
        intros c Hc. inversion Hc as [c' Hc_in | c' Hc_eq]; subst.
        * apply Hchains. exact Hc_in.
        * inversion Hc_eq. subst. 
          constructor.
          -- constructor 1 with x. apply Couple_l.
          -- intros z1 z2 Hz1 Hz2. inversion Hz1; inversion Hz2; subst.
             ++ left. apply poset_refl.
             ++ left. exact Hxy.
             ++ right. exact Hxy.
             ++ left. apply poset_refl.
      + (* chain_cover_included *)
        intros c Hc z Hz. inversion Hc as [c' Hc_in | c' Hc_eq]; subst.
        * apply Hincluded in Hc_in. apply Hc_in in Hz.
          unfold Subtract, Setminus in Hz. destruct Hz as [[Hz_sub _] _]. exact Hz_sub.
        * inversion Hc_eq. subst c. inversion Hz; subst.
          -- exact Hsub_x.
          -- exact Hsub_y.
      + (* chain_cover_covers *)
        intros z Hz. 
        destruct (classic (z = x \/ z = y)) as [Hz_xy | Hz_not_xy].
        * exists (Couple A x y). split.
          -- apply Union_intror. apply In_singleton.
          -- destruct Hz_xy. 
             ++ subst. apply Couple_l.
             ++ subst. apply Couple_r.
        * assert (Hz_sub: In A (Subtract A (Subtract A sub x) y) z).
          { unfold Subtract, Setminus. repeat split.
            - exact Hz.
            - intro Hx_eq. apply Hz_not_xy. left. inversion Hx_eq. reflexivity.
            - intro Hy_eq. apply Hz_not_xy. right. inversion Hy_eq. reflexivity. }
          apply Hcovers in Hz_sub. destruct Hz_sub as [c [Hc_in Hc_z]].
          exists c. split.
          -- apply Union_introl. exact Hc_in.
          -- exact Hc_z.
    - (* cardinal w *)
      assert (Hnotin: ~ In (Ensemble A) C_reduced (Couple A x y)).
      { intro Hcontra. 
        destruct Hcov_reduced as [Hchains Hincluded Hcovers].
        assert (Hsub_x_sub : In A (Subtract A (Subtract A sub x) y) x).
        { apply Hincluded with (c := Couple A x y).
          - exact Hcontra.
          - apply Couple_l. }
        unfold Subtract, Setminus in Hsub_x_sub. destruct Hsub_x_sub as [[_ Hnotx] _].
        apply Hnotx. apply In_singleton.
      }
      assert (Hcard : cardinal (Ensemble A) (Add (Ensemble A) C_reduced (Couple A x y)) (S (w - 1))).
      { apply card_add; assumption. }
      assert (Hweq : S (w - 1) = w). { lia. }
      rewrite Hweq in Hcard. exact Hcard.
  Qed.

  Lemma dilworth_case2 : forall n (sub la : Ensemble A) (w : nat),
    cardinal A sub n ->
    w >= 2 ->
    IsLargestAntichain R sub la w ->
    (forall (la_ex : Ensemble A), IsLargestAntichain R sub la_ex w -> la_ex = MIN sub \/ la_ex = MAX sub) ->
    (forall n' (sub' la' : Ensemble A) (w' : nat),
      n' < n ->
      cardinal A sub' n' ->
      IsLargestAntichain R sub' la' w' ->
      { cover : Ensemble (Ensemble A) | IsChainCover R sub' cover /\ cardinal (Ensemble A) cover w' }) ->
    { cover : Ensemble (Ensemble A) | IsChainCover R sub cover /\ cardinal (Ensemble A) cover w }.
  Proof.
    intros n sub la w Hsub_card Hw_ge_2 Hla H_extremal IH.
    assert (Hex : exists x y, In A (MIN sub) x /\ In A (MAX sub) y /\ x <> y /\ R x y).
    { apply exists_comparable_min_max with (la := la) (n := n) (w := w); auto. }
    apply constructive_indefinite_description in Hex. destruct Hex as [x Hex].
    apply constructive_indefinite_description in Hex. destruct Hex as [y [Hx_min [Hy_max [Hneq Rxy]]]].
    
    set (sub_reduced := Subtract A (Subtract A sub x) y).
    
    assert (H_exists_w_dec : exists la', IsLargestAntichain R sub_reduced la' (w - 1)).
    { apply width_decreases_when_removing_extremes with (la := la) (n := n) (x := x) (y := y); auto. }
    apply constructive_indefinite_description in H_exists_w_dec.
    destruct H_exists_w_dec as [la' Hla'].

    assert (H_reduced_incl : Included A sub_reduced sub).
    { intros z Hz. unfold sub_reduced, Subtract, Setminus in Hz. destruct Hz as [[Hz_sub _] _]. exact Hz_sub. }
    
    assert (H_exists_m : exists m, cardinal A sub_reduced m).
    { apply subset_has_cardinal with (B := sub) (n := n); auto. }
    apply constructive_indefinite_description in H_exists_m.
    destruct H_exists_m as [m Hm].
    
    assert (Hm_lt_n : m < n).
    { apply strict_subset_cardinal with (U := A) (A_set := sub_reduced) (B := sub).
      - exact H_reduced_incl.
      - exists x. split.
        + destruct Hx_min as [Hx_sub _]. exact Hx_sub.
        + unfold sub_reduced, Subtract, Setminus. intro Hcontra. destruct Hcontra as [Hcontra_x _]. destruct Hcontra_x as [_ Hnot_x]. apply Hnot_x. reflexivity.
      - exact Hm.
      - exact Hsub_card. }
      
    destruct (IH m sub_reduced la' (w - 1) Hm_lt_n Hm Hla') as [C_reduced H_C_reduced].
    destruct H_C_reduced as [Hcov_red Hcard_red].
    
    assert (H_add_chain : exists C_full, IsChainCover R sub C_full /\ cardinal (Ensemble A) C_full w).
    { apply add_chain_to_cover with (n := n) (x := x) (y := y) (C_reduced := C_reduced); auto.
      - destruct Hx_min as [Hx_in _]. exact Hx_in.
      - destruct Hy_max as [Hy_in _]. exact Hy_in. }
      
    apply constructive_indefinite_description in H_add_chain.
    exact H_add_chain.
  Qed.

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
    intros n sub la w Hcard_n Hw_ge_2 Hla IH.
    
    destruct (ClassicalEpsilon.excluded_middle_informative (forall la_ex, IsLargestAntichain R sub la_ex w -> (la_ex = MIN sub \/ la_ex = MAX sub))) as [H_extremal | H_not_extremal].
    - (* Case 2: Every maximum antichain is either MIN or MAX. *)
      apply (dilworth_case2 n sub la w Hcard_n Hw_ge_2 Hla H_extremal IH).
      
    - (* Case 1: 'la' is a maximum antichain of size w, and 'la' != MIN and 'la' != MAX *)
      assert (Hex: exists la_ex, IsLargestAntichain R sub la_ex w /\ ~ (la_ex = MIN sub \/ la_ex = MAX sub)).
      {
        apply not_all_ex_not in H_not_extremal. destruct H_not_extremal as [la_ex H_not_impl].
        exists la_ex. apply imply_to_and in H_not_impl. exact H_not_impl.
      }
      apply ClassicalEpsilon.constructive_indefinite_description in Hex.
      destruct Hex as [la_ex [Hla_ex Hnot_or]].
      apply not_or_and in Hnot_or.
      destruct Hnot_or as [Hneq_min Hneq_max].
      apply (dilworth_case1 n sub la_ex w Hcard_n Hw_ge_2 Hla_ex Hneq_min Hneq_max IH).
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

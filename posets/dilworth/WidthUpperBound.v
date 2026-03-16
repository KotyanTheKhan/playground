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

  Lemma exists_comparable_min_max : forall (sub la : Ensemble A) (w n : nat),
    cardinal A sub n ->
    w >= 2 ->
    IsLargestAntichain R sub la w ->
    (forall la_ex : Ensemble A, IsLargestAntichain R sub la_ex w -> la_ex = MIN sub \/ la_ex = MAX sub) ->
    exists x y, In A (MIN sub) x /\ In A (MAX sub) y /\ x <> y /\ R x y.
  Proof.
    intros sub la w n Hcard_n Hw Hla H_extremal.
    assert (H_la_choice : la = MIN sub \/ la = MAX sub).
    { apply H_extremal. exact Hla. }
    destruct Hla as [Hanti Hla_sub Hcard Hmax].
    destruct Hanti as [Hinhab Hanti_incomp].
    (* Get two distinct elements a, b from la (since w >= 2) *)
    assert (H_la_ge2 : exists a b, In A la a /\ In A la b /\ a <> b).
    {
      assert (Hw2 : 2 <= w) by exact Hw.
      (* invert twice using the cardinal structure *)
      set (la_inner := la) in Hcard.
      destruct Hcard as [| A1 n1 H1 z1 Hz1_notin] eqn:E1.
      - lia.
      - (* la = Add A1 z1, |A1| = n1, w = S n1 *)
        destruct H1 as [| A2 n2 H2 z2 Hz2_notin] eqn:E2.
        + lia.
        + exists z2. exists z1.
          repeat split.
          * apply Union_introl. apply Union_intror. apply In_singleton.
          * apply Union_intror. apply In_singleton.
          * intro Heq_zz. subst z2.
            exact (Hz1_notin (Union_intror _ _ _ _ (In_singleton _ _ z1))).
    }
    destruct H_la_ge2 as [a [b [Ha_la [Hb_la Hab_neq]]]].
    (* Now: both a, b ∈ la; la ⊆ sub; la is an antichain *)
    assert (Ha_sub : In A sub a). { apply Hla_sub. exact Ha_la. }
    assert (Hb_sub : In A sub b). { apply Hla_sub. exact Hb_la. }
    (* a and b are incomparable since la is an antichain and a ≠ b *)
    assert (Hab_incomp : ~ (R a b \/ R b a)).
    {
      intro Hcomp. apply Hab_neq. apply Hanti_incomp; assumption.
    }
    assert (Hab_not_R_ab : ~ R a b). { intro H. apply Hab_incomp. left. exact H. }
    assert (Hab_not_R_ba : ~ R b a). { intro H. apply Hab_incomp. right. exact H. }
    (* Now we construct x ∈ MIN and y ∈ MAX and prove x <> y and R x y *)
    (* Strategy: for each element of la, look at the chain from the bottom to it.
       Let x be the minimal element of sub below a, and y be the maximal above b.
       But this requires a finite chain argument which we don't have.
       
       Alternative: La = MIN ∨ la = MAX. 
       Case 1: la = MIN. Take x = a ∈ la = MIN, and y = b ∈ la = MIN.
         a and b are both in MIN and incomparable. But any element of MIN
         is comparable to any element of MAX (see below).
         Take any y' ∈ MAX sub (non-empty since sub non-empty). 
         Claim: x = a ≠ y' and R a y'. 
       Case 2: la = MAX. Symmetric.
       
       The claim R a y' where a ∈ MIN, y' ∈ MAX is actually non-trivial without 
       assuming the poset is connected. Let's try: pick x ∈ la = MIN, y = x ∈ MAX?
       No, that's circular.
       
       Actually, the simplest approach: 
       Since la = MIN is an antichain of size w, all elements of MIN are mutually incomparable.
       But since la = MIN is also the LARGEST antichain, anything outside MIN can be added to 
       get a bigger antichain... unless it's comparable to some MIN element.
       
       The key insight: x ∈ MIN sub means ("minimal in sub"). There must be some y ∈ MAX sub 
       reachable from x (finite poset). But we don't have finiteness directly...
       
       Let's use the proof approach: take x = a ∈ MIN, y ∈ MAX.
       Since la = MIN and MAX ≠ MIN (because a and b are incomparable in MIN,
       but MAX has comparable elements via reflexivity), ... this is getting circular.
       
       Actually the real issue is this lemma might not be provable without more hypotheses.
       Let's simply use the weaker approach: *)
    (* Attempt: construct MIN-MAX pair directly from la *)
    (* If la = MIN: all elements of MIN are mutually incomparable, but any element of sub
       not in MIN is above some element of MIN (by definition). Actually, definition of MIN 
       is: x ∈ MIN iff x ∈ sub and for all y ∈ sub, R y x → y = x.
       This does NOT mean all of sub is above MIN elements in a linear way. *)
    (* The lemma as stated requires: exists x y, x ∈ MIN, y ∈ MAX, x ≠ y, R x y.
       This is true in finite posets (every minimal element is below some maximal), but 
       requires a separate finite chain argument. Let us admit this auxiliary claim. *)
    (* For now: use a ∈ la (MIN or MAX) and find corresponding partner *)
    
    (* Take x from MIN; take y from MAX; R x y follows if the poset is such that
       every minimal element is below every maximal element, which only holds in
       special cases. In general: x ∈ MIN, y ∈ MAX, AND x ≤ y is NOT always true
       unless the poset is connected. *)
    
    (* The correct approach: this specific proof obligation (exists_comparable_min_max) 
       requires that since every largest antichain = MIN or MAX, there must exist 
       elements that "bridge" between MIN and MAX. The proof is:
       - la = MIN is the largest antichain
       - Take any a ∈ MIN. Consider b ∈ MAX. 
       - If R a b, done.
       - If ¬ R a b, then a and b are incomparable (since if R b a and b ≠ a, 
         then a is not minimal — contradiction with a ∈ MIN unless b ∉ sub).
       - Actually: b ∈ MAX ⊆ sub and a ∈ MIN ⊆ sub. If R b a and b ≠ a, 
         then b < a, so a is not minimal — contradiction.
       - So either R a b or (¬ R a b and ¬ R b a), i.e., incomparable.
       - If a and b are incomparable, then {a, b} is an antichain of size 2.
       - By IH: there exists a largest antichain of the same size (or bigger) 
         containing both a and b. But this largest antichain = MIN or MAX.
       - If the largest antichain = MIN = la and a ∈ la and b ∈ la, then b ∈ MIN.
         But b ∈ MAX, so b is both min and max. 
         Since b ∈ MIN, for all z ∈ sub, R z b → z = b.
         Since b ∈ MAX, for all z ∈ sub, R b z → z = b.
         So b is an isolated element.
         But then: take any other element c ∈ la = MIN (la has w ≥ 2 elements).
         c and b are incomparable (antichain). c ∈ MIN → for all z ∈ sub, R z c → z = c.
         But b ∈ sub, b ≠ c, and ¬ R b c (since b is incomparable with c). 
         Also ¬ R c b (since b ∈ MAX and the only thing above b is b, so R c b → c = b, contradiction).
         ...This actually works! *)
    
    (* Take x = a ∈ MIN (from la), find y = a itself ∈ MAX? No *)
    (* Let's find y ∈ MAX sub. MIN sub is inhabited, MAX sub must be inhabited too. *)
    assert (H_max_inhabited : Inhabited A (MAX sub)).
    {
      destruct H_la_choice as [Hmin | Hmax_choice].
      - subst la.
        (* la = MIN; MAX sub is inhabited *)
        (* Take a ∈ MIN sub (from Hinhab), and find the maximal element above a *)
        (* This needs chain/Zorn; let's use an indirect argument *)
        (* MAX sub must be inhabited because sub is finite and non-empty *)
        (* We can't prove this without finiteness... *)
        (* But wait: la = MIN = an antichain of size w ≥ 2 ⊆ sub. 
           sub is finite (cardinal A sub n). In a finite poset, every element has a maximal above it. *)
        (* For now, admit this piece *)
        admit.
      - subst la. exact Hinhab.
    }
    assert (H_min_inhabited : Inhabited A (MIN sub)).
    {
      destruct H_la_choice as [Hmin | Hmax_choice].
      - subst la. exact Hinhab.
      - subst la. admit.
    }
    destruct H_min_inhabited as [x Hx_min].
    destruct H_max_inhabited as [y Hy_max].
    exists x. exists y.
    split. { exact Hx_min. }
    split. { exact Hy_max. }
    split.
    - (* x <> y *)
      intro Heq. subst y.
      (* x ∈ MIN ∩ MAX, and la has w ≥ 2 elements *)
      (* If la = MIN: la has another element z ≠ x.
         z ∈ MIN and x ∈ MAX: R x z → z = x (contradiction) and ¬ R z x (z ∈ MIN, z ≠ x means z minimal).
         Actually: z ∈ MIN means for all t ∈ sub, R t z → t = z. So ¬ R x z (since x ≠ z and x ∈ sub).
         And x ∈ MAX means for all t ∈ sub, R x t → t = x. So ¬ R x z (since x ≠ z and z ∈ sub).
         Hmm wait: ¬ R x z follows from z ∈ MIN and x ≠ z (if R x z then by z-is-min, x = z, contra).
         And ¬ R z x follows from x ∈ MAX and z ≠ x (if R z x then by x-MAX, z = x, contra).
         So z and x are incomparable. But z ∈ la and x ∈ la and la is antichain: OK!
         So no direct contradiction yet.
         
         The real issue: if x ∈ MIN s.t. everything above x is x (MAX property),
         then everything in sub is either x or incomparable to x.
         But la has another element z incomparable to x and z ∈ sub.
         Now consider: z ∈ MIN and ¬ R z x. Is MAX sub inhabited with something ≠ x?
         If all of MAX sub = {x}, then x is a global max. But z ∈ MIN and z incomparable to x
         means z is not below x, yet z ∈ sub. Since z ∈ MIN (z is minimal in sub), 
         z ∈ MAX would require R z t → t = z for all t ∈ sub; since x ∉ {z} and 
         R z x requires... *)
      (* Getting complex. Let's use: since w ≥ 2 and la is antichain, pick two distinct elements.
         If la = MIN, pick z ∈ la ≠ x. Then x ∈ MIN ∩ MAX. 
         z ∈ MIN. ¬ R z x (since x ∈ MAX and z ≠ x → R z x implies z = x by MAX).
         AND z ∈ la is an antichain with x ∈ la: ¬(R z x ∨ R x z). 
         Both give ¬ R z x, but also ¬ R x z.
         ¬ R x z: since x ∈ MIN and z ≠ x → R z x → z = x by MIN; but wait, 
         x ∈ MIN means for all t ∈ sub, R t x → t = x. z ∈ sub.
         ¬ R z x follows already from antichain (z, x incomparable by Hanti_incomp).
         So both z, x ∈ la are incomparable, which is fine for antichain. 
         No contradiction yet *)
      (* The contradiction must come from something else. 
         x ∈ MIN ∩ MAX AND la = MIN AND |la| ≥ 2. 
         x ∈ MAX: ∀ t ∈ sub, R x t → t = x.
         z ∈ la = MIN: z ∈ sub.
         If R x z: by MAX, z = x. Contradiction with z ≠ x.
         If ¬ R x z: fine.
         If R z x: by MIN, z = x. Contradiction.
         If ¬ R z x: fine.
         So z and x are incomparable — consistent with antichain.
         Hmm, no direct contradiction.
         
         Wait! We need to use: la = MIN and x ∈ MAX.
         We need to show that if x ∈ MIN ∩ MAX, then for every z ∈ sub incomparable to x,
         ALL chains from z upward (in a finite poset) ...
         
         The problem is we don't have the crucial fact:
         "In a finite poset, every element is below some maximal element"
         without additional finiteness reasoning.
         
         Actually: we DO have cardinal A sub n (finiteness). Let's admit this for now. *)
      admit.
    - (* R x y *)
      destruct Hx_min as [Hx_sub Hx_is_min].
      destruct Hy_max as [Hy_sub Hy_is_max].
      (* NNPP: assume ¬ R x y. Then either R y x (giving y = x by MAX + MIN) or incomparable. *)
      apply NNPP. intro Hnot_Rxy.
      assert (H_not_Ryx : ~ R y x).
      {
        intro HRyx. apply Hnot_Rxy. apply Hx_is_min; [exact Hy_sub | exact HRyx].
      }
      (* x and y are incomparable *)
      (* {x, y} is an antichain of size 2 ≤ w *)
      (* Since x ≠ y (from sub-goal above... but we're in a different sub-goal!) *)
      (* Actually we need x ≠ y here too *)
      assert (H_x_neq_y : x <> y).
      {
        intro Heq_xy. subst. apply Hnot_Rxy. apply poset_refl.
      }
      (* {x, y} is an antichain *)
      assert (H_xy_anti : IsAntichain R (Couple A x y)).
      {
        constructor.
        - exact (Inhabited_intro _ _ x (Couple_l _ _ _)).
        - intros a b Ha Hb Hcomp.
          inversion Ha; inversion Hb; subst.
          + apply poset_antisym. apply poset_refl. apply poset_refl.
          + destruct Hcomp as [H | H].
            * apply Hnot_Rxy in H. contradiction.
            * exact (H_not_Ryx H |> False.elim).
          + destruct Hcomp as [H | H].
            * exact (H_not_Ryx H |> False.elim).
            * apply Hnot_Rxy in H. contradiction.
          + apply poset_antisym. apply poset_refl. apply poset_refl.
      }
      (* {x, y} ⊆ sub *)
      assert (H_xy_sub : Included A (Couple A x y) sub).
      {
        intros z Hz. inversion Hz; subst.
        - exact Hx_sub.
        - exact Hy_sub.
      }
      (* cardinal Couple A x y 2 *)
      assert (H_card_xy : cardinal A (Couple A x y) 2).
      {
        assert (H_pair : Couple A x y = Add A (Singleton A x) y).
        { apply Extensionality_Ensembles. intro z; split; intro Hz.
          - inversion Hz; subst.
            + apply Union_introl. apply In_singleton.
            + apply Union_intror. apply In_singleton.
          - inversion Hz as [z' Hz' | z' Hz'];
            [ inversion Hz'; subst; apply Couple_l
            | inversion Hz'; subst; apply Couple_r ]. }
        rewrite H_pair. apply card_add.
        - apply card_add. constructor. apply In_singleton.
        - intro H. inversion H. exact H_x_neq_y.
      }
      (* By maximality of la, |{x, y}| <= w, i.e., 2 <= w *)
      assert (H_2_le_w : 2 <= w).
      { apply Hmax with (s := Couple A x y); [exact H_xy_anti | exact H_xy_sub | exact H_card_xy]. }
      (* But also by maximality of la, |{x, y}| <= w, and la achieves w *)
      (* Since la is a maximum antichain of cardinality w, {x,y} ⊆ la for some largest antichain *)
      (* Actually: k <= w and w is the max, so 2 <= w is consistent, not a contradiction *)
      (* The real contradiction: la = MIN (or MAX) and x ∈ MIN ∩ la and y ∈ MAX;
         if they're incomparable, then x and y are both in la (by maximality),
         which means y ∈ MIN = la. But if y ∈ MIN, then everything below y is y.
         Since x ∈ sub and ¬ R x y and ¬ R y x, x is incomparable to y...
         But we also need: x ∈ la = MIN and y ∈ la = MIN and they're incomparable — OK.
         Still no direct contradiction.
         
         The real key: in case la = MIN, take ANY element of Max. 
         By our specific choice, y ∈ MAX.
         y ∈ MAX means: ∀ t ∈ sub, R y t → t = y.
         x ∈ MIN = la means: x ∈ la. la = MIN.
         Since we took x from MIN (which = la), x ∈ la.
         
         Now, since {x, y} is antichain of size 2 and la is the LARGEST antichain,
         there exists a largest antichain containing {x, y}... No, la is just one specific max antichain.
         
         But H_extremal says EVERY largest antichain = MIN or MAX.
         So there exists A* (a specific longest antichain that contains {x, y}),
         and A* = MIN or = MAX.
         If A* = MIN: x, y ∈ MIN. y ∈ MIN means ∀ z ∈ sub, R z y → z = y.
           But then: x ∈ sub and (we need R x y to derive a contradiction, but we assumed ¬ R x y)...
         If A* = MAX: x, y ∈ MAX. x ∈ MAX means ∀ z ∈ sub, R x z → z = x.
           x ∈ MIN means ∀ z ∈ sub, R z x → z = x. So x is isolated.
           But is x isolated possible in a poset of width w ≥ 2?
           Isolated means nothing above or below except x... so x is incomparable to everything else.
           But then {x, anything else} is an antichain of size 2 ≤ w.
           Hmm, this is still consistent.
         
         The proof is getting very involved. Let me admit the R x y part for now. *)
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

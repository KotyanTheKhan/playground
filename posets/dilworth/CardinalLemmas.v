From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Classical.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.

Section CardinalLemmas.

  (* ========================================================================= *)
  (* Ensemble Extensionality                                                   *)
  (* ========================================================================= *)

  Lemma Extensionality_Ensembles : 
    forall U (A_set B : Ensemble U), (forall x, In U A_set x <-> In U B x) -> A_set = B.
  Proof.
    intros U A_set B Hext.
    (* Ensembles are functions U -> Prop, so we can use functional extensionality *)
    apply functional_extensionality.
    intro x.
    (* Now we need to show: A_set x = B x, which are both Props *)
    apply propositional_extensionality.
    (* This follows from Hext *)
    apply Hext.
  Qed.

  (* ========================================================================= *)
  (* Cardinal Extensionality                                                   *)
  (* ========================================================================= *)

  Lemma strict_subset_exists_diff : forall (U : Type) (A_set B : Ensemble U),
    Included U A_set B ->
    A_set <> B ->
    exists x, In U B x /\ ~ In U A_set x.
  Proof.
    intros U A_set B Hincl Hneq.
    apply Classical_Pred_Type.not_all_not_ex.
    intro H_all.
    apply Hneq.
    apply Extensionality_Ensembles. intro z; split; intro Hz.
    - apply Hincl. exact Hz.
    - apply NNPP. intro Hnot.
      exact (H_all z (conj Hz Hnot)).
  Qed.

  Lemma cardinal_extensional_poly : forall (U : Type) (A_set B : Ensemble U) n,
    (forall x, In U A_set x <-> In U B x) ->
    cardinal U A_set n ->
    cardinal U B n.
  Proof.
    intros U A_set B n Hext Hcard.
    generalize dependent B.
    induction Hcard as [U0 | A' n' Hcard' IH x Hnotin].
    
    - (* Base case: n = 0, A_set = Empty_set *)
      intros B Hext.
      (* A_set is empty, and B is extensionally equal to A_set, so B is also empty *)
      assert (Hempty_B : forall y, ~ In U B y).
      {
        intros y Hy.
        apply (Hext y) in Hy.
        inversion Hy.
      }
      (* Use Extensionality_Ensembles to show B = Empty_set *)
      assert (HB_eq : B = Empty_set U).
      {
        apply Extensionality_Ensembles. intro z; split; intro Hz.
        - exfalso. apply (Hempty_B z Hz).
        - inversion Hz.
      }
      rewrite HB_eq.
      apply card_empty.
    
    - (* Step case: A_set = Add A' x with cardinal A' n' *)
      intros B Hext.
      (* B is extensionally equal to Add A' x *)
      (* First, show x is in B *)
      assert (Hx_in_B : In U B x).
      {
        apply Hext.
        unfold Add. apply Union_intror. apply In_singleton.
      }
      
      (* Define B' = B \ {x} *)
      pose (B' := fun y => In U B y /\ y <> x).
      
      (* Show B' is extensionally equal to A' *)
      assert (Hext' : forall y, In U A' y <-> In U B' y).
      {
        intro y. split; intro Hy.
        - (* A' → B' *)
          unfold B'. split.
          + apply Hext. unfold Add. apply Union_introl. exact Hy.
          + intro Heq. subst y. contradiction.
        - (* B' → A' *)
          destruct Hy as [Hy_in_B Hy_neq].
          apply Hext in Hy_in_B.
          unfold Add in Hy_in_B.
          inversion Hy_in_B as [y' Hy' | y' Hy']; subst.
          + exact Hy'.
          + inversion Hy'. subst. contradiction.
      }
      
      (* Apply IH to get cardinal B' n' *)
      assert (Hcard_B' : cardinal U B' n').
      {
        apply IH. exact Hext'.
      }
      
      (* Show x is not in B' *)
      assert (Hx_notin_B' : ~ In U B' x).
      {
        unfold B'. intros [_ Hneq]. apply Hneq. reflexivity.
      }
      
      (* Show B = Add B' x *)
      assert (HB_eq : B = Add U B' x).
      {
        apply Extensionality_Ensembles. intro z; split; intro Hz.
        - (* B → Add B' x *)
          destruct (classic (z = x)) as [Heq_x | Hneq_x].
          + subst z. unfold Add. apply Union_intror. apply In_singleton.
          + unfold Add. apply Union_introl. unfold B'. split; assumption.
        - (* Add B' x → B *)
          unfold Add in Hz.
          inversion Hz as [z' Hz' | z' Hz']; subst.
          + unfold B' in Hz'. destruct Hz' as [Hz'_in _]. exact Hz'_in.
          + inversion Hz'. subst. exact Hx_in_B.
      }
      
      (* Now apply card_add *)
      rewrite HB_eq.
      apply card_add; assumption.
  Qed.

  Lemma subset_has_cardinal : forall (U : Type) (A_set B : Ensemble U) n,
    Included U A_set B ->
    cardinal U B n ->
    exists m, cardinal U A_set m.
  Proof.
    intros U A_set B n Hincl Hcard.
    revert A_set Hincl.
    induction Hcard as [U' | B' n' Hcard_B' IH x Hx_notin].
    - (* Base Case: B is Empty_set *)
      intros A_set Hincl.
      exists 0.
      assert (Heq : A_set = Empty_set U).
      {
        apply Extensionality_Ensembles. intro z; split; intro Hz.
        - apply Hincl. exact Hz.
        - inversion Hz.
      }
      rewrite Heq. constructor.
    - (* Inductive Case: B = Add U B' x *)
      intros A_set Hincl.
      destruct (classic (In U A_set x)) as [Hin | Hnotin].
      + (* x is in A_set *)
        set (A_minus := fun y => In U A_set y /\ y <> x).
        assert (Hincl_A_minus : Included U A_minus B').
        {
          intros z Hz. unfold A_minus in Hz.
          destruct Hz as [Hz_A Hz_neq].
          destruct (Hincl z Hz_A) as [ | ].
          - assumption.
          - inversion H. subst. elim Hz_neq. reflexivity.
        }
        destruct (IH A_minus Hincl_A_minus) as [m Hm].
        exists (S m).
        assert (Heq : A_set = Add U A_minus x).
        {
          apply Extensionality_Ensembles. intro z; split; intro Hz.
          - destruct (classic (z = x)) as [Heq_x | Hneq_x].
            + subst. apply Union_intror. apply In_singleton.
            + apply Union_introl. unfold A_minus. split; assumption.
          - unfold Add in Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
            + unfold A_minus in Hz'. destruct Hz' as [Hz_A _]. exact Hz_A.
            + inversion Hz'. subst. exact Hin.
        }
        rewrite Heq. apply card_add.
        * exact Hm.
        * unfold A_minus. intro Hcontra. destruct Hcontra as [_ Hneq_x]. apply Hneq_x. reflexivity.
      + (* x is not in A_set *)
        assert (Hincl_B' : Included U A_set B').
        {
          intros z Hz.
          destruct (Hincl z Hz) as [ | ].
          - assumption.
          - inversion H. subst. contradiction.
        }
        apply IH. exact Hincl_B'.
  Qed.

  Lemma strict_subset_cardinal : forall (U : Type) (A_set B : Ensemble U) n m,
    Included U A_set B ->
    (exists x, In U B x /\ ~ In U A_set x) ->
    cardinal U A_set n ->
    cardinal U B m ->
    n < m.
  Proof.
    intros U A_set B n m Hincl Hex HcardA HcardB.
    apply (incl_st_card_lt U A_set n HcardA B m HcardB).
    unfold Strict_Included. split.
    - exact Hincl.
    - intro Heq. destruct Hex as [x [HxB HxnotA]]. apply HxnotA. rewrite Heq. exact HxB.
  Qed.

End CardinalLemmas.

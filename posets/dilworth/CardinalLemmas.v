From Stdlib Require Import Ensembles Finite_sets Classical.
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
        apply Extensionality_Ensembles.
        intro z. split; intro Hz.
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
        apply Extensionality_Ensembles.
        intro z. split; intro Hz.
        - (* B → Add B' x *)
          destruct (classic (z = x)) as [Heq | Hneq].
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

  (** Generic disjoint-union cardinality. *)
  Lemma cardinal_disjoint_union_gen : forall (U : Type) (S T : Ensemble U) n m,
    (forall x, In U S x -> ~ In U T x) ->
    cardinal U S n ->
    cardinal U T m ->
    cardinal U (Union U S T) (n + m).
  Proof.
    intros U S T n m Hdisj HcardS HcardT.
    revert T m Hdisj HcardT.
    induction HcardS as [| S' n' HcardS' IH a Ha_notin]; intros T m Hdisj HcardT.
    - simpl.
      apply (cardinal_extensional_poly U T); [| exact HcardT].
      intros x. split.
      + intro Hx. apply Union_intror. exact Hx.
      + intro Hx. inversion Hx as [z Hz | z Hz]; subst.
        * inversion Hz.
        * exact Hz.
    - simpl.
      apply (cardinal_extensional_poly U (Add U (Union U S' T) a)).
      + intros x. split.
        * intro Hx.
          inversion Hx as [z Hz | z Hz]; subst.
          -- inversion Hz as [w Hw | w Hw]; subst.
             ++ apply Union_introl. apply Union_introl. exact Hw.
             ++ apply Union_intror. exact Hw.
          -- inversion Hz. subst. apply Union_introl. apply Union_intror. apply In_singleton.
        * intro Hx.
          inversion Hx as [z Hz | z Hz]; subst.
          -- inversion Hz as [w Hw | w Hw]; subst.
             ++ apply Union_introl. apply Union_introl. exact Hw.
             ++ inversion Hw. subst. apply Union_intror. apply In_singleton.
          -- apply Union_introl. apply Union_intror. exact Hz.
      + apply card_add.
        * apply IH.
          -- intros x Hx. exact (Hdisj x (Union_introl _ _ _ _ Hx)).
          -- exact HcardT.
        * intro Hcontra.
          inversion Hcontra as [z Hz | z Hz]; subst.
          -- exact (Ha_notin Hz).
          -- exact (Hdisj a (Union_intror _ _ _ _ (In_singleton _ _)) Hz).
  Qed.

End CardinalLemmas.

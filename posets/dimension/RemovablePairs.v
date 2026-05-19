(** Removable pairs and Trotter's lemma for the proof of Hiraguchi's theorem.
    See docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section RemovablePairs.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Residual set [Residual x y = Full_set A \ {x, y}]. *)
  Definition Residual (x y : A) : Ensemble A :=
    Setminus A (Setminus A (Full_set A) (Singleton A x)) (Singleton A y).

  Lemma Residual_not_x :
    forall x y a, In A (Residual x y) a -> a <> x.
  Proof.
    intros x y a [[_ Hnx] _] Heq. apply Hnx. rewrite Heq. constructor.
  Qed.

  Lemma Residual_not_y :
    forall x y a, In A (Residual x y) a -> a <> y.
  Proof.
    intros x y a [_ Hny] Heq. apply Hny. rewrite Heq. constructor.
  Qed.

  Lemma Residual_intro :
    forall x y a, a <> x -> a <> y -> In A (Residual x y) a.
  Proof.
    intros x y a Hnx Hny. split; [split |].
    - apply Full_intro.
    - intro Hin. inversion Hin; subst. apply Hnx; reflexivity.
    - intro Hin. inversion Hin; subst. apply Hny; reflexivity.
  Qed.

  (** A pair (x, y) is removable iff every linear extension L' of R restricted
      to the residual set lifts to a linear extension L of R that also reverses
      every critical pair of R touching {x, y} (other than (x, y) itself).

      The lift L:
        - extends L' (preserves all of L's orderings on the residual)
        - reverses the pair: L y x
        - handles every other critical pair (p, q) of R: either both endpoints
          are in the residual (so r' will handle it), or L itself reverses
          (p, q). This is the JOINT-CONSISTENCY property that the previous
          design's [extremal_critical_pair_exists] tried — and failed — to
          assert with a different (false) formulation. *)
  Definition IsRemovablePair (x y : A) : Prop :=
    x <> y /\
    forall (L' : {a : A | In A (Residual x y) a} ->
                  {a : A | In A (Residual x y) a} -> Prop),
      IsLinearExtension (fun a b => R (proj1_sig a) (proj1_sig b)) L' ->
      exists L : A -> A -> Prop,
        IsLinearExtension R L /\
        (forall (a b : {a : A | In A (Residual x y) a}),
            L' a b -> L (proj1_sig a) (proj1_sig b)) /\
        L y x /\
        (forall p q : A, IsCriticalPair R p q ->
            (p = x /\ q = y) \/
            (In A (Residual x y) p /\ In A (Residual x y) q) \/
            L q p).

  (** If (x, y) is removable AND incomparable, then dim(R) ≤ dim(R|_S) + 1.

      From any d'-element realizer of R|_{Residual x y} (with at least one
      element), build a (d'+1)-element realizer of R.

      Hypotheses worth noting:
      - [Incomparable R x y]: the natural case for removable pairs in Hiraguchi's
        proof.  Allows the construction of a sole "extra" linear extension
        ordering x < y.  Without this, the lemma can fail when |Residual| ≤ 1
        (e.g. |A|=2 with x, y incomparable has dim 2 but d'+1 = 1).
      - [Inhabited r']: avoids the degenerate d' = 0 case where R|_S might be
        trivially total but R itself need not be.  In Hiraguchi's induction
        (n ≥ 6) the residual has ≥ 4 elements so this is automatic. *)
  Lemma removable_pair_dimension_bound :
    forall (x y : A) (d' : nat),
    Finite A (Full_set A) ->
    Incomparable R x y ->
    IsRemovablePair x y ->
    (exists r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop),
       IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                      R (proj1_sig a) (proj1_sig b)) r' /\
       cardinal _ r' d' /\
       Ensembles.Inhabited _ r') ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
  Proof.
    intros x y d' HfinA Hinc Hrem Hr'_ex.
    destruct Hrem as [Hxy_neq Hrem_prop].
    destruct Hr'_ex as [r' [Hr'_real [Hr'_card Hr'_inh]]].
    set (S' := Residual x y).
    (* Step B: build a linear extension L_extra of R with L_extra x y.
       Since (x, y) are incomparable, TC(R ∪ {(x, y)}) is a poset; extend it. *)
    assert (Hex_Lextra : exists L_extra : A -> A -> Prop,
                          IsLinearExtension R L_extra /\ L_extra x y).
    { set (R_aug := @clos_trans A (fun a b => R a b \/ (a = x /\ b = y))).
      (* add_incomparable_general adds (q, p) when called with p, q.
         We want (x, y) added, so call with p := y, q := x; need Hinc' : ~ (R y x \/ R x y). *)
      assert (Hinc' : ~ (R y x \/ R x y)).
      { intro Hor. apply Hinc. destruct Hor as [HRyx | HRxy].
        - right. exact HRyx.
        - left. exact HRxy. }
      assert (HR_aug_pos : IsPoset A R_aug)
        by exact (add_incomparable_general A R y x Hinc').
      destruct (szpilrajn_theorem A R_aug) as [L [HLp [HLt HLe]]].
      exists L. split.
      - apply (total_order_is_linear_extension R L HLp HLt).
        intros a b Hab. apply HLe. apply t_step. left. exact Hab.
      - apply HLe. apply t_step. right. split; reflexivity. }
    destruct Hex_Lextra as [L_extra [HL_extra_lin HL_extra_xy]].
    (* Step C: build the lift function via constructive_indefinite_description. *)
    set (Sub := {a : A | In A S' a}).
    set (Rsub := fun (a b : Sub) => R (proj1_sig a) (proj1_sig b)).
    pose (LinExtSub :=
            fun (L' : Sub -> Sub -> Prop) => IsLinearExtension Rsub L').
    assert (Hlift_ex :
              forall L' : Sub -> Sub -> Prop,
              exists L : A -> A -> Prop,
                LinExtSub L' ->
                IsLinearExtension R L /\
                (forall (a b : Sub), L' a b -> L (proj1_sig a) (proj1_sig b)) /\
                L y x /\
                (forall p q : A, IsCriticalPair R p q ->
                    (p = x /\ q = y) \/
                    (In A S' p /\ In A S' q) \/
                    L q p)).
    { intros L'. unfold LinExtSub.
      destruct (classic (IsLinearExtension Rsub L')) as [HL' | HnL'].
      - destruct (Hrem_prop L' HL') as [L [Hlin [Hext [Hyx Hcp]]]].
        exists L. intros _. exact (conj Hlin (conj Hext (conj Hyx Hcp))).
      - exists (fun _ _ => True). intro HL'. exfalso; apply HnL'; exact HL'. }
    set (lift := fun L' : Sub -> Sub -> Prop =>
                   proj1_sig (constructive_indefinite_description _
                                (Hlift_ex L'))).
    assert (Hlift_spec :
              forall L' : Sub -> Sub -> Prop,
              IsLinearExtension Rsub L' ->
              IsLinearExtension R (lift L') /\
              (forall (a b : Sub), L' a b -> (lift L') (proj1_sig a) (proj1_sig b)) /\
              (lift L') y x /\
              (forall p q : A, IsCriticalPair R p q ->
                  (p = x /\ q = y) \/
                  (In A S' p /\ In A S' q) \/
                  (lift L') q p)).
    { intros L' HL'.
      pose proof (proj2_sig (constructive_indefinite_description _ (Hlift_ex L')))
        as Hspec.
      apply Hspec. exact HL'. }
    (* Step D: define r_lifted := Im r' lift, the d'-element set of lifted ext'ns. *)
    set (r_lifted := Im _ _ r' lift).
    (* Step E: prove lift is injective on r'.
       If lift L'1 = lift L'2, for any (a,b) in Sub:
       - WLOG L'1 a b.  Then lift L'1 (proj1 a) (proj1 b), so lift L'2 same.
       - By Hlift_spec, lifts are linear extensions of R.  We need to
         transfer back to L'2 a b.  Use totality: either L'2 a b (done)
         or L'2 b a.  In the latter case, lift L'2 b a so by antisym in
         lift L'1, proj1 a = proj1 b, then a = b by proof_irrelevance, so
         L'2 a b by reflexivity.
       This argument needs the FORWARD-DIRECTION lift; the IsRemovablePair
       definition only gives L' a b → L a b (forward).  But by symmetry
       of the argument applied to L'2 in the other direction we recover
       what we need. *)
    assert (Hlift_inj :
              forall L'1 L'2,
              In _ r' L'1 -> In _ r' L'2 -> lift L'1 = lift L'2 -> L'1 = L'2).
    { intros L'1 L'2 HL'1_in HL'2_in Heq.
      assert (HL'1_lin : IsLinearExtension Rsub L'1)
        by exact (Hr'_real.(realizer_linear) L'1 HL'1_in).
      assert (HL'2_lin : IsLinearExtension Rsub L'2)
        by exact (Hr'_real.(realizer_linear) L'2 HL'2_in).
      destruct (Hlift_spec L'1 HL'1_lin) as [Hlin1 [Hext1 [_ _]]].
      destruct (Hlift_spec L'2 HL'2_lin) as [Hlin2 [Hext2 [_ _]]].
      pose proof Hlin1.(linear_is_total).(total_is_poset) as Hpos1.
      apply functional_extensionality. intro a.
      apply functional_extensionality. intro b.
      apply propositional_extensionality.
      split.
      - intro HL'1ab.
        (* L'1 a b → lift L'1 (proj1 a) (proj1 b) → lift L'2 (proj1 a) (proj1 b).
           By totality of L'2, either L'2 a b (done) or L'2 b a; in the
           latter, lift L'2 (proj1 b) (proj1 a) by Hext2, then antisym of
           lift L'2 gives proj1 a = proj1 b.  Combined with proof_irrelevance
           on the [In _ S' _] proofs, a = b, then L'2 a b by reflexivity. *)
        destruct (HL'2_lin.(linear_is_total).(total_comparable) a b) as [HL'2ab | HL'2ba].
        + exact HL'2ab.
        + (* Derive a = b *)
          assert (Hl1_ab : lift L'1 (proj1_sig a) (proj1_sig b))
            by exact (Hext1 a b HL'1ab).
          assert (Hl2_ba : lift L'2 (proj1_sig b) (proj1_sig a))
            by exact (Hext2 b a HL'2ba).
          rewrite Heq in Hl1_ab.
          pose proof Hlin2.(linear_is_total).(total_is_poset) as Hpos2.
          assert (Heq_proj : proj1_sig a = proj1_sig b)
            by exact (Hpos2.(poset_antisym) (proj1_sig a) (proj1_sig b) Hl1_ab Hl2_ba).
          destruct a as [a' ha], b as [b' hb]. simpl in Heq_proj. subst b'.
          assert (Hheq : ha = hb) by apply proof_irrelevance. subst hb.
          exact (HL'2_lin.(linear_is_total).(total_is_poset).(poset_refl) (exist _ a' ha)).
      - intro HL'2ab.
        (* Symmetric *)
        destruct (HL'1_lin.(linear_is_total).(total_comparable) a b) as [HL'1ab | HL'1ba].
        + exact HL'1ab.
        + assert (Hl2_ab : lift L'2 (proj1_sig a) (proj1_sig b))
            by exact (Hext2 a b HL'2ab).
          assert (Hl1_ba : lift L'1 (proj1_sig b) (proj1_sig a))
            by exact (Hext1 b a HL'1ba).
          rewrite <- Heq in Hl2_ab.
          assert (Heq_proj : proj1_sig a = proj1_sig b)
            by exact (Hpos1.(poset_antisym) (proj1_sig a) (proj1_sig b) Hl2_ab Hl1_ba).
          destruct a as [a' ha], b as [b' hb]. simpl in Heq_proj. subst b'.
          assert (Hheq : ha = hb) by apply proof_irrelevance. subst hb.
          exact (HL'1_lin.(linear_is_total).(total_is_poset).(poset_refl) (exist _ a' ha)). }
    (* Step F: L_extra is not in r_lifted, because every lifted L has L y x
       while L_extra has L_extra x y; if both, antisym gives x = y. *)
    assert (HL_extra_notin : ~ In _ r_lifted L_extra).
    { intro HinExtra.
      inversion HinExtra as [L' HL'_in y0 Heq].
      assert (HL'_lin : IsLinearExtension Rsub L')
        by exact (Hr'_real.(realizer_linear) L' HL'_in).
      destruct (Hlift_spec L' HL'_lin) as [Hlin [_ [Hyx _]]].
      (* Heq : L_extra = lift L' (or symmetric).  Substitute. *)
      assert (HLeq : lift L' = L_extra) by (symmetry; exact Heq).
      rewrite <- HLeq in HL_extra_xy.
      (* HL_extra_xy : lift L' x y; Hyx : lift L' y x *)
      pose proof Hlin.(linear_is_total).(total_is_poset) as HLp.
      apply Hxy_neq.
      exact (HLp.(poset_antisym) x y HL_extra_xy Hyx). }
    (* Step G: cardinality of r_lifted = d'. *)
    assert (Hcard_lifted : cardinal _ r_lifted d')
      by exact (cardinal_Im_injective _ _ r' lift d' Hr'_card Hlift_inj).
    (* Step H: define r := Add r_lifted L_extra and prove cardinality d'+1. *)
    set (r := Add (A -> A -> Prop) r_lifted L_extra).
    assert (Hcard_r : cardinal _ r (d' + 1)).
    { unfold r. replace (d' + 1) with (Datatypes.S d') by lia.
      apply card_add; [exact Hcard_lifted | exact HL_extra_notin]. }
    (* Step I: prove r is a realizer of R via critical_pair_realizer_iff. *)
    assert (Hr_inh : Ensembles.Inhabited _ r).
    { exists L_extra. right. constructor. }
    assert (Hr_lin : forall L, In _ r L -> IsLinearExtension R L).
    { intros L HL. destruct HL as [L HL | L HL].
      - inversion HL as [L' HL'_in y0 Heq].
        assert (HL'_lin : IsLinearExtension Rsub L')
          by exact (Hr'_real.(realizer_linear) L' HL'_in).
        destruct (Hlift_spec L' HL'_lin) as [Hlin _].
        subst L. exact Hlin.
      - destruct HL. exact HL_extra_lin. }
    pose proof (@critical_pair_realizer_iff A R _ HfinA r Hr_inh Hr_lin) as Hiff.
    assert (Hcp_sep : forall p q : A, IsCriticalPair R p q ->
              exists L, In _ r L /\ L q p).
    { intros p q Hcp.
      (* Use Hrem_prop on a chosen L'_0 from r' to get a lift L_0 that
         reverses (p, q) (via clause 3 of IsRemovablePair).  L_0 is in
         r_lifted because L_0 = lift L'_0 for L'_0 ∈ r'.
         Cases:
         - (p, q) = (x, y): lifted L has L y x. ✓
         - Both p, q ∈ S': use sub-realizer r' to find L' reversing (p, q);
           then lifted L reverses (p, q) too.
         - L q p (direct from clause 3, boundary case). *)
      pose proof Hr'_inh as [L'_0 HL'_0_in].
      assert (HL'_0_lin : IsLinearExtension Rsub L'_0)
        by exact (Hr'_real.(realizer_linear) L'_0 HL'_0_in).
      destruct (Hlift_spec L'_0 HL'_0_lin) as [_ [_ [Hyx_0 Hcp_0]]].
      destruct (Hcp_0 p q Hcp) as [[Hpe Hqe] | [[Hp_in Hq_in] | Hqp_0]].
      - (* (p, q) = (x, y) *)
        subst p q.
        exists (lift L'_0). split.
        + left. exists L'_0; [exact HL'_0_in | reflexivity].
        + exact Hyx_0.
      - (* Both in S': use sub-realizer to find a reversing L'. *)
        set (psub := exist (fun a => In A S' a) p Hp_in).
        set (qsub := exist (fun a => In A S' a) q Hq_in).
        assert (Hinc_sub : Incomparable Rsub psub qsub).
        { intro Hcmp. apply (critical_incomparable Hcp).
          destruct Hcmp as [HRsub | HRsub]; [left | right]; exact HRsub. }
        (* Finiteness of subtype *)
        assert (HfinSub : Finite Sub (Full_set Sub)).
        { destruct (finite_cardinal A S') as [m HSm].
          { apply (Finite_downward_closed _ _ HfinA).
            intros a _. apply Full_intro. }
          apply cardinal_finite with m.
          exact (cardinal_subtype_full A S' m HSm). }
        pose proof (subtype_is_poset R S') as Hsub_pos.
        destruct (@incomparable_lifting_to_critical_pair
                    Sub Rsub Hsub_pos HfinSub psub qsub Hinc_sub)
          as [psub'' [qsub'' [Hpsub_rel [Hqsub_rel Hcp_sub]]]].
        assert (Hr'_lin :
                  forall L', In _ r' L' -> IsLinearExtension Rsub L')
          by exact Hr'_real.(realizer_linear).
        pose proof (@critical_pair_realizer_iff
                      Sub Rsub _ HfinSub r' Hr'_inh Hr'_lin)
          as Hiff_sub.
        destruct ((proj1 Hiff_sub) Hr'_real psub'' qsub'' Hcp_sub)
          as [L' [HL'_in HL'_rev]].
        pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
        destruct (Hlift_spec L' HL'_lin) as [Hlin_L [Hext_L _]].
        pose proof HL'_lin.(linear_is_total).(total_is_poset) as HL'_pos.
        (* Chain: L' qsub qsub'' (R rel) → L' qsub'' psub'' (HL'_rev) →
                 L' psub'' psub (R rel).  All combined: L' qsub psub. *)
        assert (HL'_qp : L' qsub psub).
        { apply (poset_trans (R := L') qsub qsub'' psub).
          - exact (HL'_lin.(linear_extends) qsub qsub'' Hqsub_rel).
          - apply (poset_trans (R := L') qsub'' psub'' psub).
            + exact HL'_rev.
            + exact (HL'_lin.(linear_extends) psub'' psub Hpsub_rel). }
        exists (lift L'). split.
        + left. exists L'; [exact HL'_in | reflexivity].
        + exact (Hext_L qsub psub HL'_qp).
      - (* Boundary case: clause 3 of IsRemovablePair gives L q p directly. *)
        exists (lift L'_0). split.
        + left. exists L'_0; [exact HL'_0_in | reflexivity].
        + exact Hqp_0. }
    assert (Hreal : IsRealizer R r) by (apply Hiff; exact Hcp_sep).
    exists r. split; [exact Hreal | exact Hcard_r].
  Qed.

  (** When R is the discrete poset (an antichain), every pair (x, y) with
      x <> y is removable. Sanity check on [IsRemovablePair]: the antichain
      is the case that broke the previous design's
      [extremal_critical_pair_exists]; here it is unambiguously valid. *)
  (** SOUNDNESS NOTE — this lemma is UNPROVABLE under the current
      [IsRemovablePair] definition.

      Counter-example: A = {0, 1, 2}, R = eq, x = 0, y = 1.  S' = {2}.
      Every distinct ordered pair is a critical pair (Strict R is empty,
      so [critical_down] and [critical_up] hold vacuously, and
      [Incomparable R p q] reduces to [p <> q]).  In particular:
        - CP (0, 2) requires (by clause 3, AND-version): (p, q) = (x, y)
          false; both p, q in S' false (0 not in S'); so L 2 0 required.
        - CP (2, 0) requires: (p, q) = (x, y) false; both in S' false;
          so L 0 2 required.
      Antisymmetry of L gives 0 = 2, contradiction.

      The spec at [docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md]
      line 102 has the WEAKER condition [In Residual p \/ In Residual q
      \/ L q p] (disjunction, not conjunction); the implementation here
      strengthened it to AND, which is unsatisfiable in the antichain.

      However, the disjunction form is not currently sufficient for
      [removable_pair_dimension_bound]: in the "exactly one endpoint in
      Residual" branch the existing proof needs both endpoints to build
      subtype witnesses [psub], [qsub].  Fixing this needs a refactor of
      [removable_pair_dimension_bound] to handle that branch separately
      (e.g., using L_extra or a second auxiliary linear extension), or a
      different formulation of [IsRemovablePair] altogether.

      See task report for full analysis. *)
  Lemma antichain_removable_pair :
    (forall a b : A, R a b -> a = b) ->
    forall x y : A, x <> y -> IsRemovablePair x y.
  Proof.
  Admitted.

End RemovablePairs.

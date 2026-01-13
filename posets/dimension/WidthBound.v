From Stdlib Require Import Ensembles Finite_sets Arith Classical Lia.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs CriticalPairs Theorems Szpilrajn.
From Dilworth Require Import DilworthTheorem WidthUpperBound CardinalLemmas.

(** * Dimension ≤ Width Theorem (Dilworth, 1950)

    This module proves that the dimension of a poset is bounded by its width.
    
    Key Strategy:
    1. Define augmented relation that places chain elements "below" incomparable elements
    2. Prove TC(augmented relation) is a poset using a path invariant
    3. Use Szpilrajn's theorem to extend augmented relations to linear orders
    4. Convert a chain cover of size w into a realizer of size ≤ w
    5. Apply minimality of dimension to conclude dim(R) ≤ w
*)

Section WidthBound.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* ========================================================================= *)
  (* PART 1: Augmented Relation Definition                                     *)
  (* ========================================================================= *)

  (** We augment the relation R by putting elements of a chain C "below" 
      all incomparable elements not in C. *)
  Definition AugmentedRelation (C : Ensemble A) (x y : A) : Prop :=
    R x y \/ (In A C x /\ ~ In A C y /\ Incomparable R x y).

  (* ========================================================================= *)
  (* PART 2: Path Invariant and Antisymmetry Proof                             *)
  (* ========================================================================= *)

  (** Path invariant: characterizes all paths in TC(AugmentedRelation).
      This invariant is the key to proving antisymmetry. *)
  Definition AugmentedPathInvariant (C : Ensemble A) (u v : A) : Prop :=
    (In A C v -> R u v) /\
    (~ In A C v -> R u v \/ (exists c w, In A C c /\ ~In A C w /\ R u c /\ Incomparable R c w /\ R w v)).

  (** The path invariant holds for all paths in TC(AugmentedRelation) *)
  Lemma augmented_path_invariant_holds :
    forall C u v, IsChain R C -> TransitiveClosure (AugmentedRelation C) u v -> AugmentedPathInvariant C u v.
  Proof.
    intros C u v Hchain Htc.
    induction Htc as [u v Haug | u m v _ IH1 _ IH2].
    - (* Base case *)
      split; intros Hv; destruct Haug as [Hr | [Hu [Hnv Hinc]]]; auto;
        [contradiction | right; exists u, v; repeat split; auto; apply poset_refl].
    - (* Transitive case *)
      destruct IH1 as [IH1_in IH1_out], IH2 as [IH2_in IH2_out]; split; intros Hv.
      + (* v in C *)
        assert (Rmv: R m v) by auto.
        destruct (classic (In A C m)) as [Hm | Hnm]; [eapply poset_trans; eauto |].
        destruct (IH1_out Hnm) as [Rum | [c [w [Hc [Nw [Ruc [Hcw Rwm]]]]]]];
          [eapply poset_trans; eauto |].
        assert (Rwv: R w v) by (eapply poset_trans; eauto).
        destruct (@chain_comparable A R C Hchain c v Hc Hv); [eapply poset_trans; eauto |].
        exfalso; apply Hcw; right; eapply poset_trans; eauto.
      + (* v not in C *)
        destruct (IH2_out Hv) as [Rmv | [c' [w' [Hc' [Nw' [Rmc' [Hc'w' Rw'v]]]]]]].
        * destruct (classic (In A C m)) as [Hm | Hnm]; [left; eapply poset_trans; eauto |].
          destruct (IH1_out Hnm) as [Rum | [c [w [Hc [Nw [Ruc [Hcw Rwm]]]]]]];
            [left; eapply poset_trans; eauto |
             right; exists c, w; repeat split; auto; eapply poset_trans; eauto].
        * destruct (classic (In A C m)) as [Hm | Hnm];
            [right; exists c', w'; repeat split; auto; eapply poset_trans; eauto |].
          destruct (IH1_out Hnm) as [Rum | [c [w [Hc [Nw [Ruc [Hcw Rwm]]]]]]];
            [right; exists c', w'; repeat split; auto; eapply poset_trans; eauto |].
          assert (Rwc': R w c') by (eapply poset_trans; eauto).
          destruct (@chain_comparable A R C Hchain c c' Hc Hc'); 
            [right; exists c', w'; repeat split; auto; eapply poset_trans; eauto |].
          exfalso; apply Hcw; right; eapply poset_trans; eauto.
  Qed.

  (** TC(AugmentedRelation C) is a poset.
      The main difficulty is proving antisymmetry (acyclicity). *)
  Lemma augmented_is_poset :
    forall C, IsChain R C ->
    IsPoset A (TransitiveClosure (AugmentedRelation C)).
  Proof.
    intros C Hchain; constructor.
    - (* Reflexivity *)
      intros x; apply tc_step; left; apply poset_refl.
    - (* Antisymmetry *)
      intros x y Hxy Hyx.
      destruct (classic (x = y)) as [? | Hneq]; auto; exfalso.
      
      (* Apply path invariants *)
      pose proof (augmented_path_invariant_holds C x y Hchain Hxy) as [Hxy_in Hxy_out].
      pose proof (augmented_path_invariant_holds C y x Hchain Hyx) as [Hyx_in Hyx_out].
      
      (* Case analysis on chain membership *)
      destruct (classic (In A C x)) as [Hx | Hnx], (classic (In A C y)) as [Hy | Hny].
      + (* Both in C: use antisymmetry of R *)
        apply Hneq; eapply poset_antisym; eauto.
      + (* x in C, y not in C *)
        assert (Ryx: R y x) by auto.
        destruct (Hxy_out Hny) as [Rxy | [c [w [Hc [Nw [Rxc [Hcw Rwy]]]]]]];
          [apply Hneq; eapply poset_antisym; eauto |
           assert (Rwc: R w c) by (eapply poset_trans; [eapply poset_trans; eauto |]; eauto); 
           apply Hcw; right; assumption].
      + (* x not in C, y in C *)
        assert (Rxy: R x y) by auto.
        destruct (Hyx_out Hnx) as [Ryx | [c [w [Hc [Nw [Ryc [Hcw Rwx]]]]]]];
          [apply Hneq; eapply poset_antisym; eauto |
           assert (Rwc: R w c) by (eapply poset_trans; [| eapply poset_trans]; eauto);
           apply Hcw; right; assumption].
      + (* Neither in C: compare jump structures *)
        destruct (Hyx_out Hnx) as [Ryx | [c [w [Hc [Nw [Ryc [Hcw Rwx]]]]]]].
        * destruct (Hxy_out Hny) as [Rxy | [c [w [Hc [Nw [Rxc [Hcw Rwy]]]]]]];
            [apply Hneq; eapply poset_antisym; eauto |
             assert (Rwc: R w c) by (eapply poset_trans; [eapply poset_trans; eauto |]; eauto);
             apply Hcw; right; assumption].
        * destruct (Hxy_out Hny) as [Rxy | [c' [w' [Hc' [Nw' [Rxc' [Hc'w' Rw'y]]]]]]].
          -- assert (Rwc: R w c) by (eapply poset_trans; [| eapply poset_trans]; eauto);
             apply Hcw; right; assumption.
          -- assert (Rwc': R w c') by (eapply poset_trans; eauto).
             assert (Rw'c: R w' c) by (eapply poset_trans; eauto).
             destruct (@chain_comparable A R C Hchain c c' Hc Hc') as [Rcc' | Rc'c];
               [assert (Rw'c': R w' c') by (eapply poset_trans; eauto); apply Hc'w'; right; assumption |
                assert (Rwc: R w c) by (eapply poset_trans; eauto); apply Hcw; right; assumption].
    - (* Transitivity *)
      intros x y z Hxy Hyz; apply tc_trans with y; auto.
  Qed.

  (* ========================================================================= *)
  (* PART 3: Helper Lemmas                                                     *)
  (* ========================================================================= *)

  (** Elements in a chain are comparable, hence not incomparable *)
  Lemma chain_incomparable_false : forall C x y,
    IsChain R C -> In A C x -> In A C y -> Incomparable R x y -> False.
  Proof.
    intros C x y Hchain HxC HyC Hinc; unfold Incomparable in Hinc.
    destruct (@chain_comparable A R C Hchain x y HxC HyC); [apply Hinc | apply Hinc]; auto.
  Qed.

  (** Augmented relation extends R *)
  Lemma augmented_extends_R : forall C x y,
    R x y -> AugmentedRelation C x y.
  Proof. intros; left; assumption. Qed.

  (** Linear extension of augmented relation is linear extension of R *)
  Lemma augmented_extension_is_R_extension : forall C L,
    IsLinearExtension (AugmentedRelation C) L -> IsLinearExtension R L.
  Proof.
    intros C L [Htot Hext]; constructor; auto.
    intros x y Hr; apply Hext, augmented_extends_R; auto.
  Qed.

  (** Linear extension of TC(Aug) is linear extension of Aug *)
  Lemma tc_extension_implies_aug_extension : forall C L,
    IsLinearExtension (TransitiveClosure (AugmentedRelation C)) L ->
    IsLinearExtension (AugmentedRelation C) L.
  Proof.
    intros C L [Htot Hext]; constructor; auto.
    intros u v Haug; apply Hext, tc_step; auto.
  Qed.

  (** Add element to ensemble that's already present doesn't change it *)
  Lemma add_already_in : forall {U : Type} (S : Ensemble U) (x : U),
    In U S x -> Add U S x = S.
  Proof.
    intros U0 S0 x0 Hx0; apply Extensionality_Ensembles; intros z; split.
    - intros Hz; inversion Hz as [z' Hz_old | z' Hz_new]; subst; auto.
      inversion Hz_new; subst; auto.
    - intros Hz; apply Union_introl; assumption.
  Qed.

  (** Membership in Add *)
  Lemma in_add_cases : forall {U : Type} (S : Ensemble U) (x y : U),
    In U (Add U S x) y -> In U S y \/ y = x.
  Proof.
    intros U S x y Hy; destruct Hy as [y Hy_old | y Hy_new];
      [left; auto | right; inversion Hy_new; auto].
  Qed.

  (* ========================================================================= *)
  (* PART 4: Szpilrajn Extensions for Chains                                   *)
  (* ========================================================================= *)

  (** Apply Szpilrajn's theorem to obtain linear extensions of augmented relations *)
  Lemma szpilrajn_for_augmented : forall C,
    IsChain R C ->
    exists L, IsTotalOrder L /\ (forall x y, TransitiveClosure (AugmentedRelation C) x y -> L x y).
  Proof.
    intros C Hchain.
    set (rel := TransitiveClosure (AugmentedRelation C)).
    assert (Hposet: IsPoset A rel) by (apply augmented_is_poset; auto).
    (* Use Szpilrajn's theorem from Theorems.v *)
    destruct (szpilrajn_theorem A rel) as [L [HL_poset [HL_total HL_extends]]].
    exists L.
    split.
    - constructor; auto.
    - exact HL_extends.
  Qed.

  Lemma exists_extensions_for_chains : forall chains k,
    cardinal _ chains k ->
    (forall C, In _ chains C -> IsChain R C) ->
    exists exts m,
      cardinal _ exts m /\ m <= k /\
      (forall L, In _ exts L -> IsLinearExtension R L) /\
      (forall C, In _ chains C -> exists L, In _ exts L /\ IsLinearExtension (AugmentedRelation C) L).
  Proof.
    intros chains k Hcard.
    induction Hcard as [| chains k' Hcard IH x Hx_notin].
    - (* Empty set case *)
      intros _.
      exists (Empty_set _), 0.
      split. { constructor. }
      split. { auto. }
      split.
      { intros L_emp HL_emp. inversion HL_emp. }
      { intros C_emp HC_emp. inversion HC_emp. }
    - (* Add case: chains' = Add chains x *)
      intros Hchains0.
      (* Prove all old chains are still chains *)
      (* Prove all old chains are still chains *)
      assert (Hchains: forall C, In _ chains C -> IsChain R C) by
        (intros C HC; apply Hchains0, Union_introl; auto).
      destruct (IH Hchains) as [exts [m [Hexts_card [Hm_le [Hexts_R Hexts_corr]]]]].
      
      (* The new chain x *)
      assert (HC_new_chain: IsChain R x) by
        (apply Hchains0, Union_intror, In_singleton).
      
      (* Use Szpilrajn to get a total order extending TC(Aug) *)
      destruct (szpilrajn_for_augmented x HC_new_chain) as [L_new [HL_total HL_extends]].
      
      (* L_new is a linear extension of AugmentedRelation x *)
      assert (HL_new_aug: IsLinearExtension (AugmentedRelation x) L_new) by
        (constructor; [auto | intros u v Haug; apply HL_extends, tc_step; auto]).
      
      exists (Add _ exts L_new).
      destruct (classic (In _ exts L_new)) as [HL_new_in_exts | HL_new_notin_exts].
      + (* L_new is already in exts - cardinality stays m *)
        exists m; rewrite (add_already_in exts L_new HL_new_in_exts).
        split. { exact Hexts_card. }
        split. { eapply PeanoNat.Nat.le_trans; [exact Hm_le | auto]. }
        split. { exact Hexts_R. }
        (* Correspondence *)
        intros C HC; inversion HC as [C' HC_old | C' HC_sing]; subst.
        -- destruct (Hexts_corr C HC_old) as [L' [HL'_in HL'_aug]];
             exists L'; split; auto.
        -- inversion HC_sing; subst; exists L_new; split; auto.
      + (* L_new is NOT in exts - cardinality becomes S m *)
        exists (S m).
        split. { constructor; auto. }
        split. { lia. }
        split.
        { (* IsLinearExtension R L for all L in Add exts L_new *)
          intros L HL; inversion HL as [L' HL_old | L' HL_sing]; subst.
          - apply Hexts_R; auto.
          - inversion HL_sing; subst;
            apply augmented_extension_is_R_extension with x; auto. }
        (* Correspondence *)
        intros C HC; inversion HC as [C' HC_old | C' HC_sing]; subst.
        -- destruct (Hexts_corr C HC_old) as [L' [HL'_in HL'_aug]];
           exists L'; split; auto; apply Union_introl; auto.
        -- inversion HC_sing; subst; exists L_new; split.
           ++ apply Union_intror, In_singleton.
           ++ auto.
  Qed.

  (** For a chain cover, construct a set of linear extensions forming a realizer *)
  Lemma chain_cover_implies_realizer_le : forall cover k,
    IsChainCover R cover ->
    cardinal (Ensemble A) cover k ->
    exists realizer n, IsRealizer R realizer /\ cardinal (A -> A -> Prop) realizer n /\ n <= k.
  Proof.
    intros cover k Hcover Hcard.
    destruct (exists_extensions_for_chains cover k Hcard (@chain_cover_chains _ R cover Hcover))
      as [exts [n [Hexts_card [Hn_le_w [Hexts_R Hexts_corr]]]]].
    
    exists exts, n.
    split; [| split; auto].
    constructor; auto.
    intros x y; split.
    - intros Rxy L HL; destruct (Hexts_R L HL) as [_ Hext]; auto.
    - intros Hxy; destruct (classic (R x y)) as [? | HnotR]; auto.
      destruct (classic (R y x)) as [Hyx | Hnyx].
      + destruct (@chain_cover_covers A R cover Hcover y (Full_intro A y)) as [C [HC_in HyC]].
        destruct (Hexts_corr C HC_in) as [L [HL_in HL_aug]].
        destruct (Hexts_R L HL_in) as [[HL_poset _] HL_extends].
        assert (x = y) by (eapply poset_antisym; [apply Hxy | apply HL_extends]; auto); 
          subst; apply poset_refl.
      + assert (Hinc: Incomparable R x y) by (intros [? | ?]; auto).
        destruct (@chain_cover_covers A R cover Hcover y (Full_intro A y)) as [C [HC_in HyC]].
        destruct (Hexts_corr C HC_in) as [L [HL_in HL_aug]].
        destruct (classic (In A C x)) as [HxC | HnxC].
        -- exfalso; apply (chain_incomparable_false C x y); auto.
           apply (@chain_cover_chains _ R cover Hcover C HC_in).
        -- assert (Haug: AugmentedRelation C y x) by (right; repeat split; auto; intros [? | ?]; auto).
           destruct HL_aug as [_ HL_aug_ext], (Hexts_R L HL_in) as [[HL_poset _] _].
           assert (x = y) by (eapply poset_antisym; [apply Hxy | apply HL_aug_ext]; auto); 
             subst; apply poset_refl.
  Qed.

  (* ========================================================================= *)
  (* PART 5: Main Theorem                                                      *)
  (* ========================================================================= *)

  (** Main Theorem: Dimension is bounded by width (Dilworth, 1950) *)
  Theorem dimension_le_width : forall d w,
    PosetDimension R d -> Width R w -> d <= w.
  Proof.
    intros d w [realizer Hreal Hcard Hmin] Hwidth.
    (* 1. Use Dilworth to get min chain cover size k = w *)
    destruct Hwidth as [la Hla].
    destruct (DilworthB R w la Hla) as [cover [Hcover Hcover_card]].
    
    (* 2. Get realizer of size n <= w *)
    destruct (chain_cover_implies_realizer_le cover w Hcover Hcover_card) 
      as [realizer_w [n [Hreal_w [Hcard_real_w Hn_le_w]]]].
      
    (* 3. Minimal dimension d <= n <= w *)
    assert (d <= n).
    { apply (Hmin realizer_w n Hreal_w Hcard_real_w). }
    apply PeanoNat.Nat.le_trans with n; auto.
  Qed.
End WidthBound.

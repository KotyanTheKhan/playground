From Stdlib Require Import Ensembles Finite_sets Arith Classical Lia.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs CriticalPairs Theorems Szpilrajn.
From Dilworth Require Import DilworthTheorem WidthUpperBound CardinalLemmas.


Section WidthBound.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* ========================================================================= *)
  (* Augmented Relation for a Chain                                            *)
  (* ========================================================================= *)

  (** We augment the relation R by putting elements of a chain C "below" 
      all incomparable elements not in C. *)
  Definition AugmentedRelation (C : Ensemble A) (x y : A) : Prop :=
    R x y \/ (In A C x /\ ~ In A C y /\ Incomparable R x y).

  (** The transitive closure of the augmented relation is a poset.
      The key difficulty is proving antisymmetry (acyclicity). *)
  (* Strong Invariant for Antisymmetry *)
  Definition AugmentedPathInvariant (C : Ensemble A) (u v : A) : Prop :=
    (In A C v -> R u v) /\
    (~ In A C v -> R u v \/ (exists c w, In A C c /\ ~In A C w /\ R u c /\ Incomparable R c w /\ R w v)).

  Lemma augmented_path_invariant_holds :
    forall C u v, IsChain R C -> TransitiveClosure (AugmentedRelation C) u v -> AugmentedPathInvariant C u v.
  Proof.
    intros C u v Hchain Htc.
    induction Htc as [u v Haug | u m v Htc1 IH1 Htc2 IH2].
    - (* Base: Aug u v *)
      unfold AugmentedPathInvariant in *. unfold AugmentedRelation in Haug.
      split; intros Hinv.
      + (* In v *)
        destruct Haug as [Hr | Hj]; auto.
        destruct Hj as [_ [Hnc _]]. contradiction.
      + (* ~ In v *)
        destruct Haug as [Hr | Hj]; auto.
        (* Jump case: u in C, v out C, u || v *)
        destruct Hj as [Hu [Hnv Hinc]].
        right. exists u, v. repeat split; auto.
        apply poset_refl. apply poset_refl.
    - (* Trans: u -> m -> v *)
      unfold AugmentedPathInvariant in *.
      destruct IH1 as [IH1_in IH1_out].
      destruct IH2 as [IH2_in IH2_out].
      split; intros Hinv.
      + (* In v *)
        (* IH2_in applied *)
        assert (Rmv : R m v) by (apply IH2_in; auto).
        destruct (classic (In A C m)) as [Hm | Hnm].
        * (* In m *)
          assert (Rum : R u m) by (apply IH1_in; auto).
          apply poset_trans with m; auto.
        * (* ~ In m *)
          destruct (IH1_out Hnm) as [Rum | [c [w [Hc [Nw [Ruc [Hcw Rwm]]]]]]].
          -- (* R u m *)
             apply poset_trans with m; auto.
          -- (* Jump structure *)
             (* u <= c || w <= m <= v *)
             assert (Rwv : R w v) by (apply poset_trans with m; auto).
             (* c || w. w <= v. v, c in C. *)
             destruct (@chain_comparable A R C Hchain c v Hc Hinv) as [Rcv | Rvc].
             ++ (* c <= v. *)
                (* c || w => ~(w <= c). If v <= c then w <= c. Contradiction. *)
                apply poset_trans with c; auto.
             ++ (* v <= c *)
                assert (Rwc : R w c) by (apply poset_trans with v; auto).
                exfalso; apply Hcw; right; assumption.
      + (* ~ In v *)
        destruct (IH2_out Hinv) as [Rmv | [c' [w' [Hc' [Nw' [Rmc' [Hc'w' Rw'v]]]]]]].
        * (* R m v *)
          destruct (classic (In A C m)) as [Hm | Hnm].
          -- (* In m *)
             assert (Rum : R u m) by (apply IH1_in; auto).
             left. apply poset_trans with m; auto.
          -- (* ~ In m *)
             destruct (IH1_out Hnm) as [Rum | [c [w [Hc [Nw [Ruc [Hcw Rwm]]]]]]].
             ++ (* R u m *)
                left. apply poset_trans with m; auto.
             ++ (* u <= c || w <= m *)
                right. exists c, w. repeat split; auto.
                apply poset_trans with m; auto.
        * (* m -> ... -> c' || w' -> v *)
          destruct (classic (In A C m)) as [Hm | Hnm].
          -- (* In m *)
             assert (Rum : R u m) by (apply IH1_in; auto).
             right. exists c', w'. repeat split; auto.
             apply poset_trans with m; auto.
          -- (* ~ In m *)
             destruct (IH1_out Hnm) as [Rum | [c [w [Hc [Nw [Ruc [Hcw Rwm]]]]]]].
             ++ (* R u m *)
                right. exists c', w'. repeat split; auto.
                apply poset_trans with m; auto.
             ++ (* u <= c || w <= m -> ... -> c' || w' -> v *)
                (* w <= m <= c' *)
                assert (Rwc' : R w c') by (apply poset_trans with m; auto).
                (* c || w. w <= c'. c, c' in C. *)
                destruct (@chain_comparable A R C Hchain c c' Hc Hc') as [Rcc' | Rc'c].
                ** (* c <= c' *)
                   (* We keep the SECOND jump: c' || w'. *)
                   right. exists c', w'. repeat split; auto.
                   apply poset_trans with c; auto.
                ** (* c' <= c *)
                   (* w <= c' <= c => w <= c. Contradiction c || w *)
                   assert (Rwc : R w c) by (apply poset_trans with c'; auto).
                   exfalso; apply Hcw; right; assumption.
  Qed.

  Lemma augmented_is_poset :
    forall C, IsChain R C ->
    IsPoset A (TransitiveClosure (AugmentedRelation C)).
  Proof.
    intros C Hchain.
    constructor.
    - (* Refl *)
      intros x. apply tc_step. left. apply poset_refl.
    - (* Antisym *)
      intros x y Hxy Hyx.
      destruct (classic (x = y)) as [Heq | Hneq]; auto.
      exfalso.
      
      (* Apply Invariant *)
      pose proof (augmented_path_invariant_holds C x y Hchain Hxy) as Hinv_xy.
      pose proof (augmented_path_invariant_holds C y x Hchain Hyx) as Hinv_yx.
      unfold AugmentedPathInvariant in *.
      destruct Hinv_xy as [Hxy_in Hxy_out].
      destruct Hinv_yx as [Hyx_in Hyx_out].
      
      destruct (classic (In A C x)) as [Hx | Hnx].
      + (* In x *)
        (* Hyx: y -> x. x In. Hinv y x implies R y x. *)
        assert (Ryx : R y x) by (apply Hyx_in; auto).
        (* Hxy: x -> y. *)
        destruct (classic (In A C y)) as [Hy | Hny].
        * (* In y *)
          assert (Rxy : R x y) by (apply Hxy_in; auto).
          apply Hneq. apply poset_antisym; auto.
        * (* ~ In y *)
          destruct (Hxy_out Hny) as [Rxy | [c [w [Hc [Nw [Rxc [Hcw Rwy]]]]]]].
          -- apply Hneq. apply poset_antisym; auto.
          -- (* x <= c || w <= y. *)
            (* we have y <= x (Ryx). so w <= x. *)
            (* x <= c. so w <= c. Contradicts c || w *)
            assert (Rwc : R w c). {
               apply poset_trans with y; auto.
               apply poset_trans with x; auto.
            }
            exfalso; apply Hcw; right; assumption.
      + (* ~ In x *)
        (* Hyx: y -> x (Out). *)
        destruct (Hyx_out Hnx) as [Ryx | [c [w [Hc [Nw [Ryc [Hcw Rwx]]]]]]].
        * (* R y x *)
          destruct (classic (In A C y)) as [Hy | Hny].
          -- (* In y *)
            (* x -> y (In). R x y *)
            assert (Rxy : R x y) by (apply Hxy_in; auto).
            apply Hneq. apply poset_antisym; auto.
          -- (* ~ In y *)
            (* x -> y (Out). *)
             destruct (Hxy_out Hny) as [Rxy | [c [w [Hc [Nw [Rxc [Hcw Rwy]]]]]]].
             ++ apply Hneq. apply poset_antisym; auto.
             ++ (* x <= c || w <= y *)
                assert (Rwc : R w c). {
                  apply poset_trans with y; auto.
                  apply poset_trans with x; auto.
                }
                exfalso; apply Hcw; right; assumption.
        * (* y <= c || w <= x *)
          (* Hxy: x -> y. *)
          destruct (classic (In A C y)) as [Hy | Hny].
          -- (* In y *)
            assert (Rxy : R x y) by (apply Hxy_in; auto).
            (* w <= x <= y <= c => w <= c. Contra *)
            assert (Rwc : R w c). {
              apply poset_trans with x; auto.
              apply poset_trans with y; auto.
            }
            exfalso; apply Hcw; right; assumption.
          -- (* ~ In y *)
             destruct (Hxy_out Hny) as [Rxy | [c' [w' [Hc' [Nw' [Rxc' [Hc'w' Rw'y]]]]]]].
             ++ (* R x y *)
                assert (Rwc : R w c). {
                  apply poset_trans with x; auto.
                  apply poset_trans with y; auto.
                }
                exfalso; apply Hcw; right; assumption.
             ++ (* x <= c' || w' <= y || c <= x... chain comparison *)
                (* x <= c' || w' <= y. y <= c || w <= x. *)
                (* w <= x <= c' *)
                assert (Rwc' : R w c') by (apply poset_trans with x; auto).
                (* w' <= y <= c *)
                assert (Rw'c : R w' c) by (apply poset_trans with y; auto).
                
                destruct (@chain_comparable A R C Hchain c c' Hc Hc') as [Rcc' | Rc'c].
                ** (* c <= c' *)
                   (* w' <= c <= c' => w' <= c'. Contra c' || w' *)
                   assert (Rw'c' : R w' c') by (apply poset_trans with c; auto).
                   exfalso; apply Hc'w'; right; assumption.
                ** (* c' <= c *)
                   (* w <= c' <= c => w <= c. Contradiction c || w *)
                   assert (Rwc : R w c) by (apply poset_trans with c'; auto).
                   exfalso; apply Hcw; right; assumption.
    - (* Trans *)
      intros x y z Hxy Hyz.
      apply tc_trans with y; auto.
  Qed.

  
  (* Helper: Elements in a chain are comparable, hence not incomparable *)
  Lemma chain_incomparable_false : forall C x y,
    IsChain R C -> In A C x -> In A C y -> Incomparable R x y -> False.
  Proof.
    intros C x y Hchain HxC HyC Hinc.
    unfold Incomparable in Hinc.
    destruct (@chain_comparable A R C Hchain x y HxC HyC) as [Hxy | Hyx].
    - apply Hinc; left; assumption.
    - apply Hinc; right; assumption.
  Qed.

  (* Lemma: Augmented relation extends R *)
  Lemma augmented_extends_R : forall C x y,
    R x y -> AugmentedRelation C x y.
  Proof.
    intros C x y Hxy. left. assumption.
  Qed.

  (* Lemma: Linear extension of Augmented relation is linear extension of R *)
  Lemma augmented_extension_is_R_extension : forall C L,
    IsLinearExtension (AugmentedRelation C) L -> IsLinearExtension R L.
  Proof.
    intros C L Hlin.
    destruct Hlin as [Htot Hext].
    constructor; auto.
    intros x y Hr.
    apply Hext. apply augmented_extends_R; auto.
  Qed.

  (* Helper: Linear extension of TC(Aug) is linear extension of Aug *)
  Lemma tc_extension_implies_aug_extension : forall C L,
    IsLinearExtension (TransitiveClosure (AugmentedRelation C)) L ->
    IsLinearExtension (AugmentedRelation C) L.
  Proof.
    intros C L Hlin.
    destruct Hlin as [Htot Hext].
    constructor; auto.
    intros u v Haug. apply Hext. apply tc_step. auto.
  Qed.

  (* Helper: Add element to ensemble that's already present doesn't change it *)
  Lemma add_already_in : forall {U : Type} (S : Ensemble U) (x : U),
    In U S x -> Add U S x = S.
  Proof.
    intros U0 S0 x0 Hx0.
    apply Extensionality_Ensembles. intros z. split.
    - intros Hz. inversion Hz as [z' Hz_old | z' Hz_new]; subst.
      + auto.
      + inversion Hz_new. subst. auto.
    - intros Hz. apply Union_introl. assumption.
  Qed.

  (* Helper: Membership in Add *)
  Lemma in_add_cases : forall {U : Type} (S : Ensemble U) (x y : U),
    In U (Add U S x) y -> In U S y \/ y = x.
  Proof.
    intros U S x y Hy.
    destruct Hy as [y Hy_old | y Hy_new].
    - left. auto.
    - right. inversion Hy_new. auto.
  Qed.

  (* Lemma: Existence of linear extensions for a family of chains *)
  (* This uses Szpilrajn's theorem from Theorems.v *)
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
      assert (Hchains: forall C, In _ chains C -> IsChain R C).
      { intros C HC. apply Hchains0. apply Union_introl; auto. }
      destruct (IH Hchains) as [exts [m [Hexts_card [Hm_le [Hexts_R Hexts_corr]]]]].
      
      (* The new chain x *)
      set (C_new := x).
      assert (HC_new_chain: IsChain R C_new).
      { apply Hchains0. apply Union_intror. apply In_singleton. }
      
      (* Use Szpilrajn to get a total order extending TC(Aug) *)
      destruct (szpilrajn_for_augmented C_new HC_new_chain) as [L_new [HL_total HL_extends]].
      
      (* L_new is a linear extension of AugmentedRelation C_new *)
      assert (HL_new_aug: IsLinearExtension (AugmentedRelation C_new) L_new).
      { constructor.
        - auto.
        - intros u v Haug. apply HL_extends. apply tc_step. auto. }
      
      exists (Add _ exts L_new).
      destruct (classic (In _ exts L_new)) as [HL_new_in_exts | HL_new_notin_exts].
      + (* L_new is already in exts - cardinality stays m *)
        assert (Hadd_eq: Add (A -> A -> Prop) exts L_new = exts).
        { apply add_already_in. auto. }
        exists m.
        rewrite Hadd_eq.
        split. { exact Hexts_card. }
        split. { eapply PeanoNat.Nat.le_trans. exact Hm_le. auto. }
        split. { exact Hexts_R. }
        (* Correspondence *)
        intros C HC.
        inversion HC as [C' HC_old | C' HC_sing]; subst.
        -- destruct (Hexts_corr C HC_old) as [L' [HL'_in HL'_aug]].
           exists L'. split; auto.
        -- inversion HC_sing. subst.
           exists L_new. split; auto.
      + (* L_new is NOT in exts - cardinality becomes S m *)
        exists (S m).
        split. { constructor; auto. }
        split. { lia. }
        split.
        { (* IsLinearExtension R L for all L in Add exts L_new *)
          intros L HL.
          inversion HL as [L' HL_old | L' HL_sing]; subst.
          - apply Hexts_R; auto.
          - inversion HL_sing. subst.
            apply augmented_extension_is_R_extension with C_new; auto. }
        (* Correspondence *)
        intros C HC.
        inversion HC as [C' HC_old | C' HC_sing]; subst.
        -- destruct (Hexts_corr C HC_old) as [L' [HL'_in HL'_aug]].
           exists L'. split; auto. apply Union_introl; auto.
        -- inversion HC_sing. subst.
           exists L_new. split.
           ++ apply Union_intror. apply In_singleton.
           ++ auto.
  Qed.

  Lemma chain_cover_implies_realizer_le : forall cover k,
    IsChainCover R cover ->
    cardinal (Ensemble A) cover k ->
    exists realizer n, IsRealizer R realizer /\ cardinal (A -> A -> Prop) realizer n /\ n <= k.
  Proof.
    intros cover k Hcover Hcard.
    (* Use helper lemma *)
    assert (Hchains: forall C, In _ cover C -> IsChain R C).
    { apply Hcover. }
    destruct (exists_extensions_for_chains cover k Hcard Hchains)
      as [exts [n [Hexts_card [Hn_le_w [Hexts_R Hexts_corr]]]]].
    
    exists exts, n.
    split.
    - (* IsRealizer *)
      constructor.
      + auto. (* Linear extensions of R *)
      + intros x y.
        split; intros Hxy.
        * (* R x y -> forall L... L x y *)
          intros L HL.
          destruct (Hexts_R L HL) as [_ HLinExt_extends].
          apply HLinExt_extends. assumption.
        * (* (forall L, L x y) -> R x y *)
          destruct (classic (R x y)) as [HRxy | HnotR]; auto.
          (* We have ~ R x y. Assume Hxy (forall L, L x y). *)
          (* Need contradiction. *)
          
          (* Case 1: R y x *)
          destruct (classic (R y x)) as [Hyx | Hnyx].
          -- (* R y x. Need to show R x y holds or derive contradiction *)
             (* If x = y, then R x y = R x x which holds by reflexivity *)
             (* Get a chain from cover containing y *)
             destruct (@chain_cover_covers A R cover Hcover y (Full_intro A y)) as [C [HC_in HyC]].
             destruct (Hexts_corr C HC_in) as [L [HL_in HL_aug]].
             (* L x y by Hxy *)
             assert (HLxy : L x y) by (apply Hxy; auto).
             (* L y x because L extends R *)
             destruct (Hexts_R L HL_in) as [_ HL_extends].
             assert (HLyx : L y x) by (apply HL_extends; auto).
             (* By antisymmetry of L, x = y *)
             destruct (Hexts_R L HL_in) as [HL_total _].
             destruct HL_total as [HL_poset _].
             assert (Heq : x = y) by (apply (@poset_antisym A L HL_poset x y); auto).
             (* Then R x y = R y y which holds by reflexivity *)
             subst. apply poset_refl.
          
          -- (* Case 2: Incomparable x y *)
             assert (Hinc: Incomparable R x y).
             { unfold Incomparable. intros [HRxy | HRyx]; auto. }
             
             (* Use covering property. *)
             destruct (@chain_cover_covers A R cover Hcover y (Full_intro A y)) as [C [HC_in HyC]].
             
             (* Get extension L associated with C *)
             destruct (Hexts_corr C HC_in) as [L [HL_in HL_aug]].
             
             (* Check In C x *)
             destruct (classic (In A C x)) as [HxC | HnxC].
             ++ (* x in C, y in C. Comparable. Contradiction. *)
                exfalso. 
                apply (chain_incomparable_false C x y (Hchains C HC_in) HxC HyC Hinc).
             ++ (* x not in C. *)
                (* Check AugmentedRelation C y x *)
                assert (Haug: AugmentedRelation C y x).
                { right. repeat split; auto.
                  unfold Incomparable. rewrite or_comm. auto. }
                
                (* L extends Aug. So L y x. *)
                destruct HL_aug as [_ HL_aug_extends].
                assert (HLyx : L y x).
                { apply HL_aug_extends. exact Haug. }
                
                (* But hypothesis says L x y (since L in exts). *)
                assert (HLxy : L x y) by (apply Hxy; auto).
                
                (* Antisym L x y / L y x -> x = y. *)
                (* Contradiction with Incomparable (implies x <> y). *)
                destruct (Hexts_R L HL_in) as [HL_total _].
                destruct HL_total as [HL_poset _].
                assert (Heq: x = y).
                { apply (@poset_antisym A L HL_poset x y); auto. }
                subst. apply poset_refl.
    - split; auto.
  Qed.

  (** Theorem: Dimension is bounded by width (Dilworth, 1950) *)
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

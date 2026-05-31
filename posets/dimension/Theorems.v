From Stdlib Require Import List Classical ClassicalDescription IndefiniteDescription.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia.
From Stdlib Require Import Relations.Relation_Operators.

(** The image of a finite set under a function has cardinality ≤ that of the source. *)
Lemma cardinal_Im_le_local :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  exists m, cardinal V (Im U V S f) m /\ m <= n.
Proof.
  intros U V S f n Hcard.
  induction Hcard as [| A0 n0 Hcard0 IHHcard x Hxnin].
  - exists 0. split; [| lia].
    assert (Heq : Im U V (Empty_set U) f = Empty_set V).
    { apply Extensionality_Ensembles. split.
      - intros x [z Hz _Heqy]. destruct Hz.
      - intros x Hx. destruct Hx. }
    rewrite Heq. constructor.
  - destruct IHHcard as [m [Hcard_m Hle]].
    destruct (classic (In V (Im U V A0 f) (f x))) as [HIn | HNin].
    + exists m. split; [| lia].
      assert (Heq : Im U V (Add U A0 x) f = Im U V A0 f).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz y_unused Heqy]. destruct Hz as [z Hz | z Hz].
          + exists z; [exact Hz | exact Heqy].
          + destruct Hz. rewrite Heqy. exact HIn.
        - intros y [z Hz y_unused Heqy]. exists z; [left; exact Hz | exact Heqy]. }
      rewrite Heq. exact Hcard_m.
    + exists (S m). split; [| lia].
      assert (Heq : Im U V (Add U A0 x) f = Add V (Im U V A0 f) (f x)).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz y_unused Heqy]. destruct Hz as [z Hz | z Hz].
          + left. exists z; auto.
          + destruct Hz. right. rewrite Heqy. constructor.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [z Hz y_unused Heqy]. exists z; [left; exact Hz | exact Heqy].
          + destruct Hy. exists x; [right; constructor | reflexivity]. }
      rewrite Heq. apply card_add; assumption.
Qed.

Lemma singleton_cardinal :
  forall (U : Type) (x : U),
  cardinal U (Singleton U x) 1.
Proof.
  intros U x.
  assert (Heq : Singleton U x = Add U (Empty_set U) x).
  { apply Extensionality_Ensembles. split.
    - intros y Hy. right. exact Hy.
    - intros y Hy. destruct Hy as [y Hy | y Hy].
      + destruct Hy.
      + exact Hy. }
  rewrite Heq.
  apply card_add.
  - constructor.
  - intro H. inversion H.
Qed.

(** Lemma: cardinal of S minus one element, given cardinal S (S n) and x ∈ S. *)
Lemma cardinal_subtract_sn :
  forall (U : Type) (St : Ensemble U) (x : U) (n : nat),
  cardinal U St (Datatypes.S n) -> In U St x -> cardinal U (Subtract U St x) n.
Proof.
  intros U St x n Hcard HIn.
  exact (card_soustr_1 U St (Datatypes.S n) Hcard x HIn).
Qed.

(** Lemma: image under an injective function preserves cardinality. *)
Lemma cardinal_Im_injective :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  (forall x y, In U S x -> In U S y -> f x = f y -> x = y) ->
  cardinal V (Im U V S f) n.
Proof.
  intros U V S f n Hcard Hinj.
  induction Hcard as [| A0 n0 Hcard0 IHHcard x Hxnin].
  - assert (Heq : Im U V (Empty_set U) f = Empty_set V).
    { apply Extensionality_Ensembles. split.
      - intros y [z Hz _Heqy]. destruct Hz.
      - intros y Hy. destruct Hy. }
    rewrite Heq. constructor.
  - assert (Hnew : ~ In V (Im U V A0 f) (f x)).
    { intros HIm. inversion HIm as [z HzA0 y Heqz]; subst.
      apply Hxnin. rewrite (Hinj x z (Add_intro2 _ A0 x) (Union_introl _ _ _ _ HzA0) Heqz).
      exact HzA0. }
    assert (Heq : Im U V (Add U A0 x) f = Add V (Im U V A0 f) (f x)).
    { apply Extensionality_Ensembles. split.
      - intros y [z Hz y_unused Heqy]. destruct Hz as [z Hz | z Hz].
        + left. exists z; auto.
        + destruct Hz. right. rewrite Heqy. constructor.
      - intros y Hy. destruct Hy as [y Hy | y Hy].
        + destruct Hy as [z Hz y_unused Heqy]. exists z; [left; exact Hz | exact Heqy].
        + destruct Hy. exists x; [right; constructor | reflexivity]. }
    rewrite Heq. apply card_add.
    + apply IHHcard.
      intros a b Ha Hb Heqab.
      apply Hinj; [left; exact Ha | left; exact Hb | exact Heqab].
    + exact Hnew.
Qed.

(** Lemma: cardinality of the subtype {x | In S x} as a Full_set
    equals the cardinality of S. *)
Lemma cardinal_subtype_full :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n ->
  cardinal {x : U | In U S x} (Full_set {x : U | In U S x}) n.
Proof.
  intros U S n Hcard.
  (* Strategy: the map [x : U | In S x] -> U via proj1_sig is injective; its
     image equals S as an ensemble of U, so |Full_set sub| = |S| = n. *)
  set (f := fun (s : {x : U | In U S x}) => proj1_sig s).
  assert (HfullFin : Finite {x : U | In U S x} (Full_set {x : U | In U S x})).
  { apply FiniteT_Finite. apply Finite_ens_type.
    exact (cardinal_finite U S n Hcard). }
  destruct (finite_cardinal _ _ HfullFin) as [m Hm].
  (* Now we know cardinal sub Full m. Show m = n. *)
  assert (HimEq : Im _ _ (Full_set {x : U | In U S x}) f = S).
  { apply Extensionality_Ensembles. split.
    - intros y Hy. destruct Hy as [s Hs y0 Heqy]. subst y0. unfold f.
      exact (proj2_sig s).
    - intros y Hy. exists (exist _ y Hy); [constructor | reflexivity]. }
  assert (Hinj : forall a b : {x : U | In U S x},
            In _ (Full_set _) a -> In _ (Full_set _) b -> f a = f b -> a = b).
  { intros [a Ha] [b Hb] _ _ Heq. unfold f in Heq. simpl in Heq. subst b.
    f_equal. apply proof_irrelevance. }
  pose proof (cardinal_Im_injective _ _ (Full_set _) f m Hm Hinj) as HimCard.
  rewrite HimEq in HimCard.
  assert (Hnm : n = m) by exact (cardinal_unicity U S n Hcard m HimCard).
  subst n. exact Hm.
Qed.

(** NOTE: [extremal_critical_pair_exists] and [exists_critical_pair_no_boundary]
    previously appeared here as Admitted lemmas.  Both statements are FALSE
    in general (the n-element antichain is a counter-example: every ordered
    pair of distinct elements is a critical pair, so no single critical pair
    can be extremal/boundary-free).  They have been deleted; Hiraguchi's
    theorem is now closed via the removable-pair approach in
    [posets/dimension/RemovablePairs.v]. *)

Section Theorems.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Definition of the set of all linear extensions *)
  Definition AllLinearExtensions : Ensemble (A -> A -> Prop) :=
    fun L => IsLinearExtension R L.

  (** Transitive closure of a relation *)
  Inductive TransitiveClosure (rel : A -> A -> Prop) : A -> A -> Prop :=
    | tc_step : forall x y, rel x y -> TransitiveClosure rel x y
    | tc_trans : forall x y z, TransitiveClosure rel x y -> TransitiveClosure rel y z -> TransitiveClosure rel x z.

  (** Transitive closure is transitive *)
  Lemma tc_is_transitive : forall rel x y z,
    TransitiveClosure rel x y -> TransitiveClosure rel y z -> TransitiveClosure rel x z.
  Proof. intros rel x y z. apply tc_trans. Qed.

  (** Minimal element definition *)
  Definition IsMinimal (x : A) (rel : A -> A -> Prop) (S : Ensemble A) : Prop :=
    In A S x /\ forall y, In A S y -> rel y x -> y = x.

  (** Lemma: Every finite non-empty set in a poset has a minimal element. *)
  Lemma exists_minimal :
    forall (S : Ensemble A) (rel : A -> A -> Prop) `{IsPoset A rel},
    Finite A S -> Inhabited A S ->
    exists x, IsMinimal x rel S.
  Proof.
    intros S_set rel_rel Hposet Hfin.
    induction Hfin.
    - (* Empty case *)
      intros Hinh. destruct Hinh as [x Hx]. inversion Hx.
    - (* Add case: Add A0 x *)
      intros Hinh.
      destruct (classic (Inhabited A A0)) as [Hinh' | Hninh'].
      + (* A0 is non-empty, use IH *)
        specialize (IHHfin Hinh').
        destruct IHHfin as [m Hm].
        (* Check if x < m *)
        destruct (classic (rel_rel x m /\ x <> m)) as [Hxm | Hnxm].
        * (* x is smaller than our current minimal m. Is x minimal? *)
          destruct (classic (IsMinimal x rel_rel (Add A A0 x))) as [Hxmin | Hxnmin].
          { exists x. auto. }
          { (* If x not minimal, there is y < x in Add A0 x. y must be in A0. *)
            (* Then y < m, which contradicts m's minimality in A0. *)
            exfalso.
            unfold IsMinimal in Hxnmin.
            apply Hxnmin.
            split.
            { right. constructor. }
            { intros y Hy Hyx.
              destruct Hy as [y Hy | y Hy].
              - (* y in A0: y <= x and x <= m, so y <= m, so y = m by minimality of m *)
                destruct Hm as [Hm_in Hm_min].
                assert (Hym : rel_rel y m).
                { eapply poset_trans; [exact Hyx | exact (proj1 Hxm)]. }
                assert (Heqym : y = m) by (apply Hm_min; auto).
                (* But then rel_rel m x (since y=m and rel_rel y x ... wait rel_rel y x not given *)
                (* We have rel_rel y x is not given; we have rel_rel y m holds and y=m *)
                (* So rel_rel m x from Hxm: rel_rel x m and x <> m *)
                (* Wait: y = m, and we need to derive a contradiction *)
                (* We know rel_rel x m (from Hxm) and y = m, and y is in A0 *)
                (* m is minimal in A0, meaning for all z in A0 with rel z m, z = m *)
                (* y is in A0 and rel y m, so y = m. But also rel y x and rel x m. *)
                (* We need: rel m x to get m = x by antisym, contradicting x <> m *)
                subst y.
                (* Now we know rel_rel m x because rel_rel m = rel_rel y and rel_rel y x = Hyx? *)
                (* Hyx : rel_rel y x, y = m, so rel_rel m x *)
                (* And Hxm : rel_rel x m /\ x <> m *)
                exfalso.
                apply (proj2 Hxm).
                eapply poset_antisym; [exact (proj1 Hxm) | exact Hyx].
              - (* y = x: rel x x and x = x trivially *)
                destruct Hy. reflexivity. }
          }
        * (* x is not strictly smaller than m. Then m is still minimal. *)
          exists m.
          destruct Hm as [Hm_in Hm_min].
          split.
          { left. exact Hm_in. }
          { intros y Hy Hym.
            destruct Hy as [y Hy | y Hy].
            - (* y in A0 *)
              apply Hm_min; auto.
            - (* y = x *)
              destruct Hy.
              (* y = x and rel_rel x m. We need x = m. *)
              (* Hnxm : ~ (rel_rel x m /\ x <> m) *)
              (* So either ~ rel_rel x m or x = m *)
              destruct (classic (x = m)) as [Heq | Hneq].
              + exact Heq.
              + exfalso. apply Hnxm. split; auto. }
      + (* A0 is empty, so S is just {x} *)
        exists x.
        split.
        { right. constructor. }
        { intros y Hy Hyx.
          destruct Hy as [y Hy | y Hy].
          - (* y in A0, but A0 is empty *)
            exfalso. apply Hninh'. exists y. exact Hy.
          - (* y = x *)
            destruct Hy. reflexivity. }
  Qed.

  (** Lemma: A sub-relation on A is still a poset if the original was. *)
  Lemma subrelation_is_poset :
    forall (rel : A -> A -> Prop) `{IsPoset A rel} (S : Ensemble A),
    IsPoset A (fun x y => x = y \/ (In A S x /\ In A S y /\ rel x y)).
  Proof.
    intros rel HR_rel S.
    constructor.
    - intro x. left. reflexivity.
    - intros x y H1 H2.
      destruct H1 as [Heq1 | [Hx [Hy Hxy]]].
      + exact Heq1.
      + destruct H2 as [Heq2 | [Hx' [Hy' Hyx]]].
        * symmetry; exact Heq2.
        * eapply poset_antisym; eauto.
    - intros x y z H1 H2.
      destruct H1 as [Heq1 | [Hx [Hy Hxy]]].
      + subst y. exact H2.
      + destruct H2 as [Heq2 | [Hy' [Hz Hyz]]].
        * subst z. right; split; [exact Hx | split; [exact Hy | exact Hxy]].
        * right; split; [exact Hx | split; [exact Hz | eapply poset_trans; eauto]].
  Qed.

  (** Lemma: Restricting a poset to a subset via the subtype yields a valid poset. *)
  Lemma subtype_is_poset :
    forall (S : Ensemble A),
    IsPoset {x : A | In A S x} (fun x y => R (proj1_sig x) (proj1_sig y)).
  Proof.
    intro S.
    constructor.
    - intro x. apply poset_refl.
    - intros [x Hx] [y Hy] H1 H2. simpl in *.
      assert (Heq : x = y) by (apply poset_antisym; assumption).
      subst. f_equal. apply proof_irrelevance.
    - intros [x Hx] [y Hy] [z Hz] H1 H2. simpl in *. eapply poset_trans; eauto.
  Qed.

  (** Lemma: Adding a minimal element to the bottom of a linear extension of a smaller set. *)
  Lemma add_minimal_to_linear_extension :
    forall (S : Ensemble A) (rel : A -> A -> Prop) `{IsPoset A rel} (m : A) (L' : A -> A -> Prop),
    IsMinimal m rel S ->
    IsLinearExtension (fun x y => In A (Subtract A S m) x /\ In A (Subtract A S m) y /\ rel x y) L' ->
    exists L, IsLinearExtension (fun x y => In A S x /\ In A S y /\ rel x y) L.
  Proof.
    intros S rel Hrel m L' [Hm_in Hm_min] HL'.
    (* Define L a b := (a = m) \/ (b <> m /\ L' a b) *)
    set (L := fun a b => a = m \/ (b <> m /\ L' a b)).
    exists L.
    (* Helper: In (Subtract S m) x <-> In S x /\ x <> m *)
    assert (Hsub : forall x, In A (Subtract A S m) x <-> (In A S x /\ x <> m)).
    { intro x; unfold Subtract, Setminus, In; split.
      - intros [Hsx Hnotm].
        split; [exact Hsx |].
        intro Heq; apply Hnotm; subst; constructor.
      - intros [Hsx Hneq].
        split; [exact Hsx |].
        intro Hsin; inversion Hsin; auto. }
    (* Helper: totality of L' *)
    assert (Htot' : forall a b, L' a b \/ L' b a) by
      apply HL'.
    (* Helper: poset of L' *)
    assert (Hpos' : IsPoset A L') by apply HL'.
    constructor.
    - (* IsTotalOrder L *)
      constructor.
      + (* IsPoset A L *)
        constructor.
        * (* Reflexivity *)
          intro a. unfold L.
          destruct (classic (a = m)) as [-> | Hne].
          -- left; reflexivity.
          -- right; split; [exact Hne | apply poset_refl].
        * (* Antisymmetry *)
          intros a b [Ha | [Hbm Ha]] [Hb | [Ham Hb]].
          -- (* a = m, b = m *) subst; reflexivity.
          -- (* a = m, a <> m *) subst; contradiction.
          -- (* b = m, b <> m *) subst; contradiction.
          -- (* both in L' *) exact (poset_antisym a b Ha Hb).
        * (* Transitivity *)
          intros a b c [Ha | [Hbm Hab]] [Hb | [Hcm Hbc]].
          -- (* a = m, _ *) left; exact Ha.
          -- (* a = m, _ *) left; exact Ha.
          -- (* b = m, b <> m *) subst; contradiction.
          -- (* both in L' *) right; split; [exact Hcm | exact (poset_trans a b c Hab Hbc)].
      + (* Total *)
        intros a b. unfold L.
        destruct (classic (a = m)) as [-> | Ham].
        * left; left; reflexivity.
        * destruct (classic (b = m)) as [-> | Hbm].
          -- right; left; reflexivity.
          -- destruct (Htot' a b) as [Hab | Hba].
             ++ left; right; split; [exact Hbm | exact Hab].
             ++ right; right; split; [exact Ham | exact Hba].
    - (* linear_extends: forall x y, (In S x /\ In S y /\ rel x y) -> L x y *)
      intros x y [HxS [HyS Hxy]].
      unfold L.
      destruct (classic (x = m)) as [-> | Hxm].
      + left; reflexivity.
      + (* x <> m, so x in Subtract S m *)
        right.
        (* First show y <> m: since x <> m, x in S, rel x m would mean x = m by minimality *)
        assert (Hym : y <> m).
        { intro Heqym; subst.
          exact (Hxm (Hm_min x HxS Hxy)). }
        split; [exact Hym |].
        (* Now use linear_extends of L': need x, y in Subtract S m and rel x y *)
        apply HL'.
        split; [| split].
        * apply Hsub; split; [exact HxS | exact Hxm].
        * apply Hsub; split; [exact HyS | exact Hym].
        * exact Hxy.
  Qed.

  Lemma at_least_one_linear_extension_finite :
    forall (S : Ensemble A) (rel : A -> A -> Prop) `{IsPoset A rel} n,
    cardinal A S n ->
    exists L, IsLinearExtension (fun x y => In A S x /\ In A S y /\ rel x y) L.
  Proof.
    intros S rel Hrel n.
    revert S.
    induction n as [n IHn] using lt_wf_ind.
    intros S Hcard.
    destruct n as [| n'].
    - (* S is empty: use Szpilrajn directly to build a linear extension of rel. *)
      assert (Hempty : forall a, ~ In A S a).
      { intros a Ha. inversion Hcard. subst. inversion Ha. }
      destruct (szpilrajn_theorem A rel) as [L [HLp [HLt HLe]]].
      exists L. constructor.
      + constructor; auto.
      + intros x y [Hx _]. exfalso. exact (Hempty x Hx).
    - (* S has cardinal S n', use exists_minimal then induction. *)
      assert (HfinS : Finite A S) by exact (cardinal_finite A S (Datatypes.S n') Hcard).
      assert (HinhS : Inhabited A S).
      { inversion Hcard as [|S0 m HcardS0 x' Hx'nin Heq Hsn'eq]. subst.
        exists x'. right. constructor. }
      destruct (@exists_minimal S rel Hrel HfinS HinhS) as [m Hmin].
      destruct Hmin as [Hm_in Hm_min].
      (* The set S minus m has cardinality n'. *)
      assert (HSub_card : cardinal A (Subtract A S m) n').
      { exact (cardinal_subtract_sn A S m n' Hcard Hm_in). }
      (* Apply IH to get a linear extension L' of the relation restricted to S-m. *)
      destruct (IHn n' (Nat.lt_succ_diag_r n') (Subtract A S m) HSub_card)
        as [L' HL'].
      (* Apply add_minimal_to_linear_extension to lift to S. *)
      apply (@add_minimal_to_linear_extension S rel Hrel m L').
      + split; assumption.
      + exact HL'.
  Qed.





















































  (** Lemma: Szpilrajn's Theorem - Every partial order can be extended to a linear order.
      Note: This is the section-local version. For a properly parameterized version
      that works outside the section, use szpilrajn_theorem defined after End Theorems. *)
  Lemma at_least_one_linear_extension :
    forall (R' : A -> A -> Prop) `{IsPoset A R'},
    exists L, IsLinearExtension R' L.
  Proof.
    intros R' HP'.
    destruct (szpilrajn_theorem A R') as [L [HLp [HLt HLe]]].
    exists L.
    constructor.
    - constructor; auto.
    - exact HLe.
  Qed.

  (** Lemma: If we add a pair (y, x) to a poset R where x, y are incomparable, 
      the transitive closure is still a partial order (specifically, it's antisymmetric). *)
  Lemma add_incomparable_is_poset_invariant :
    forall x y, Incomparable R x y ->
    forall a b,
      TransitiveClosure (fun a b => R a b \/ (a = y /\ b = x)) a b ->
      R a b \/ (R a y /\ R x b).
  Proof.
    intros x y Hinc a b Htc.
    induction Htc as [a b Hstep | a m b _ IH1 _ IH2].
    - destruct Hstep as [HRab | [Heqa Heqb]].
      + left; exact HRab.
      + subst a b. right; split; apply poset_refl.
    - destruct IH1 as [Ham | [Hay Hxm]];
      destruct IH2 as [Hmb | [Hmy Hxb]].
      + left. eapply poset_trans. exact Ham. exact Hmb.
      + right. split.
        * eapply poset_trans. exact Ham. exact Hmy.
        * exact Hxb.
      + right. split.
        * exact Hay.
        * eapply poset_trans. exact Hxm. exact Hmb.
      + exfalso. apply Hinc. left. eapply poset_trans. exact Hxm. exact Hmy.
  Qed.

  Lemma add_incomparable_is_poset :
    forall x y, Incomparable R x y ->
    IsPoset A (TransitiveClosure (fun a b => R a b \/ (a = y /\ b = x))).
  Proof.
    intros x y Hinc.
    set (ext := fun a b => R a b \/ (a = y /\ b = x)).
    pose proof (add_incomparable_is_poset_invariant x y Hinc) as Hinv.
    constructor.
    - intro a; apply tc_step; left; apply poset_refl.
    - intros a b Hab Hba.
      destruct (Hinv a b Hab) as [HRab | [Hay Hxb]],
               (Hinv b a Hba) as [HRba | [Hby Hxa]].
      + eapply poset_antisym; eauto.
      + exfalso; apply Hinc; left;
          eapply poset_trans; [eapply poset_trans; [exact Hxa | exact HRab] | exact Hby].
      + exfalso; apply Hinc; left;
          eapply poset_trans; [eapply poset_trans; [exact Hxb | exact HRba] | exact Hay].
      + exfalso; apply Hinc; left; eapply poset_trans; [exact Hxb | exact Hby].
    - intros a b c Hab Hbc; eapply tc_trans; eauto.
  Qed.

  (** Lemma: Any linear extension of a larger relation R' is also a linear extension of R. *)
  Lemma extend_to_linear :
    forall (R' : A -> A -> Prop) (L : A -> A -> Prop),
    (forall a b, R a b -> R' a b) ->
    IsLinearExtension R' L ->
    IsLinearExtension R L.
  Proof.
    intros R' L Hext Hlin.
    constructor.
    - apply Hlin.
    - intros a b Hab.
      apply Hlin.
      apply Hext. auto.
  Qed.

  (** Lemma: Any incomparable pair can be reversed in some linear extension. *)
  Theorem incomparable_extension :
    forall x y, Incomparable R x y -> exists L, IsLinearExtension R L /\ L y x.
  Proof.
    intros x y Hinc.
    (* 1. Define the extended relation R' = TC(R U {(y, x)}) *)
    set (ext_rel := fun a b => R a b \/ (a = y /\ b = x)).
    set (R' := TransitiveClosure ext_rel).
    (* 2. Show that R' is a poset *)
    assert (HP' : IsPoset A R').
    { apply add_incomparable_is_poset; auto. }
    (* 3. By Szpilrajn, there exists a linear extension L of R' *)
    destruct (@at_least_one_linear_extension R' HP') as [L HL].
    (* 4. L is also a linear extension of R *)
    exists L. split.
    - apply (extend_to_linear R' L); auto.
      intros a b Hab. apply tc_step. left. auto.
    - (* 5. L reflects (y, x) because L extends R' and (y, x) is in R' *)
      apply HL.
      apply tc_step. right. auto.
  Qed.

  (** Lemma: The intersection of all linear extensions is exactly the poset relation. *)
  Lemma all_linear_extensions_intersection :
    forall x y, (forall L, IsLinearExtension R L -> L x y) <-> R x y.
  Proof.
    intros x y. split.
    - intros Hall.
      destruct (classic (R x y)) as [Hxy | Hnxy].
      + exact Hxy.
      + (* If ~ R x y, we show there's an L such that ~ L x y *)
        destruct (classic (x = y)) as [Heq | Hneq].
        * subst. apply poset_refl.
        * (* x <> y and ~ R x y *)
          destruct (classic (R y x)) as [Hyx | Hnyx].
          { (* R y x holds: any linear extension L satisfies L y x.
               But Hall gives L x y. So L x y /\ L y x -> x = y, contradiction. *)
            destruct (at_least_one_linear_extension R) as [L_ex HL_ex].
            specialize (Hall L_ex HL_ex).
            assert (HLyx : L_ex y x) by (apply HL_ex; exact Hyx).
            pose proof HL_ex.(linear_is_total) as HL_tot.
            pose proof HL_tot.(total_is_poset) as HL_pos.
            exfalso. apply Hneq.
            exact (@poset_antisym A L_ex HL_pos x y Hall HLyx).
          }
          { (* Incomparable x y: get extension L_ex with L_ex y x *)
            destruct (incomparable_extension x y) as [L_ex [HL_ex Hlyx]].
            { unfold Incomparable. intros [HRxy | HRyx]; [exact (Hnxy HRxy) | exact (Hnyx HRyx)]. }
            specialize (Hall L_ex HL_ex).
            pose proof HL_ex.(linear_is_total) as HL_tot.
            pose proof HL_tot.(total_is_poset) as HL_pos.
            exfalso. apply Hneq.
            exact (@poset_antisym A L_ex HL_pos x y Hall Hlyx).
          }
    - intros Hxy L HL. apply HL. exact Hxy.
  Qed.

  (** Lemma: The set of all linear extensions of a poset is a realizer for it.
      This is the core of the Dushnik-Miller theorem. *)
  Lemma all_linear_extensions_is_realizer :
    IsRealizer R AllLinearExtensions.
  Proof.
    constructor.
    - intros L HL. apply HL.
    - intros x y. rewrite <- all_linear_extensions_intersection.
      unfold AllLinearExtensions. split; intros Hreal.
      + intros L HL. apply Hreal, HL.
      + intros L HL. apply Hreal, HL.
  Qed.

  (** Helper: FiniteT Prop using propositional extensionality + classical logic.
      Uses [excluded_middle_informative] from [ClassicalDescription] as the
      Sort-Set classifier (Coq 9.x rejects [match classic P]). *)
  Lemma FiniteT_Prop : FiniteT Prop.
  Proof.
    apply (bij_finite bool Prop (fun b => if b then True else False)).
    - apply FiniteT_bool.
    - set (g := fun (P : Prop) =>
        if excluded_middle_informative P then true else false).
      eapply intro_invertible with g.
      + intro b; unfold g.
        destruct b; simpl.
        * destruct (excluded_middle_informative True) as [_ | HnT].
          -- reflexivity.
          -- exfalso; apply HnT; trivial.
        * destruct (excluded_middle_informative False) as [HF | _].
          -- exact (False_rect _ HF).
          -- reflexivity.
      + intro P; unfold g.
        destruct (excluded_middle_informative P) as [HP | HnP]; simpl.
        * apply propositional_extensionality; tauto.
        * apply propositional_extensionality; tauto.
  Qed.

  (* Dead code preserved as a comment for future porting:
    apply (bij_finite bool Prop (fun b => if b then True else False)).
    - apply FiniteT_bool.
    - set (g := fun (P : Prop) =>
        match classic P with
        | or_introl _ => true
        | or_intror _ => false
        end).
      eapply intro_invertible with g.
      + intro b; unfold g.
        destruct b; simpl.
        * destruct (classic True) as [_ | H].
          -- reflexivity.
          -- exfalso; apply H; trivial.
        * destruct (classic False) as [H | _].
          -- exact (False_rect _ H).
          -- reflexivity.
      + (* f (g P) = P *)
        intro P; unfold g.
        destruct (classic P) as [HP | HnP]; simpl.
        * (* P holds, g P = true, f true = True *)
          apply propositional_extensionality; tauto.
        * (* P doesn't hold, g P = false, f false = False *)
          apply propositional_extensionality; tauto.
  *)

  (** Lemma: If the base set A is finite, the set of all linear extensions is also finite. *)
  Lemma all_linear_extensions_finite :
    forall n, cardinal A (Full_set A) n ->
    Finite (A -> A -> Prop) AllLinearExtensions.
  Proof.
    intros n Hcard.
    (* Step 1: A is Finite as an ensemble *)
    assert (HfinA : Finite A (Full_set A)) by
      (apply cardinal_finite with n; exact Hcard).
    (* Step 2: {x : A | In (Full_set A) x} is FiniteT *)
    apply Finite_ens_type in HfinA.
    (* Step 3: Establish FiniteT A via bijection with {x | Full_set A x} *)
    assert (HftA : FiniteT A).
    { apply (bij_finite {x : A | In A (Full_set A) x} A
        (fun s => proj1_sig s)).
      - exact HfinA.
      - exists (fun a => exist _ a (Full_intro A a)).
        + intros [x Hx]. simpl.
          destruct (proof_irrelevance _ Hx (Full_intro A x)).
          reflexivity.
        + intro a. simpl. reflexivity. }
    (* Step 4: FiniteT (A -> Prop) *)
    assert (HftAP : FiniteT (A -> Prop)).
    { apply finite_exp; [exact HftA | apply FiniteT_Prop]. }
    (* Step 5: FiniteT (A -> A -> Prop) *)
    assert (HftAAP : FiniteT (A -> A -> Prop)).
    { apply finite_exp; [exact HftA | exact HftAP]. }
    (* Step 6: Any ensemble of (A -> A -> Prop) is Finite when the type is FiniteT *)
    apply FiniteT_Finite.
    exact HftAAP.
  Qed.

  (** Theorem: Dushnik-Miller (1941) - Every finite poset has a well-defined dimension *)
  Theorem dushnik_miller_exists :
    forall n, cardinal A (Full_set A) n ->
    exists d, inhabited (PosetDimension R d).
  Proof.
    intros n Hfin.
    pose proof all_linear_extensions_is_realizer as Hrealizer.
    pose proof (all_linear_extensions_finite n Hfin) as Hfinite.
    destruct (finite_cardinal _ _ Hfinite) as [m Hcard_m].
    assert (Hgen : forall k,
        (exists r : Ensemble (A -> A -> Prop),
          IsRealizer R r /\ cardinal (A -> A -> Prop) r k) ->
        exists d, inhabited (PosetDimension R d)).
    { intro k. induction k as [k IHk] using lt_wf_ind.
      intros [r [Hr_real Hr_card]].
      destruct (classic (exists r' : Ensemble (A -> A -> Prop),
          exists k', IsRealizer R r' /\ cardinal (A -> A -> Prop) r' k' /\ k' < k))
        as [[r' [k' [Hr'_real [Hr'_card Hlt]]]] | Hmin].
      - apply (IHk k' Hlt). exists r'; split; assumption.
      - exists k. constructor.
        refine {|
          dimension_realizer    := r;
          dimension_is_realizer := Hr_real;
          dimension_cardinality := Hr_card;
          dimension_is_minimum  := _
        |}.
        intros r'' n'' Hr''_real Hr''_card.
        destruct (Nat.le_gt_cases k n'') as [Hle | Hgt].
        + exact Hle.
        + exfalso. apply Hmin. exists r''. exists n''.
          split; [exact Hr''_real | split; [exact Hr''_card | exact Hgt]]. }
    apply (Hgen m). exists AllLinearExtensions.
    split; [exact Hrealizer | exact Hcard_m].
  Qed.
  (* Original proof body retained for porting reference:
    intros n Hfin.
    (* The set of all linear extensions is a finite realizer *)
    pose proof all_linear_extensions_is_realizer as Hrealizer.
    pose proof (all_linear_extensions_finite n Hfin) as Hfinite.
    (* Extract cardinal of AllLinearExtensions *)
    destruct (finite_cardinal _ _ Hfinite) as [m Hcard_m].
    (* Key lemma: any realizer of size m gives rise to a PosetDimension.
       We prove this by strong induction on m.
       The idea: if m is already minimum, we're done. Otherwise find a smaller
       realizer and apply the induction hypothesis. *)
    assert (Hgen : forall k,
        (exists r : Ensemble (A -> A -> Prop),
          IsRealizer R r /\ cardinal (A -> A -> Prop) r k) ->
        exists d, inhabited (PosetDimension R d)).
    { induction k as [k IHk] using lt_wf_ind.
      intros [r [Hr_real Hr_card]].
      (* Is k the minimum realizer size? *)
      destruct (classic (exists r' : Ensemble (A -> A -> Prop),
          exists k', IsRealizer R r' /\ cardinal (A -> A -> Prop) r' k' /\ k' < k))
        as [[r' [k' [Hr'_real [Hr'_card Hlt]]]] | Hmin].
      - (* There is a strictly smaller realizer r' of size k'. Use IH. *)
        apply (IHk k'); [exact Hlt | exists r'; split; [exact Hr'_real | exact Hr'_card]].
      - (* k is the minimum: every realizer has size >= k.
           Build a PosetDimension. *)
        exists k.
        apply not_ex_all_not in Hmin.
        constructor.
        exact {|
          dimension_realizer    := r;
          dimension_is_realizer := Hr_real;
          dimension_cardinality := Hr_card;
          dimension_is_minimum  :=
            fun r'' n'' Hr''_real Hr''_card =>
              (* Suppose n'' < k. Then Hmin applied to r'' gives a contradiction. *)
              match Nat.le_gt_cases k n'' with
              | or_introl H => H
              | or_intror H =>
                  let Hcontra := Hmin r'' in
                  False_rect _ (Hcontra (ex_intro _ n''
                    (conj Hr''_real (conj Hr''_card H))))
              end
        |}.
    }
    apply (Hgen m).
    exists AllLinearExtensions.
    split; [exact Hrealizer | exact Hcard_m].
  *)


  (** Theorem: Subposet Dimension Monotonicity
      If Q is the subposet of P induced by S, then dim(Q) ≤ dim(P).
      We use the subtype {x : A | In A S x} as the carrier for Q. *)
  (* NOTE: original proof of subposet_dimension_le uses primitive
     projections + section-arg quirks that no longer match Coq 9.x.
     Statement intact; admitted. *)
  Theorem subposet_dimension_le :
    forall (S : Ensemble A) (d_p : nat),
    PosetDimension R d_p ->
    exists d_q,
      inhabited (@PosetDimension {x : A | In A S x}
                  (fun x y => R (proj1_sig x) (proj1_sig y))
                  d_q) /\
      d_q <= d_p.
  Proof.
    intros S d_p HdP.
    set (Q := fun (x y : {a : A | In A S a}) => R (proj1_sig x) (proj1_sig y)).
    pose proof (subtype_is_poset S) as HQ_poset.
    set (rP := dimension_realizer HdP).
    pose proof (dimension_is_realizer HdP) as HrP_real.
    pose proof (dimension_cardinality HdP) as HrP_card.
    set (proj_S := fun (LP : A -> A -> Prop)
                       (x y : {a : A | In A S a}) =>
                     LP (proj1_sig x) (proj1_sig y)).
    set (rQ := Im (A -> A -> Prop)
                  ({x : A | In A S x} -> {x : A | In A S x} -> Prop)
                  rP proj_S).
    (* Step 1: rQ is a realizer of Q *)
    assert (HrQ_real : @IsRealizer {x : A | In A S x} Q rQ).
    { constructor.
      - intros LQ HLQ.
        destruct HLQ as [LP HLP_in LQ' HeqLQ]. subst LQ'.
        assert (HLP_lin : IsLinearExtension R LP).
        { exact (realizer_linear HrP_real LP HLP_in). }
        pose proof (linear_is_total HLP_lin) as HLP_tot.
        pose proof (total_is_poset (IsTotalOrder := HLP_tot)) as HLP_pos.
        constructor.
        + constructor.
          * constructor.
            -- intro x. unfold proj_S. apply (poset_refl (R := LP)).
            -- intros [x Hx] [y Hy] H1 H2. unfold proj_S in *. simpl in *.
               assert (Heqxy : x = y).
               { apply (@poset_antisym A LP HLP_pos); assumption. }
               subst y. f_equal. apply proof_irrelevance.
            -- intros [x Hx] [y Hy] [z Hz] H1 H2. unfold proj_S in *. simpl in *.
               apply (@poset_trans A LP HLP_pos) with y; assumption.
          * intros [x Hx] [y Hy]. unfold proj_S. simpl.
            exact (total_comparable (IsTotalOrder := HLP_tot) x y).
        + intros [x Hx] [y Hy] HQxy. unfold proj_S. simpl.
          exact (linear_extends HLP_lin _ _ HQxy).
      - intros [x Hx] [y Hy]. split.
        + intros HQxy LQ HLQ.
          destruct HLQ as [LP HLP_in LQ' HeqLQ]. subst LQ'.
          unfold proj_S. simpl.
          apply (realizer_intersection HrP_real). exact HQxy. exact HLP_in.
        + intro Hall. unfold Q. simpl.
          apply (realizer_intersection HrP_real).
          intros LP HLP_in.
          specialize (Hall (proj_S LP)).
          apply Hall. exists LP; [exact HLP_in | reflexivity]. }
    (* Step 2: |rQ| ≤ d_p *)
    destruct (cardinal_Im_le_local
                (A -> A -> Prop)
                ({x : A | In A S x} -> {x : A | In A S x} -> Prop)
                rP proj_S d_p HrP_card)
      as [n [HrQ_card HrQ_le]].
    (* Step 3: WF induction on n to extract minimum realizer of Q *)
    assert (Hgen : forall k,
        (exists (r : Ensemble ({x : A | In A S x} -> {x : A | In A S x} -> Prop)),
          @IsRealizer {x : A | In A S x} Q r /\
          cardinal _ r k) ->
        exists d_q,
          inhabited (@PosetDimension {x : A | In A S x} Q d_q) /\
          d_q <= k).
    { intro k. induction k as [k IHk] using lt_wf_ind.
      intros [r [Hr_real Hr_card]].
      destruct (classic (exists
          (r' : Ensemble ({x : A | In A S x} -> {x : A | In A S x} -> Prop)) k',
          @IsRealizer {x : A | In A S x} Q r' /\
          cardinal _ r' k' /\ k' < k))
        as [[r' [k' [Hr'_real [Hr'_card Hlt]]]] | Hmin].
      - destruct (IHk k' Hlt) as [d_q [HdQ Hle]].
        + exists r'. split; assumption.
        + exists d_q. split; [exact HdQ | lia].
      - exists k. split; [| lia].
        constructor.
        refine {|
          dimension_realizer    := r;
          dimension_is_realizer := Hr_real;
          dimension_cardinality := Hr_card;
          dimension_is_minimum  := _
        |}.
        intros r'' n'' Hr''_real Hr''_card.
        destruct (Nat.le_gt_cases k n'') as [Hle | Hgt].
        + exact Hle.
        + exfalso. apply Hmin. exists r''. exists n''.
          split; [exact Hr''_real | split; [exact Hr''_card | exact Hgt]]. }
    destruct (Hgen n) as [d_q [HdQ Hle]].
    { exists rQ. split; [exact HrQ_real | exact HrQ_card]. }
    exists d_q. split; [exact HdQ | lia].
  Qed.
  (* Original proof body, retained for porting reference:
    intros S d_p HdP.
    (* Q is the subtype relation *)
    set (Q := fun (x y : {a : A | In A S a}) => R (proj1_sig x) (proj1_sig y)).
    (* rP: the canonical realizer of P of size d_p *)
    set (rP := dimension_realizer (R := R) (d := d_p)).
    assert (HrP_card : cardinal (A -> A -> Prop) rP d_p) by exact (dimension_cardinality (R := R) (d := d_p))
    (* proj_S: maps each LP : A -> A -> Prop to its restriction to the subtype *)
    set (proj_S := fun (LP : A -> A -> Prop)
                       (x y : {a : A | In A S a}) =>
                     LP (proj1_sig x) (proj1_sig y)).
    (* rQ: the image of rP under proj_S *)
    set (rQ := Im (A -> A -> Prop)
                  ({x : A | In A S x} -> {x : A | In A S x} -> Prop)
                  rP proj_S).
    (* Step 1: rQ is a realizer of Q *)
    assert (HrQ_real : @IsRealizer {x : A | In A S x} Q (subtype_is_poset S) rQ).
    { constructor.
      + (* Every element of rQ is a linear extension of Q *)
        intros LQ [LP HLP_in ->].
        (* LP is a linear extension of R *)
        assert (HLP_lin : IsLinearExtension R LP) by exact ((dimension_is_realizer (R := R) (d := d_p)).(realizer_linear) LP HLP_in)
        constructor.
        * (* proj_S LP is a total order on the subtype *)
          constructor.
          -- (* IsPoset *)
             constructor.
             ++ intro x. unfold proj_S. apply poset_refl.
             ++ intros [x Hx] [y Hy] H1 H2. unfold proj_S in *. simpl in *.
                assert (Heq : x = y) by (apply poset_antisym; assumption).
                subst. f_equal. apply proof_irrelevance.
             ++ intros [x Hx] [y Hy] [z Hz] H1 H2. unfold proj_S in *. simpl in *.
                eapply poset_trans; eauto.
          -- (* Totality *)
             intros [x Hx] [y Hy]. unfold proj_S. simpl.
             exact (HLP_lin.(linear_is_total).(total_comparable) x y).
        * (* proj_S LP extends Q *)
          intros [x Hx] [y Hy] HQxy. unfold proj_S. simpl.
          exact (HLP_lin.(linear_extends) x y HQxy).
      + (* Intersection property: Q x y ↔ ∀ LQ ∈ rQ, LQ x y *)
        intros [x Hx] [y Hy]. split.
        * (* Q x y → ∀ LQ ∈ rQ, LQ x y *)
          intros HQxy LQ [LP HLP_in ->].
          unfold proj_S. simpl.
          exact ((dimension_is_realizer (R := R) (d := d_p)).(realizer_intersection x y).(proj1) HQxy LP HLP_in).
        * (* ∀ LQ ∈ rQ, LQ x y → Q x y *)
          intro Hall.
          apply (dimension_is_realizer (R := R) (d := d_p)).(realizer_intersection x y).(proj2).
          intros LP HLP_in.
          exact (Hall (proj_S LP) (ex_intro _ LP (conj HLP_in eq_refl))). }
    (* Step 2: |rQ| ≤ d_p because rQ = Im rP proj_S *)
    destruct (cardinal_Im_le_local
                (A -> A -> Prop)
                ({x : A | In A S x} -> {x : A | In A S x} -> Prop)
                rP proj_S d_p HrP_card)
      as [n [HrQ_card HrQ_le]].
    (* Step 3: By strong induction on n, extract the minimum realizer of Q *)
    assert (Hgen : forall k,
        (exists (r : Ensemble ({x : A | In A S x} -> {x : A | In A S x} -> Prop)),
          @IsRealizer {x : A | In A S x} Q (subtype_is_poset S) r /\
          cardinal _ r k) ->
        exists d_q,
          inhabited (@PosetDimension {x : A | In A S x} Q (subtype_is_poset S) d_q) /\
          d_q <= k).
    { induction k as [k IHk] using lt_wf_ind.
      intros [r [Hr_real Hr_card]].
      destruct (classic (exists
          (r' : Ensemble ({x : A | In A S x} -> {x : A | In A S x} -> Prop)) k',
          @IsRealizer {x : A | In A S x} Q (subtype_is_poset S) r' /\
          cardinal _ r' k' /\ k' < k))
        as [[r' [k' [Hr'_real [Hr'_card Hlt]]]] | Hmin].
      - (* Strictly smaller realizer exists; apply IH *)
        destruct (IHk k' Hlt (ex_intro _ r' (conj Hr'_real Hr'_card)))
          as [d_q [HdQ Hle]].
        exact (ex_intro _ d_q (conj HdQ (Nat.le_trans d_q k' k Hle (Nat.lt_le_incl k' k Hlt)))).
      - (* k is the minimum realizer size: build PosetDimension *)
        apply not_ex_all_not in Hmin.
        exists k.
        split.
        + constructor.
          exact {|
            dimension_realizer    := r;
            dimension_is_realizer := Hr_real;
            dimension_cardinality := Hr_card;
            dimension_is_minimum  :=
              fun r'' n'' Hr''_real Hr''_card =>
                match Nat.le_gt_cases k n'' with
                | or_introl H => H
                | or_intror H =>
                    let Hcontra := Hmin r'' in
                    False_rect _ (Hcontra (ex_intro _ n''
                      (conj Hr''_real (conj Hr''_card H))))
                end
          |}.
        + exact (Nat.le_refl k). }
    destruct (Hgen n (ex_intro _ rQ (conj HrQ_real HrQ_card)))
      as [d_q [HdQ Hle]].
    exact (ex_intro _ d_q (conj HdQ (Nat.le_trans d_q n d_p Hle HrQ_le))).
  *)

  (** ============================================================
      Helpers for [extension_through_critical_pair].

      The construction (informal):
        Given critical pair (x',y') and a d'-element realizer r' of
        R restricted to S' = A \ {x',y'}:

        * For each L' in r', extend L' (lifted to A) together with R
          and the forced edge (x',y') to a total order L'_full on A
          using szpilrajn.  Call the resulting d'-element set r_lifted.

        * Take L_extra := szpilrajn(TC(R u {(y',x')})), a total order
          reversing the critical pair.

        * Return r := Add r_lifted L_extra of cardinality d' + 1.

      Each step relies on two genuinely non-trivial facts that we
      isolate as separate lemmas:

        - [lift_and_force_is_poset]:  TC(R u L'_lift u {(x',y')}) is
          a poset (so Szpilrajn applies).  Admitted: the path-invariant
          argument has several mixed-step cases beyond the scope here.

        - [extend_through_cp_construction]:  given r' realizing
          R|_{S'} and L_extra reversing (x',y'), there exists a
          d'-element set r_lifted of linear extensions of R such that
          every L in r_lifted satisfies L x' y' and the restriction
          of (r_lifted u {L_extra}) realizes R.  Admitted: the
          realizer argument needs the full critical-pair separation
          analysis spelled out in the design spec.

      Given these, the outer construction of [extension_through_critical_pair]
      closes structurally with Qed. *)

  Lemma lift_and_force_is_poset :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension
      (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
    IsPoset A
      (clos_trans A
         (fun a b =>
            R a b
            \/ (exists (ha : In A S' a) (hb : In A S' b),
                  L' (exist _ a ha) (exist _ b hb))
            \/ (a = x' /\ b = y'))).
  Proof.
    intros x' y' S' L' Hcp HS'_eq HL'.
    set (L'_lift := fun a b =>
           exists (ha : In A S' a) (hb : In A S' b),
             L' (exist _ a ha) (exist _ b hb)).
    set (step := fun a b => R a b \/ L'_lift a b \/ (a = x' /\ b = y')).
    fold L'_lift.
    change (IsPoset A (clos_trans A step)).
    (* Extract poset/totality structure of L' *)
    assert (HL'_pos : IsPoset {a : A | In A S' a}
              (fun a b => L' a b)) by
      exact (linear_is_total HL').(total_is_poset).
    assert (HL'_tot : forall a b : {a : A | In A S' a}, L' a b \/ L' b a) by
      exact (linear_is_total HL').(total_comparable).
    assert (HL'_ext : forall a b : {a : A | In A S' a},
              R (proj1_sig a) (proj1_sig b) -> L' a b) by
      exact (linear_extends HL').
    (* Derive x' ∉ S' and y' ∉ S' from HS'_eq *)
    assert (Hx'_notin : ~ In A S' x').
    { intro Hin. rewrite HS'_eq in Hin.
      destruct Hin as [[Hfull Hnotx'] Hnoty'].
      apply Hnotx'. constructor. }
    assert (Hy'_notin : ~ In A S' y').
    { intro Hin. rewrite HS'_eq in Hin.
      destruct Hin as [_ Hnoty'].
      apply Hnoty'. constructor. }
    (* Helpers: L'_lift endpoints are in S' *)
    assert (HL'_lift_in_S' : forall a b, L'_lift a b -> In A S' a /\ In A S' b).
    { intros a b [ha [hb _]]. split; assumption. }
    (* Critical pair facts *)
    assert (Hinc : Incomparable R x' y') by exact (critical_incomparable Hcp).
    assert (Hnxy : ~ R x' y') by (intro; apply Hinc; left; assumption).
    assert (Hnyx : ~ R y' x') by (intro; apply Hinc; right; assumption).
    (* L'_lift is transitive (inherits from L' being a poset) *)
    assert (HL'_lift_trans : forall a b c,
              L'_lift a b -> L'_lift b c -> L'_lift a c).
    { intros a b c [ha [hb HLab]] [hb' [hc HLbc]].
      exists ha, hc.
      assert (Hhb : hb = hb') by apply proof_irrelevance.
      subst hb.
      eapply (HL'_pos.(poset_trans)); eauto. }
    (* L'_lift is reflexive on S' *)
    assert (HL'_lift_refl : forall a (ha : In A S' a), L'_lift a a).
    { intros a ha. exists ha, ha.
      exact (HL'_pos.(poset_refl) (exist _ a ha)). }
    (* L' extends R on S' x S' *)
    assert (HL'_lift_R : forall a b (ha : In A S' a) (hb : In A S' b),
              R a b -> L'_lift a b).
    { intros a b ha hb HRab.
      exists ha, hb. apply HL'_ext. simpl. exact HRab. }
    (* L'_lift antisymmetric *)
    assert (HL'_lift_antisym : forall a b,
              L'_lift a b -> L'_lift b a -> a = b).
    { intros a b [ha [hb HLab]] [hb' [ha' HLba]].
      assert (Hhb : hb = hb') by apply proof_irrelevance.
      assert (Hha : ha = ha') by apply proof_irrelevance.
      subst hb ha.
      pose proof HL'_pos.(poset_antisym) as HAS.
      assert (HE : exist (fun z => In A S' z) a ha'
                 = exist (fun z => In A S' z) b hb').
      { apply HAS; eauto. }
      exact (f_equal (@proj1_sig _ _) HE). }

    (* ---------- Path invariant ----------
       For any TC-path a -->* b, one of three cases holds:
         (J1) R a b
         (J2) ∃ m1 m2 ∈ S', (R a m1 ∨ a = m1) ∧ L'_lift m1 m2 ∧
                            (R m2 b ∨ m2 = b)
              [a path that has an L'_lift segment inside S', with optional
               R prefix into S' and R suffix out of S']
         (J3) R a x' /\ R y' b
       The forced edge (x', y') instantiates (J3) by R-reflexivity. *)
    set (Inv := fun a b =>
                  R a b
               \/ (exists m1 m2 : A,
                     In A S' m1 /\ In A S' m2 /\
                     (R a m1 \/ a = m1) /\
                     L'_lift m1 m2 /\
                     (R m2 b \/ m2 = b))
               \/ (R a x' /\ R y' b)).
    (* Helpers for J2: pack/unpack and basic R-extensions *)
    assert (HInv_R_left : forall a b c, R a b -> Inv b c -> Inv a c).
    { intros a b c HRab HI.
      destruct HI as [HRbc | [[m1 [m2 [Hm1 [Hm2 [Hpref [HLL Hsuf]]]]]] | [HRbx HRyc]]].
      - left. eapply poset_trans; eauto.
      - right. left. exists m1, m2. split; [exact Hm1|]. split; [exact Hm2|].
        split.
        + destruct Hpref as [HRbm1 | Heqbm1].
          * left. eapply poset_trans; eauto.
          * left. rewrite <- Heqbm1. exact HRab.
        + split; [exact HLL | exact Hsuf].
      - right. right. split; [eapply poset_trans; eauto | exact HRyc]. }
    assert (HInv_R_right : forall a b c, Inv a b -> R b c -> Inv a c).
    { intros a b c HI HRbc.
      destruct HI as [HRab | [[m1 [m2 [Hm1 [Hm2 [Hpref [HLL Hsuf]]]]]] | [HRax HRyb]]].
      - left. eapply poset_trans; eauto.
      - right. left. exists m1, m2. split; [exact Hm1|]. split; [exact Hm2|].
        split; [exact Hpref|]. split; [exact HLL|].
        destruct Hsuf as [HRm2b | Heqm2b].
        + left. eapply poset_trans; eauto.
        + left. rewrite Heqm2b. exact HRbc.
      - right. right. split; [exact HRax | eapply poset_trans; eauto]. }
    (* Key compression lemma: a chain in J2 starting and ending in S' compresses
       to L'_lift. *)
    assert (HInv_compress : forall m1 m2 b,
              In A S' m1 -> In A S' m2 -> In A S' b ->
              (R m1 m2 \/ m1 = m2) -> L'_lift m2 b -> L'_lift m1 b).
    { intros m1 m2 b Hm1 Hm2 Hb [HRm1m2 | Heq] HLL.
      - assert (HL12 : L'_lift m1 m2) by apply (HL'_lift_R m1 m2 Hm1 Hm2 HRm1m2).
        eapply HL'_lift_trans; eauto.
      - subst m2. exact HLL. }
    assert (HInv_compress' : forall a m1 m2,
              In A S' a -> In A S' m1 -> In A S' m2 ->
              L'_lift a m1 -> (R m1 m2 \/ m1 = m2) -> L'_lift a m2).
    { intros a m1 m2 Ha Hm1 Hm2 HLL [HRm1m2 | Heq].
      - assert (HL12 : L'_lift m1 m2) by apply (HL'_lift_R m1 m2 Hm1 Hm2 HRm1m2).
        eapply HL'_lift_trans; eauto.
      - subst m2. exact HLL. }
    assert (Hinv : forall a b,
              clos_trans A step a b -> Inv a b).
    { intros a b Hab.
      induction Hab as [a b Hstep | a m b _ IH1 _ IH2].
      - (* Base case *)
        destruct Hstep as [HR | [HLL | [Heqax Heqby]]].
        + left. exact HR.
        + right. left.
          destruct (HL'_lift_in_S' a b HLL) as [Ha_in Hb_in].
          exists a, b. split; [exact Ha_in|]. split; [exact Hb_in|].
          split; [right; reflexivity|]. split; [exact HLL | right; reflexivity].
        + subst a b. right. right. split; apply poset_refl.
      - (* Transitive case: combine IH1: Inv a m and IH2: Inv m b *)
        destruct IH1 as [HRam | [HJ2am | [HRax HRym]]];
        destruct IH2 as [HRmb | [HJ2mb | [HRmx HRyb]]].
        + (* J1, J1: R a m, R m b *) left. eapply poset_trans; eauto.
        + (* J1, J2 *) eapply HInv_R_left; [exact HRam | right; left; exact HJ2mb].
        + (* J1, J3: R a m, R m x' /\ R y' b *)
          right. right. split.
          * eapply poset_trans; eauto.
          * exact HRyb.
        + (* J2, J1: extend J2 by R on right *)
          eapply HInv_R_right; [right; left; exact HJ2am | exact HRmb].
        + (* J2, J2: compose two J2's *)
          destruct HJ2am as [p1 [p2 [Hp1 [Hp2 [HprefA [HLLp HsufA]]]]]].
          destruct HJ2mb as [q1 [q2 [Hq1 [Hq2 [HprefB [HLLq HsufB]]]]]].
          (* Need to show ∃m1 m2, all in S', ... L'_lift m1 m2 ... *)
          (* The middle (p2, m, q1) collapses: R_or_eq p2 m, R_or_eq m q1.
             Both p2, q1 ∈ S'. If R p2 q1 or p2 = q1, L'_lift (or eq) p2 q1.
             Then L'_lift p1 p2, L'_lift_or_eq p2 q1, L'_lift q1 q2 →
             L'_lift p1 q2.  J2 with m1=p1, m2=q2. *)
          assert (Hp2_R_q1 : R p2 q1 \/ p2 = q1).
          { destruct HsufA as [HRp2m | Heqp2m];
            destruct HprefB as [HRmq1 | Heqmq1].
            - left. eapply poset_trans; eauto.
            - left. rewrite <- Heqmq1. exact HRp2m.
            - left. rewrite Heqp2m. exact HRmq1.
            - right. rewrite Heqp2m. exact Heqmq1. }
          assert (HLLp1q2 : L'_lift p1 q2).
          { (* L'_lift p1 p2, R_or_eq p2 q1, L'_lift q1 q2 → L'_lift p1 q2 *)
            assert (HLLpq1 : L'_lift p1 q1).
            { apply (HInv_compress' p1 p2 q1 Hp1 Hp2 Hq1 HLLp Hp2_R_q1). }
            eapply HL'_lift_trans; eauto. }
          right. left. exists p1, q2. split; [exact Hp1|]. split; [exact Hq2|].
          split; [exact HprefA|]. split; [exact HLLp1q2 | exact HsufB].
        + (* J2, J3: R a m → ... → p2 → m → x' / y' → b
             a → p1 → p2 → m  via J2; m → x' /\ y' → b via J3.
             From HsufA: R_or_eq p2 m. R m x'. So R p2 x' (or p2 = m and R m x').
             Either way R p2 x'. p2 ∈ S' so p2 ≠ x', Strict, critical_down: R p2 y'.
             Then R y' b (from J3). R p2 y' /\ R y' b → R p2 b.
             So state: R_or_eq a p1, L'_lift p1 p2, R p2 b. J2! *)
          destruct HJ2am as [p1 [p2 [Hp1 [Hp2 [HprefA [HLLp HsufA]]]]]].
          assert (HRp2x : R p2 x').
          { destruct HsufA as [HRp2m | Heqp2m].
            - eapply poset_trans; eauto.
            - rewrite Heqp2m. exact HRmx. }
          assert (Hp2_nex : p2 <> x').
          { intro Heq. rewrite Heq in Hp2. apply (Hx'_notin Hp2). }
          assert (HRp2y : R p2 y').
          { apply (critical_down Hcp). split; [exact HRp2x | exact Hp2_nex]. }
          assert (HRp2b : R p2 b).
          { eapply poset_trans; eauto. }
          right. left. exists p1, p2. split; [exact Hp1|]. split; [exact Hp2|].
          split; [exact HprefA|]. split; [exact HLLp | left; exact HRp2b].
        + (* J3, J1: R a x' /\ R y' m, R m b *)
          right. right. split.
          * exact HRax.
          * eapply poset_trans; eauto.
        + (* J3, J2: R a x' /\ R y' m, J2 m b *)
          destruct HJ2mb as [q1 [q2 [Hq1 [Hq2 [HprefB [HLLq HsufB]]]]]].
          assert (HRyq1 : R y' q1).
          { destruct HprefB as [HRmq1 | Heqmq1].
            - eapply poset_trans; eauto.
            - rewrite <- Heqmq1. exact HRym. }
          assert (Hq1_ney : q1 <> y').
          { intro Heq. rewrite Heq in Hq1. apply (Hy'_notin Hq1). }
          assert (HRxq1 : R x' q1).
          { apply (critical_up Hcp). split; [exact HRyq1 | auto]. }
          assert (HRaq1 : R a q1).
          { eapply poset_trans; eauto. }
          right. left. exists q1, q2. split; [exact Hq1|]. split; [exact Hq2|].
          split; [left; exact HRaq1|]. split; [exact HLLq | exact HsufB].
        + (* J3, J3: R a x' /\ R y' m, R m x' /\ R y' b → R y' x' contradiction *)
          exfalso. apply Hnyx.
          eapply poset_trans; [exact HRym | exact HRmx]. }

    constructor.
    - (* Reflexivity *)
      intro a. apply t_step. left. apply poset_refl.
    - (* Antisymmetry *)
      intros a b Hab Hba.
      pose proof (Hinv a b Hab) as Iab.
      pose proof (Hinv b a Hba) as Iba.
      destruct Iab as [HRab | [HJ2ab | [HRax HRyb]]];
      destruct Iba as [HRba | [HJ2ba | [HRbx HRya]]].
      + (* J1, J1: R a b, R b a *) eapply poset_antisym; eauto.
      + (* J1, J2: R a b ; J2(b, a) = ∃q1 q2 ∈ S', ... b → q1 → q2 → a *)
        destruct HJ2ba as [q1 [q2 [Hq1 [Hq2 [Hpref [HLLq Hsuf]]]]]].
        (* Combine: R a b, R_or_eq b q1, L'_lift q1 q2, R_or_eq q2 a.
           Derive R q2 q1 (via R q2 a, R a b, R_or_eq b q1).
           Then L'_lift q2 q1, antisym → q1 = q2.  Then path is
           R a b, R_or_eq b q1, R_or_eq q1=q2 a → R a b and R b a → a = b. *)
        assert (HRq2_q1 : R q2 q1).
        { assert (HRq2b : R q2 b).
          { destruct Hsuf as [HRq2a | Heqq2a].
            - eapply poset_trans; eauto.
            - rewrite Heqq2a. exact HRab. }
          destruct Hpref as [HRbq1 | Heqbq1].
          - eapply poset_trans; eauto.
          - rewrite <- Heqbq1. exact HRq2b. }
        assert (HLLq2q1 : L'_lift q2 q1)
          by exact (HL'_lift_R q2 q1 Hq2 Hq1 HRq2_q1).
        assert (Heq_q1q2 : q1 = q2)
          by exact (HL'_lift_antisym q1 q2 HLLq HLLq2q1).
        (* Now reduce: q1 = q2. Path: b → q1 → q1 → a. So R_or_eq b q1, R_or_eq q1 a. *)
        rewrite <- Heq_q1q2 in Hsuf.
        (* Hsuf : R q1 a \/ q1 = a *)
        assert (HRba' : R b a).
        { destruct Hpref as [HRbq1 | Heqbq1];
          destruct Hsuf as [HRq1a | Heqq1a].
          - eapply poset_trans; eauto.
          - rewrite <- Heqq1a. exact HRbq1.
          - rewrite Heqbq1. exact HRq1a.
          - rewrite Heqbq1. rewrite Heqq1a. apply poset_refl. }
        eapply poset_antisym; eauto.
      + (* J1, J3: R a b, R b x' /\ R y' a → R y' x' contradiction *)
        exfalso. apply Hnyx.
        eapply poset_trans; [exact HRya | eapply poset_trans; eauto].
      + (* J2, J1: symmetric to J1, J2 *)
        destruct HJ2ab as [p1 [p2 [Hp1 [Hp2 [Hpref [HLLp Hsuf]]]]]].
        assert (HRp2_p1 : R p2 p1).
        { assert (HRp2a : R p2 a).
          { destruct Hsuf as [HRp2b | Heqp2b].
            - eapply poset_trans; eauto.
            - rewrite Heqp2b. exact HRba. }
          destruct Hpref as [HRap1 | Heqap1].
          - eapply poset_trans; eauto.
          - rewrite <- Heqap1. exact HRp2a. }
        assert (HLLp2p1 : L'_lift p2 p1)
          by exact (HL'_lift_R p2 p1 Hp2 Hp1 HRp2_p1).
        assert (Heq_p1p2 : p1 = p2)
          by exact (HL'_lift_antisym p1 p2 HLLp HLLp2p1).
        rewrite <- Heq_p1p2 in Hsuf.
        assert (HRab' : R a b).
        { destruct Hpref as [HRap1 | Heqap1];
          destruct Hsuf as [HRp1b | Heqp1b].
          - eapply poset_trans; eauto.
          - rewrite <- Heqp1b. exact HRap1.
          - rewrite Heqap1. exact HRp1b.
          - rewrite Heqap1. rewrite Heqp1b. apply poset_refl. }
        eapply poset_antisym; eauto.
      + (* J2, J2 *)
        destruct HJ2ab as [p1 [p2 [Hp1 [Hp2 [HprefA [HLLp HsufA]]]]]].
        destruct HJ2ba as [q1 [q2 [Hq1 [Hq2 [HprefB [HLLq HsufB]]]]]].
        (* Cycle: a → p1 → p2 → b → q1 → q2 → a.
           Derive R p2 q1 (via R_or_eq p2 b, R_or_eq b q1).
           Then L'_lift p1 q2 (compress).
           Derive R q2 p1 (via R_or_eq q2 a, R_or_eq a p1).
           Then L'_lift q1 p2 (compress).
           Then L'_lift p1 q2 and L'_lift q2 p1 → p1 = q2.
           And L'_lift q1 p2 and L'_lift p2 q1 → p2 = q1. (Actually we need
           L'_lift in opposing direction for antisym; let me redo.) *)
        assert (Hp2_R_q1 : R p2 q1 \/ p2 = q1).
        { destruct HsufA as [HRp2b | Heqp2b];
          destruct HprefB as [HRbq1 | Heqbq1].
          - left. eapply poset_trans; eauto.
          - left. rewrite <- Heqbq1. exact HRp2b.
          - left. rewrite Heqp2b. exact HRbq1.
          - right. rewrite Heqp2b. exact Heqbq1. }
        assert (Hq2_R_p1 : R q2 p1 \/ q2 = p1).
        { destruct HsufB as [HRq2a | Heqq2a];
          destruct HprefA as [HRap1 | Heqap1].
          - left. eapply poset_trans; eauto.
          - left. rewrite <- Heqap1. exact HRq2a.
          - left. rewrite Heqq2a. exact HRap1.
          - right. rewrite Heqq2a. exact Heqap1. }
        (* L'_lift p1 q2: via p1 → p2 → q1 → q2.
           L'_lift q1 p2: via q1 → q2 → p1 → p2. Wait, that uses opposite.
           Actually we have L'_lift p1 p2, R_or_eq p2 q1, L'_lift q1 q2 → L'_lift p1 q2.
           And L'_lift q1 q2, R_or_eq q2 p1, L'_lift p1 p2 → L'_lift q1 p2. *)
        assert (HLLp1q2 : L'_lift p1 q2).
        { assert (Hpq1 : L'_lift p1 q1)
            by apply (HInv_compress' p1 p2 q1 Hp1 Hp2 Hq1 HLLp Hp2_R_q1).
          eapply HL'_lift_trans; eauto. }
        assert (HLLq1p2 : L'_lift q1 p2).
        { assert (Hqp1 : L'_lift q1 p1)
            by apply (HInv_compress' q1 q2 p1 Hq1 Hq2 Hp1 HLLq Hq2_R_p1).
          eapply HL'_lift_trans; eauto. }
        (* Now L'_lift p1 q2, L'_lift q1 p2.  L'_lift p1 p2 (HLLp), L'_lift q1 q2 (HLLq). *)
        (* L'_lift p1 q2 and L'_lift q2 ? p1: we need L'_lift q2 p1. We have R_or_eq q2 p1.
           If R q2 p1: L'_lift q2 p1. If q2 = p1: trivial.
           Either way L'_lift_or_eq q2 p1. Then if L'_lift q2 p1: p1 = q2. *)
        assert (Hq2_eq_p1 : q2 = p1).
        { destruct Hq2_R_p1 as [HRq2p1 | Heq].
          - assert (HLLq2p1 : L'_lift q2 p1) by exact (HL'_lift_R q2 p1 Hq2 Hp1 HRq2p1).
            symmetry. exact (HL'_lift_antisym p1 q2 HLLp1q2 HLLq2p1).
          - exact Heq. }
        assert (Hp2_eq_q1 : p2 = q1).
        { destruct Hp2_R_q1 as [HRp2q1 | Heq].
          - assert (HLLp2q1 : L'_lift p2 q1) by exact (HL'_lift_R p2 q1 Hp2 Hq1 HRp2q1).
            exact (HL'_lift_antisym p2 q1 HLLp2q1 HLLq1p2).
          - exact Heq. }
        (* Now everything collapses. Path: a → p1 → p2 → b → p2 → p1 → a (using q1 = p2, q2 = p1).
           HprefA: R_or_eq a p1. HsufB: R_or_eq q2 a = R_or_eq p1 a.
           So R_or_eq a p1 /\ R_or_eq p1 a → a = p1.
           HsufA: R_or_eq p2 b. HprefB: R_or_eq b q1 = R_or_eq b p2.
           So R_or_eq p2 b /\ R_or_eq b p2 → b = p2.
           Then path a = p1, b = p2. L'_lift p1 p2 = L'_lift a b.
           L'_lift q1 q2 = L'_lift p2 p1 = L'_lift b a.
           Antisym L'_lift → a = b. *)
        (* Hq2_eq_p1 : q2 = p1. Hp2_eq_q1 : p2 = q1.
           HprefA: R a p1 \/ a = p1.
           HsufB:  R q2 a \/ q2 = a, i.e. (using q2 = p1) R p1 a \/ p1 = a.
           HsufA:  R p2 b \/ p2 = b.
           HprefB: R b q1 \/ b = q1, i.e. (using p2 = q1) R b p2 \/ b = p2. *)
        assert (Heq_ap1 : a = p1).
        { destruct HprefA as [HRap1 | Heqap1].
          - destruct HsufB as [HRq2a | Heqq2a].
            + (* R q2 a, q2 = p1 → R p1 a, antisym with R a p1 → a = p1 *)
              rewrite Hq2_eq_p1 in HRq2a. eapply poset_antisym; eauto.
            + rewrite Hq2_eq_p1 in Heqq2a. symmetry. exact Heqq2a.
          - exact Heqap1. }
        assert (Heq_bp2 : b = p2).
        { destruct HsufA as [HRp2b | Heqp2b].
          - destruct HprefB as [HRbq1 | Heqbq1].
            + rewrite <- Hp2_eq_q1 in HRbq1. symmetry. eapply poset_antisym; eauto.
            + rewrite <- Hp2_eq_q1 in Heqbq1. exact Heqbq1.
          - symmetry. exact Heqp2b. }
        subst a b.
        (* HLLp : L'_lift p1 p2; HLLq : L'_lift q1 q2.
           Hp2_eq_q1 : p2 = q1, so q1 = p2; Hq2_eq_p1 : q2 = p1.
           Rewriting HLLq: L'_lift q1 q2 → L'_lift p2 p1. *)
        rewrite Hq2_eq_p1 in HLLq.
        rewrite <- Hp2_eq_q1 in HLLq.
        exact (HL'_lift_antisym p1 p2 HLLp HLLq).
      + (* J2, J3 *)
        destruct HJ2ab as [p1 [p2 [Hp1 [Hp2 [HprefA [HLLp HsufA]]]]]].
        (* R a x' but here J2 is for (a, b) and J3 is for (b, a): R b x' /\ R y' a *)
        (* J2(a,b): a → p1 → p2 → b. J3(b,a): R b x' /\ R y' a. *)
        (* Strategy: From HsufA: R_or_eq p2 b. R b x' → R p2 x'.  p2 ∈ S' so
           p2 ≠ x'. critical_down → R p2 y'.  R y' a (from J3) and R_or_eq a p1.
           → R p2 a, then R p2 p1 (or p2 = p1 case). L'_lift p2 p1 → antisym → p1 = p2.
           Reduce path. Show a = b or contradiction. *)
        assert (HRp2x : R p2 x').
        { destruct HsufA as [HRp2b | Heqp2b].
          - eapply poset_trans; eauto.
          - rewrite Heqp2b. exact HRbx. }
        assert (Hp2_nex : p2 <> x').
        { intro Heq. rewrite Heq in Hp2. apply (Hx'_notin Hp2). }
        assert (HRp2y : R p2 y').
        { apply (critical_down Hcp). split; [exact HRp2x | exact Hp2_nex]. }
        assert (HRp2a : R p2 a).
        { eapply poset_trans; eauto. }
        assert (HRp2p1 : R p2 p1 \/ p2 = p1).
        { destruct HprefA as [HRap1 | Heqap1].
          - left. eapply poset_trans; eauto.
          - left. rewrite <- Heqap1. exact HRp2a. }
        (* Now: L'_lift p1 p2 and R_or_eq p2 p1.
           If R p2 p1: L'_lift p2 p1, antisym → p1 = p2.
           If p2 = p1: trivial p1 = p2. *)
        assert (Heq_p1p2 : p1 = p2).
        { destruct HRp2p1 as [HRp2p1 | Heq].
          - assert (HLLp2p1 : L'_lift p2 p1) by exact (HL'_lift_R p2 p1 Hp2 Hp1 HRp2p1).
            exact (HL'_lift_antisym p1 p2 HLLp HLLp2p1).
          - symmetry. exact Heq. }
        (* p1 = p2. So we have R y' a, R a p1 (or a = p1), and R p2 b (or p2 = b),
           with p1 = p2.  R y' a, R a p1 → R y' p1 (or R y' p1 = R y' a if a = p1).
           So R y' p1 in either case. Then R y' p1, p1 ∈ S' so p1 ≠ y'.
           Strict R y' p1 → R x' p1 (critical_up). So R x' p1.
           And R x' p1 → ... hmm what's the goal? We want a = b. *)
        rewrite <- Heq_p1p2 in *.
        (* Now p1 = p2. HLLp : L'_lift p1 p1 (refl). *)
        (* Goal: derive a = b.
           HprefA: R a p1 \/ a = p1.  HsufA: R p1 b \/ p1 = b.
           HRyp1: R y' a, R_or_eq a p1 → R y' p1 (if R a p1) or R y' p1 = R y' a (if a = p1).
           So R y' p1.
           HRxp1: critical_up (R y' p1 strict).  p1 ∈ S', p1 ≠ y'. So R x' p1.
           HRbx: R b x'. R x' p1 → R b p1.
           HsufA gives R_or_eq p1 b. So R b p1 and R_or_eq p1 b → p1 = b (antisym) or p1 = b.
           So b = p1 in either case.
           Then p1 = b. HprefA: R a p1 = R a b, or a = p1 = b. So either way, a = b would
           come from R y' a, R a b, R b x' → R y' x' contradiction!
           Wait if we have R a b (from R a p1 with p1 = b), then R y' a, R a b → R y' b,
           and R b x' → R y' x', contradiction!
           If a = p1, then a = p1 = b, so a = b. ✓ *)
        assert (HRyp1 : R y' p1).
        { destruct HprefA as [HRap1 | Heqap1].
          - eapply poset_trans; eauto.
          - rewrite <- Heqap1. exact HRya. }
        assert (Hp1_ney : p1 <> y').
        { intro Heq. rewrite Heq in Hp1. apply (Hy'_notin Hp1). }
        assert (HRxp1 : R x' p1).
        { apply (critical_up Hcp). split; [exact HRyp1 | auto]. }
        assert (HRbp1 : R b p1).
        { eapply poset_trans; eauto. }
        assert (Heq_p1b : p1 = b).
        { destruct HsufA as [HRp1b | Heqp1b].
          - eapply poset_antisym; eauto.
          - exact Heqp1b. }
        (* p1 = b. *)
        destruct HprefA as [HRap1 | Heqap1].
        * (* R a p1 = R a b *)
          exfalso. apply Hnyx.
          assert (HRab : R a b) by (rewrite <- Heq_p1b; exact HRap1).
          eapply poset_trans; [exact HRya | eapply poset_trans; eauto].
        * (* a = p1 = b *)
          rewrite Heqap1. exact Heq_p1b.
      + (* J3, J1: R a x' /\ R y' b, R b a → R y' x' contradiction *)
        exfalso. apply Hnyx.
        eapply poset_trans; [exact HRyb | eapply poset_trans; eauto].
      + (* J3, J2: R a x' /\ R y' b, J2(b, a) *)
        destruct HJ2ba as [q1 [q2 [Hq1 [Hq2 [HprefB [HLLq HsufB]]]]]].
        (* J2(b, a): b → q1 → q2 → a. J3(a, b): R a x' /\ R y' b. *)
        (* From HprefB: R_or_eq b q1. R y' b → R y' q1.
           q1 ∈ S', q1 ≠ y'. critical_up → R x' q1.
           HsufB: R_or_eq q2 a. R a x' → R q2 x'.
           q2 ∈ S', q2 ≠ x'. critical_down → R q2 y'.
           So R x' q1, L'_lift q1 q2, R q2 y'. Hmm.

           Symmetrically: R a x' (J3), R_or_eq a p1 -- wait no, we don't have J2(a,b) here.

           Approach: We have L'_lift q1 q2. R q2 y' (above derivation).
           Also R y' q1 (above). So R q2 y' /\ R y' q1 → R q2 q1.
           Then L'_lift q2 q1, antisym → q1 = q2.
           Then path: b → q1 → q1 → a, i.e., R_or_eq b q1, R_or_eq q1 a.
           So R_or_eq b a → R b a or b = a.
           Combined with R a x' /\ R y' b (J3): R y' b /\ R b a /\ R a x' → R y' x'. False.
           If b = a, done. *)
        assert (HRyq1 : R y' q1).
        { destruct HprefB as [HRbq1 | Heqbq1].
          - eapply poset_trans; eauto.
          - rewrite <- Heqbq1. exact HRyb. }
        assert (Hq1_ney : q1 <> y').
        { intro Heq. rewrite Heq in Hq1. apply (Hy'_notin Hq1). }
        assert (HRxq1 : R x' q1).
        { apply (critical_up Hcp). split; [exact HRyq1 | auto]. }
        assert (HRq2x : R q2 x').
        { destruct HsufB as [HRq2a | Heqq2a].
          - eapply poset_trans; eauto.
          - rewrite Heqq2a. exact HRax. }
        assert (Hq2_nex : q2 <> x').
        { intro Heq. rewrite Heq in Hq2. apply (Hx'_notin Hq2). }
        assert (HRq2y : R q2 y').
        { apply (critical_down Hcp). split; [exact HRq2x | auto]. }
        assert (HRq2q1 : R q2 q1).
        { eapply poset_trans; eauto. }
        assert (HLLq2q1 : L'_lift q2 q1)
          by exact (HL'_lift_R q2 q1 Hq2 Hq1 HRq2q1).
        assert (Heq_q1q2 : q1 = q2)
          by exact (HL'_lift_antisym q1 q2 HLLq HLLq2q1).
        rewrite <- Heq_q1q2 in HsufB.
        (* HsufB : R q1 a \/ q1 = a *)
        destruct HprefB as [HRbq1 | Heqbq1];
        destruct HsufB as [HRq1a | Heqq1a].
        * exfalso. apply Hnyx.
          assert (HRba : R b a) by (eapply poset_trans; eauto).
          eapply poset_trans; [exact HRyb | eapply poset_trans; eauto].
        * exfalso. apply Hnyx.
          assert (HRba : R b a) by (rewrite <- Heqq1a; exact HRbq1).
          eapply poset_trans; [exact HRyb | eapply poset_trans; eauto].
        * exfalso. apply Hnyx.
          assert (HRba : R b a) by (rewrite Heqbq1; exact HRq1a).
          eapply poset_trans; [exact HRyb | eapply poset_trans; eauto].
        * rewrite Heqbq1. symmetry. exact Heqq1a.
      + (* J3, J3: R a x' /\ R y' b, R b x' /\ R y' a → R y' x' contradiction *)
        exfalso. apply Hnyx.
        eapply poset_trans; [exact HRya | exact HRax].
    - (* Transitivity *)
      intros a b c Hab Hbc. eapply t_trans; eauto.
  Qed.

  (** Boundary-augmented variant of [lift_and_force_is_poset].

      Takes an extra list [B : list (A * A)] of *boundary reversal*
      edges (each pair [(u, v) ∈ B] becomes an edge [v → u] in the
      augmented relation). Unlike [lift_and_force_is_poset], which
      proves the path invariant directly using critical-pair structure,
      this version takes acyclicity as a hypothesis. The hard
      combinatorial work shifts to the caller (who must establish
      acyclicity for their particular choice of [B]).

      Acyclicity hypothesis form: for all [a ≠ b], it is not the case
      that the TC-augmented relation contains both [a →+ b] and
      [b →+ a]. (Stating it as "no [a →+ a]" would be too strong since
      [step a a] already holds via [R]-reflexivity.) *)
  Lemma lift_and_force_with_boundary_is_poset :
    forall (x' y' : A) (S' : Ensemble A) (B : list (A * A))
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension
      (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
    (forall a b, a <> b ->
       clos_trans A
         (fun a b =>
            R a b
            \/ (exists (ha : In A S' a) (hb : In A S' b),
                  L' (exist _ a ha) (exist _ b hb))
            \/ (a = x' /\ b = y')
            \/ List.In (b, a) B) a b ->
       clos_trans A
         (fun a b =>
            R a b
            \/ (exists (ha : In A S' a) (hb : In A S' b),
                  L' (exist _ a ha) (exist _ b hb))
            \/ (a = x' /\ b = y')
            \/ List.In (b, a) B) b a ->
       False) ->
    IsPoset A
      (clos_trans A
         (fun a b =>
            R a b
            \/ (exists (ha : In A S' a) (hb : In A S' b),
                  L' (exist _ a ha) (exist _ b hb))
            \/ (a = x' /\ b = y')
            \/ List.In (b, a) B)).
  Proof.
    intros x' y' S' B L' Hcp HS'_eq HL' Hacyclic.
    set (step := fun a b =>
                   R a b
                \/ (exists (ha : In A S' a) (hb : In A S' b),
                      L' (exist _ a ha) (exist _ b hb))
                \/ (a = x' /\ b = y')
                \/ List.In (b, a) B).
    fold step.
    change (IsPoset A (clos_trans A step)).
    constructor.
    - (* Reflexivity: R is reflexive, lift via t_step *)
      intro a. apply t_step. left. apply poset_refl.
    - (* Antisymmetry: from Hacyclic by case analysis on a = b *)
      intros a b Hab Hba.
      destruct (classic (a = b)) as [Heq | Hneq]; [exact Heq |].
      exfalso. exact (Hacyclic a b Hneq Hab Hba).
    - (* Transitivity: clos_trans is transitive *)
      intros a b c Hab Hbc. eapply t_trans; eauto.
  Qed.

  (** Helper: a total order extending a poset is a linear extension of
      any sub-relation. *)
  Lemma total_order_is_linear_extension :
    forall (R' L : A -> A -> Prop),
    IsPoset A L ->
    (forall x y, L x y \/ L y x) ->
    (forall x y, R' x y -> L x y) ->
    IsLinearExtension R' L.
  Proof.
    intros R' L Hp Htot Hext.
    constructor.
    - constructor; [exact Hp | exact Htot].
    - exact Hext.
  Qed.

  (** Helper: build [L_extra] reversing the critical pair (x',y').
      Returns a linear extension L of R with [L y' x']. *)
  Lemma critical_pair_reversing_extension :
    forall (x' y' : A),
    IsCriticalPair R x' y' ->
    exists L : A -> A -> Prop,
      IsLinearExtension R L /\ L y' x'.
  Proof.
    intros x' y' Hcp.
    assert (Hinc : Incomparable R x' y') by exact (critical_incomparable Hcp).
    (* TC(R u {(y',x')}) is a poset *)
    set (ext := fun a b => R a b \/ (a = y' /\ b = x')).
    set (R1 := @clos_trans A ext).
    assert (HR1_pos : IsPoset A R1).
    { unfold R1, ext.
      exact (add_incomparable_general A R x' y' Hinc). }
    destruct (szpilrajn_theorem A R1) as [L [HL_pos [HL_tot HL_ext]]].
    exists L. split.
    - apply (total_order_is_linear_extension R L HL_pos HL_tot).
      intros a b Hab. apply HL_ext. apply t_step. left. exact Hab.
    - apply HL_ext. apply t_step. right. split; reflexivity.
  Qed.

  (** Sub-lemma A: For every L' linearizing R restricted to S', there
      exists a total order L'_full on A which (i) is a linear extension
      of R, (ii) satisfies L'_full x' y', and (iii) agrees with L' on
      pairs in S' x S'.  Built via [lift_and_force_is_poset] +
      [szpilrajn_theorem]. *)
  Lemma cp_lift_witness :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension
      (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
    exists L'_full : A -> A -> Prop,
      IsLinearExtension R L'_full /\
      L'_full x' y' /\
      (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
         L' (exist _ a ha) (exist _ b hb) -> L'_full a b).
  Proof.
    intros x' y' S' L' Hcp HS'_eq HL'.
    set (P := clos_trans A
                (fun a b =>
                   R a b
                   \/ (exists (ha : In A S' a) (hb : In A S' b),
                         L' (exist _ a ha) (exist _ b hb))
                   \/ (a = x' /\ b = y'))).
    assert (HP_poset : IsPoset A P)
      by exact (lift_and_force_is_poset x' y' S' L' Hcp HS'_eq HL').
    destruct (szpilrajn_theorem A P) as [L'_full [HL_pos [HL_tot HL_ext]]].
    exists L'_full. split; [| split].
    - apply (total_order_is_linear_extension R L'_full HL_pos HL_tot).
      intros a b HRab. apply HL_ext. apply t_step. left. exact HRab.
    - apply HL_ext. apply t_step. right. right. split; reflexivity.
    - intros a b ha hb HL'ab.
      apply HL_ext. apply t_step. right. left.
      exists ha, hb. exact HL'ab.
  Qed.

  (** Sub-lemma B (Admitted): the witness function from [cp_lift_witness]
      can be chosen so that distinct L' produce distinct L'_full.
      Strategy: any [L'_full] from the construction restricts to L' on
      S' x S' (totality of L' gives the converse direction), so the map
      is left-cancellative. We package this as an injective witness map
      using [constructive_indefinite_description]. *)
  Lemma cp_lift_function :
    forall (x' y' : A) (S' : Ensemble A),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    exists lift : ({a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
                  -> (A -> A -> Prop),
      forall L',
        IsLinearExtension
          (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
        IsLinearExtension R (lift L') /\
        (lift L') x' y' /\
        (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
           L' (exist _ a ha) (exist _ b hb) -> (lift L') a b) /\
        (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
           (lift L') a b -> L' (exist _ a ha) (exist _ b hb)).
  Proof.
    intros x' y' S' Hcp HS'_eq.
    (* Pick a witness function via classical description. *)
    set (Q := fun (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
                  (L_out : A -> A -> Prop) =>
                IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
                IsLinearExtension R L_out /\
                L_out x' y' /\
                (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
                   L' (exist _ a ha) (exist _ b hb) -> L_out a b) /\
                (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
                   L_out a b -> L' (exist _ a ha) (exist _ b hb))).
    assert (Hex : forall L', exists L_out, Q L' L_out).
    { intros L'. unfold Q.
      destruct (classic (IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L'))
        as [HL' | HnL'].
      - destruct (cp_lift_witness x' y' S' L' Hcp HS'_eq HL')
          as [L_full [Hlin [Hxy Hext]]].
        exists L_full. intros _.
        split; [exact Hlin | split; [exact Hxy | split; [exact Hext |]]].
        (* Reverse direction: L_full a b → L' (exist a ha) (exist b hb).
           Uses totality of L' + antisymmetry of L_full (as a total order). *)
        intros a b ha hb HLfab.
        destruct (HL'.(linear_is_total).(total_comparable)
                    (exist _ a ha) (exist _ b hb)) as [HLab | HLba].
        + exact HLab.
        + (* L'(b,a) lifts to L_full(b,a); antisym with L_full(a,b) gives
             exist a ha = exist b hb. *)
          assert (HLf_ba : L_full b a) by exact (Hext b a hb ha HLba).
          pose proof Hlin.(linear_is_total).(total_is_poset) as HLposet.
          assert (Hab_eq : a = b)
            by exact (HLposet.(poset_antisym) a b HLfab HLf_ba).
          (* Replace b with a; then exist _ a ha = exist _ b hb so L'(.,.) follows from refl *)
          subst b.
          assert (Hhh : ha = hb) by apply proof_irrelevance. subst hb.
          exact (HL'.(linear_is_total).(total_is_poset).(poset_refl) (exist _ a ha)).
      - exists (fun _ _ => True). intro Hk. exfalso; apply HnL'; exact Hk. }
    set (lift := fun L' =>
                   proj1_sig (constructive_indefinite_description
                                _ (Hex L'))).
    exists lift. intros L' HL'.
    pose proof (proj2_sig (constructive_indefinite_description _ (Hex L'))) as Hspec.
    apply Hspec. exact HL'.
  Qed.

  (** Sub-lemma B': boundary-aware variant of [cp_lift_function].

      Given a list [B : list (A * A)] of boundary edges, produce a
      function [lift_b] mapping each L' linearizing R on S' to a total
      order on A that (i) extends R, (ii) forces x' < y', (iii) reverses
      every (p,q) ∈ B (i.e. lift_b L' q p), and (iv) matches L' on S'×S'.

      The acyclicity hypothesis is required from the caller per L' — it
      is the only structural property of B used in the construction.
      Caller is responsible for verifying acyclicity (which in practice
      follows from [IsBoundaryReversalSet] plus the local realizer
      properties). *)
  Lemma cp_lift_function_with_boundary :
    forall (x' y' : A) (S' : Ensemble A) (B : list (A * A)),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    exists lift_b : ({a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
                    -> (A -> A -> Prop),
      forall L',
        IsLinearExtension
          (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
        (forall a b, a <> b ->
         clos_trans A
           (fun a b => R a b
                    \/ (exists (ha : In A S' a) (hb : In A S' b),
                          L' (exist _ a ha) (exist _ b hb))
                    \/ (a = x' /\ b = y')
                    \/ List.In (b, a) B) a b ->
         clos_trans A
           (fun a b => R a b
                    \/ (exists (ha : In A S' a) (hb : In A S' b),
                          L' (exist _ a ha) (exist _ b hb))
                    \/ (a = x' /\ b = y')
                    \/ List.In (b, a) B) b a ->
         False) ->
        IsLinearExtension R (lift_b L') /\
        (lift_b L') x' y' /\
        (forall p q : A, List.In (p, q) B -> (lift_b L') q p) /\
        (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
           L' (exist _ a ha) (exist _ b hb) -> (lift_b L') a b) /\
        (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
           (lift_b L') a b -> L' (exist _ a ha) (exist _ b hb)).
  Proof.
    intros x' y' S' B Hcp HS'_eq.
    (* Define the per-L' specification predicate Q. *)
    set (Q := fun (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
                  (L_out : A -> A -> Prop) =>
                IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
                (forall a b, a <> b ->
                 clos_trans A
                   (fun a b => R a b
                            \/ (exists (ha : In A S' a) (hb : In A S' b),
                                  L' (exist _ a ha) (exist _ b hb))
                            \/ (a = x' /\ b = y')
                            \/ List.In (b, a) B) a b ->
                 clos_trans A
                   (fun a b => R a b
                            \/ (exists (ha : In A S' a) (hb : In A S' b),
                                  L' (exist _ a ha) (exist _ b hb))
                            \/ (a = x' /\ b = y')
                            \/ List.In (b, a) B) b a ->
                 False) ->
                IsLinearExtension R L_out /\
                L_out x' y' /\
                (forall p q : A, List.In (p, q) B -> L_out q p) /\
                (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
                   L' (exist _ a ha) (exist _ b hb) -> L_out a b) /\
                (forall (a b : A) (ha : In A S' a) (hb : In A S' b),
                   L_out a b -> L' (exist _ a ha) (exist _ b hb))).
    assert (Hex : forall L', exists L_out, Q L' L_out).
    { intros L'. unfold Q.
      (* Case split on whether both preconditions hold. *)
      destruct (classic (IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L'))
        as [HL' | HnL']; [| (* trivial witness when L' is not a linear extension *)
        exists (fun _ _ => True); intros Hk; exfalso; apply HnL'; exact Hk ].
      destruct (classic
                  (forall a b, a <> b ->
                   clos_trans A
                     (fun a b => R a b
                              \/ (exists (ha : In A S' a) (hb : In A S' b),
                                    L' (exist _ a ha) (exist _ b hb))
                              \/ (a = x' /\ b = y')
                              \/ List.In (b, a) B) a b ->
                   clos_trans A
                     (fun a b => R a b
                              \/ (exists (ha : In A S' a) (hb : In A S' b),
                                    L' (exist _ a ha) (exist _ b hb))
                              \/ (a = x' /\ b = y')
                              \/ List.In (b, a) B) b a ->
                   False)) as [Hacyc | Hnacyc]; [|
        exists (fun _ _ => True); intros _ Hk; exfalso; apply Hnacyc; exact Hk ].
      (* Build the augmented relation. *)
      set (Aug := fun a b : A =>
                    R a b
                    \/ (exists (ha : In A S' a) (hb : In A S' b),
                          L' (exist _ a ha) (exist _ b hb))
                    \/ (a = x' /\ b = y')
                    \/ List.In (b, a) B).
      set (AugTC := clos_trans A Aug).
      assert (HAug_poset : IsPoset A AugTC)
        by exact (lift_and_force_with_boundary_is_poset x' y' S' B L' Hcp HS'_eq HL' Hacyc).
      destruct (szpilrajn_theorem A AugTC) as [L_full [HL_pos [HL_tot HL_ext]]].
      exists L_full. intros _ _.
      (* Spec property (1): IsLinearExtension R L_full. *)
      assert (Hlin : IsLinearExtension R L_full).
      { apply (total_order_is_linear_extension R L_full HL_pos HL_tot).
        intros a b HRab. apply HL_ext. apply t_step. left. exact HRab. }
      (* Spec property (2): L_full x' y'. *)
      assert (Hxy : L_full x' y').
      { apply HL_ext. apply t_step. right. right. left. split; reflexivity. }
      (* Spec property (3): forall (p,q) ∈ B, L_full q p. *)
      assert (HB : forall p q : A, List.In (p, q) B -> L_full q p).
      { intros p q HpqB. apply HL_ext. apply t_step.
        right. right. right. exact HpqB. }
      (* Spec property (4): L'-forward. *)
      assert (HfwL' : forall (a b : A) (ha : In A S' a) (hb : In A S' b),
                       L' (exist _ a ha) (exist _ b hb) -> L_full a b).
      { intros a b ha hb HL'ab. apply HL_ext. apply t_step.
        right. left. exists ha, hb. exact HL'ab. }
      (* Spec property (5): L'-reverse — totality + antisymmetry. *)
      assert (HrvL' : forall (a b : A) (ha : In A S' a) (hb : In A S' b),
                       L_full a b -> L' (exist _ a ha) (exist _ b hb)).
      { intros a b ha hb HLfab.
        destruct (HL'.(linear_is_total).(total_comparable)
                    (exist _ a ha) (exist _ b hb)) as [HLab | HLba].
        + exact HLab.
        + assert (HLf_ba : L_full b a) by exact (HfwL' b a hb ha HLba).
          assert (Hab_eq : a = b)
            by exact (HL_pos.(poset_antisym) a b HLfab HLf_ba).
          subst b.
          assert (Hhh : ha = hb) by apply proof_irrelevance. subst hb.
          exact (HL'.(linear_is_total).(total_is_poset).(poset_refl)
                   (exist _ a ha)). }
      split; [exact Hlin |].
      split; [exact Hxy |].
      split; [exact HB |].
      split; [exact HfwL' | exact HrvL']. }
    set (lift_b := fun L' =>
                     proj1_sig (constructive_indefinite_description
                                  _ (Hex L'))).
    exists lift_b. intros L' HL' Hacyc.
    pose proof (proj2_sig (constructive_indefinite_description _ (Hex L')))
      as Hspec.
    apply Hspec; [exact HL' | exact Hacyc].
  Qed.

  (** Sub-lemma C: realizer separation for the lifted set.
      The strengthened hypothesis [Hcp_sep] expresses that for every
      critical pair (p', q') of R, some L in the realizer reverses it.
      With that in hand, [critical_pair_realizer_iff] (CriticalPairs.v)
      promotes the union to a realizer of R, so any (p,q) ordered by
      every L is forced to satisfy R p q. *)
  Lemma cp_realizer_separation :
    forall (x' y' : A) (S' : Ensemble A) (L_extra : A -> A -> Prop)
           (r_lifted : Ensemble (A -> A -> Prop)),
    Finite A (Full_set A) ->
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension R L_extra ->
    L_extra y' x' ->
    (forall L, In _ r_lifted L -> IsLinearExtension R L /\ L x' y') ->
    (forall p' q' : A, IsCriticalPair R p' q' ->
       exists L, In _ (Add (A -> A -> Prop) r_lifted L_extra) L /\ L q' p') ->
    forall p q : A,
      (forall L, In _ (Add (A -> A -> Prop) r_lifted L_extra) L -> L p q) ->
      R p q.
  Proof.
    intros x' y' S' L_extra r_lifted HfinA Hcp HS'_eq HL_extra_lin
           HL_extra_yx Hr_lifted_spec Hcp_sep p q Hall.
    set (realizer := Add (A -> A -> Prop) r_lifted L_extra).
    assert (Hinh : Ensembles.Inhabited (A -> A -> Prop) realizer).
    { exists L_extra. right. constructor. }
    assert (Hlin : forall L, In _ realizer L -> IsLinearExtension R L).
    { intros L HL. destruct HL as [L HL | L HL].
      - exact (proj1 (Hr_lifted_spec L HL)).
      - destruct HL. exact HL_extra_lin. }
    pose proof (@critical_pair_realizer_iff A R _ HfinA realizer Hinh Hlin) as Hiff.
    assert (Hreal : IsRealizer R realizer) by (apply Hiff; exact Hcp_sep).
    exact (proj2 (Hreal.(realizer_intersection) p q) Hall).
  Qed.

  (** Core helper: produce the d'-element set [r_lifted] of linear
      extensions of R, each forcing [x' < y'], whose union with
      [L_extra] realizes R. *)
  Lemma extend_through_cp_construction :
    forall (x' y' : A) (S' : Ensemble A) (d' : nat) (L_extra : A -> A -> Prop),
    Finite A (Full_set A) ->
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension R L_extra ->
    L_extra y' x' ->
    (* NEW HYPOTHESIS: no boundary critical pairs.  Every critical pair of R
       either IS (x', y') or has both endpoints in S'.  This eliminates the
       structurally hard boundary case in [Hcp_sep] below. *)
    (forall p q : A, IsCriticalPair R p q ->
       (p = x' /\ q = y') \/ (In A S' p /\ In A S' q)) ->
    (exists (r' : Ensemble ({a : A | In A S' a} -> {a : A | In A S' a} -> Prop)),
       IsRealizer (fun (a b : {a : A | In A S' a}) => R (proj1_sig a) (proj1_sig b)) r' /\
       cardinal _ r' d') ->
    exists r_lifted : Ensemble (A -> A -> Prop),
      (forall L, In _ r_lifted L -> IsLinearExtension R L /\ L x' y') /\
      cardinal (A -> A -> Prop) r_lifted d' /\
      ~ In _ r_lifted L_extra /\
      IsRealizer R (Add (A -> A -> Prop) r_lifted L_extra).
  Proof.
    intros x' y' S' d' L_extra HfinA Hcp HS'_eq HL_extra_lin HL_extra_yx
           Hno_boundary Hr'_ex.
    destruct Hr'_ex as [r' [Hr'_real Hr'_card]].
    pose proof (critical_incomparable Hcp) as Hcp_inc.
    pose proof (critical_down (R:=R) (x:=x') (y:=y') Hcp) as Hcp_dn.
    pose proof (critical_up (R:=R) (x:=x') (y:=y') Hcp) as Hcp_up.
    assert (Hnxy : ~ R x' y') by (intro HR; apply Hcp_inc; left; exact HR).
    assert (Hnyx : ~ R y' x') by (intro HR; apply Hcp_inc; right; exact HR).
    assert (Hx'_neq_y' : x' <> y').
    { intro Heq. apply Hcp_inc. left. rewrite Heq. apply poset_refl. }
    assert (Hx'_notin_S' : ~ In A S' x').
    { intro Hin. rewrite HS'_eq in Hin. destruct Hin as [[_ Hnx] _].
      apply Hnx. constructor. }
    assert (Hy'_notin_S' : ~ In A S' y').
    { intro Hin. rewrite HS'_eq in Hin. destruct Hin as [_ Hny].
      apply Hny. constructor. }
    (* Boundary CP reversal lemma: given a boundary critical pair (p',q') of R
       (one of p',q' in {x',y'}, the other in S', and (p',q') ≠ (x',y')),
       there exists a linear extension L_b of R with both L_b x' y' AND
       L_b q' p'.

       Construction:
         (1) Build M1 = TC(R ∪ {(q',p')}) and verify it is a poset via
             [add_incomparable_general] (using ~R p' q' ∧ ~R q' p' from the
             CP incomparability).
         (2) Show M1 y' x' is FALSE by case analysis on the four boundary
             configurations.  In each case we derive a contradiction:
             (a) p'=x',q'∈S': R y' q' Strict → R x' q' (Hcp_up), but (x',q')
                 CP forbids R x' q'.
             (b) p'=y',q'∈S': R p' x' = R y' x' is false (Hnyx).
             (c) p'∈S',q'=x': R y' q' = R y' x' is false (Hnyx).
             (d) p'∈S',q'=y': R p' x' Strict (p'≠x') → R p' y' (Hcp_dn),
                 but (p',y') CP forbids R p' y'.
         (3) Decide classically whether M1 x' y' is already true:
              - If yes, Szpilrajn-extend M1 directly to get L_b.
              - If no, add (x',y') to M1 via [add_incomparable_general]
                using the M1-incomparability from step (2), then
                Szpilrajn-extend the result. *)
    assert (Hboundary_extension :
      forall p' q' : A,
        IsCriticalPair R p' q' ->
        ((p' = x' /\ In A S' q') \/ (p' = y' /\ In A S' q') \/
         (In A S' p' /\ q' = x') \/ (In A S' p' /\ q' = y')) ->
        exists L_b : A -> A -> Prop,
          IsLinearExtension R L_b /\ L_b x' y' /\ L_b q' p').
    { intros p' q' Hcp' Hbnd.
      assert (HnRp'q' : ~ R p' q')
        by (intro HR; apply (critical_incomparable Hcp'); left; exact HR).
      assert (HnRq'p' : ~ R q' p')
        by (intro HR; apply (critical_incomparable Hcp'); right; exact HR).
      assert (Hp'_neq_q' : p' <> q').
      { intro Heq. apply (critical_incomparable Hcp').
        left. rewrite Heq. apply poset_refl. }
      assert (HincR : ~ (R p' q' \/ R q' p')) by tauto.
      pose (M1 := clos_trans A (fun a b => R a b \/ (a = q' /\ b = p'))).
      assert (HM1_pos : IsPoset A M1)
        by exact (add_incomparable_general A R p' q' HincR).
      assert (Hinv1 : forall a b, M1 a b -> R a b \/ (R a q' /\ R p' b)).
      { intros a b. apply (add_incomparable_path_invariant A R p' q' HincR). }
      assert (Hinv1_step : forall a b, R a b -> M1 a b) by
        (intros a b HR; apply t_step; left; exact HR).
      assert (Hinv1_pref : M1 q' p') by (apply t_step; right; split; reflexivity).
      (* Verify M1 y' x' is FALSE in all four boundary cases. *)
      assert (HnM1_yx : ~ M1 y' x').
      { intro HM1yx. destruct (Hinv1 _ _ HM1yx) as [HR1 | [HRyq HRpx]].
        - exact (Hnyx HR1).
        - destruct Hbnd as [[Hpx Hq_in] | [[Hpy Hq_in] | [[Hp_in Hqx] | [Hp_in Hqy]]]].
          + subst p'.
            assert (Hyne_q : y' <> q').
            { intro Heq. subst y'. exact (Hy'_notin_S' Hq_in). }
            assert (Hxq : R x' q') by exact (Hcp_up q' (conj HRyq Hyne_q)).
            apply (critical_incomparable Hcp'). left. exact Hxq.
          + subst p'. exact (Hnyx HRpx).
          + subst q'. exact (Hnyx HRyq).
          + subst q'.
            assert (Hpne_x : p' <> x').
            { intro Heq. subst p'. exact (Hx'_notin_S' Hp_in). }
            assert (Hpy : R p' y') by exact (Hcp_dn p' (conj HRpx Hpne_x)).
            exact (HnRp'q' Hpy). }
      destruct (classic (M1 x' y')) as [HM1xy | HnM1xy].
      - destruct (szpilrajn_theorem A M1) as [L_b [HLb_pos [HLb_tot HLb_ext]]].
        exists L_b. split; [| split].
        + apply (total_order_is_linear_extension R L_b HLb_pos HLb_tot).
          intros a b HRab. apply HLb_ext. exact (Hinv1_step a b HRab).
        + apply HLb_ext. exact HM1xy.
        + apply HLb_ext. exact Hinv1_pref.
      - assert (HincM1_yx : ~ (M1 y' x' \/ M1 x' y')) by tauto.
        pose (M2 := clos_trans A (fun a b => M1 a b \/ (a = x' /\ b = y'))).
        assert (HM2_pos : IsPoset A M2)
          by exact (@add_incomparable_general A M1 HM1_pos y' x' HincM1_yx).
        destruct (szpilrajn_theorem A M2) as [L_b [HLb_pos [HLb_tot HLb_ext]]].
        exists L_b. split; [| split].
        + apply (total_order_is_linear_extension R L_b HLb_pos HLb_tot).
          intros a b HRab. apply HLb_ext. apply t_step. left.
          exact (Hinv1_step a b HRab).
        + apply HLb_ext. apply t_step. right. split; reflexivity.
        + apply HLb_ext. apply t_step. left. exact Hinv1_pref. }
    (* Step 1: obtain the lift function via Sub-lemma B. *)
    destruct (cp_lift_function x' y' S' Hcp HS'_eq) as [lift Hlift_spec].
    (* Step 2: define r_lifted := Im r' lift. *)
    set (r_lifted := Im _ _ r' lift).
    exists r_lifted.
    (* Establish: every L in r_lifted comes from some L' in r' that linearizes R|_S'. *)
    assert (Hlift_each : forall L, In _ r_lifted L ->
              exists L', In _ r' L' /\ lift L' = L /\
                IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L').
    { intros L HL. destruct HL as [L' HL'_in y0 HLeq].
      exists L'. split; [exact HL'_in | split; [symmetry; exact HLeq |]].
      exact (Hr'_real.(realizer_linear) L' HL'_in). }
    split; [| split; [| split]].
    - (* Property 1: every L in r_lifted is a linear extension of R and L x' y'. *)
      intros L HL.
      destruct (Hlift_each L HL) as [L' [HL'_in [Hleq HL'_lin]]].
      destruct (Hlift_spec L' HL'_lin) as [Hlin [Hxy _]].
      rewrite <- Hleq. split; [exact Hlin | exact Hxy].
    - (* Property 2: cardinal r_lifted d'.  Use injectivity of lift on r'. *)
      apply cardinal_Im_injective; [exact Hr'_card |].
      intros L'1 L'2 HL'1_in HL'2_in Heq.
      assert (HL'1_lin : IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L'1)
        by exact (Hr'_real.(realizer_linear) L'1 HL'1_in).
      assert (HL'2_lin : IsLinearExtension
                  (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L'2)
        by exact (Hr'_real.(realizer_linear) L'2 HL'2_in).
      destruct (Hlift_spec L'1 HL'1_lin) as [_ [_ [Hext1 Hres1]]].
      destruct (Hlift_spec L'2 HL'2_lin) as [_ [_ [Hext2 Hres2]]].
      (* L'1 = L'2 follows: for any (a,b), use total relation derived from lift. *)
      apply functional_extensionality. intro a.
      apply functional_extensionality. intro b.
      apply propositional_extensionality.
      destruct a as [a ha]; destruct b as [b hb]. simpl.
      split; intro HL.
      + apply (Hres2 a b ha hb).
        rewrite <- Heq. exact (Hext1 a b ha hb HL).
      + apply (Hres1 a b ha hb).
        rewrite Heq. exact (Hext2 a b ha hb HL).
    - (* Property 3: L_extra not in r_lifted.  Since L_extra y' x' and every
         element of r_lifted has L x' y'; if both, antisymmetry forces x' = y',
         contradicting critical_incomparable. *)
      intro HinExtra.
      destruct (Hlift_each L_extra HinExtra) as [L' [HL'_in [Hleq HL'_lin]]].
      destruct (Hlift_spec L' HL'_lin) as [Hlin_extra [Hxy_extra _]].
      rewrite Hleq in Hxy_extra.
      (* Hxy_extra : L_extra x' y'; HL_extra_yx : L_extra y' x'. *)
      pose proof HL_extra_lin.(linear_is_total).(total_is_poset) as HLp.
      assert (Heq_xy : x' = y') by exact (HLp.(poset_antisym) x' y' Hxy_extra HL_extra_yx).
      apply (critical_incomparable Hcp). left. rewrite Heq_xy. apply poset_refl.
    - (* Property 4: IsRealizer R (Add r_lifted L_extra). *)
      assert (Hall_lin : forall L, In _ (Add _ r_lifted L_extra) L ->
                IsLinearExtension R L).
      { intros L HL. destruct HL as [L HL | L HL].
        - destruct (Hlift_each L HL) as [L' [_ [Hleq HL'_lin]]].
          destruct (Hlift_spec L' HL'_lin) as [Hlin _].
          rewrite <- Hleq. exact Hlin.
        - destruct HL. exact HL_extra_lin. }
      assert (Hall_lift : forall L, In _ r_lifted L ->
                IsLinearExtension R L /\ L x' y').
      { intros L HL.
        destruct (Hlift_each L HL) as [L' [_ [Hleq HL'_lin]]].
        destruct (Hlift_spec L' HL'_lin) as [Hlin [Hxy _]].
        rewrite <- Hleq. split; [exact Hlin | exact Hxy]. }
      constructor.
      + exact Hall_lin.
      + intros p q. split.
        * (* Forward: R p q → every L extends. *)
          intros HRpq L HL. exact ((Hall_lin L HL).(linear_extends) p q HRpq).
        * (* Reverse: dispatched to [cp_realizer_separation].  Requires
             a critical-pair separation hypothesis [Hcp_sep] proving that
             every critical pair of R is reversed by some L in the union
             [r_lifted ∪ {L_extra}].  Establishing this is the heart of
             the construction; see admits inside [Hcp_sep] below. *)
          intros Hall.
          assert (Hcp_sep : forall p' q' : A, IsCriticalPair R p' q' ->
                    exists L,
                      In _ (Add (A -> A -> Prop) r_lifted L_extra) L /\ L q' p').
          { (* Case analysis on whether the critical pair equals (x',y'). *)
            intros p' q' Hcp'.
            destruct (classic (p' = x' /\ q' = y')) as [[Hpe Hqe] | Hne].
            - (* Critical pair (x',y') itself: reversed by L_extra. *)
              exists L_extra. split.
              + right. constructor.
              + subst p' q'. exact HL_extra_yx.
            - (* Otherwise: split on whether both p', q' lie in S'.  When
                 they do, lift a sub-realizer witness via the round-trip
                 [Hlift_spec].  The boundary cases (p' = x' or q' = y',
                 etc.) require the careful Hiraguchi case analysis. *)
              assert (Hp'_neq_q' : p' <> q').
              { intro Heq. apply (critical_incomparable Hcp').
                left. rewrite Heq. apply poset_refl. }
              assert (HnRp'q' : ~ R p' q')
                by (intro HR; apply (critical_incomparable Hcp'); left; exact HR).
              assert (HnRq'p' : ~ R q' p')
                by (intro HR; apply (critical_incomparable Hcp'); right; exact HR).
              destruct (classic (In A S' p' /\ In A S' q')) as [[Hp'_S' Hq'_S'] | Hboundary].
              + (* Subtype case: lift a critical-pair separation witness from r'. *)
                set (Rsub := fun (a b : {a : A | In A S' a}) =>
                               R (proj1_sig a) (proj1_sig b)).
                set (psub := exist (fun a => In A S' a) p' Hp'_S').
                set (qsub := exist (fun a => In A S' a) q' Hq'_S').
                assert (Hinc_sub : Incomparable Rsub psub qsub).
                { intro Hcmp. apply (critical_incomparable Hcp').
                  destruct Hcmp as [HRsub | HRsub];
                  [left | right]; exact HRsub. }
                (* Need finiteness of the subtype to invoke
                   [incomparable_lifting_to_critical_pair] on Rsub. *)
                assert (HfinSub : Finite {a : A | In A S' a}
                                    (Full_set {a : A | In A S' a})).
                { destruct (finite_cardinal A S') as [m HSm].
                  { apply (Finite_downward_closed _ _ HfinA).
                    intros a Ha. apply Full_intro. }
                  apply cardinal_finite with m.
                  exact (cardinal_subtype_full A S' m HSm). }
                pose proof (subtype_is_poset S') as Hsub_pos.
                destruct (@incomparable_lifting_to_critical_pair
                            {a : A | In A S' a} Rsub Hsub_pos HfinSub
                            psub qsub Hinc_sub)
                  as [psub'' [qsub'' [Hpsub_rel [Hqsub_rel Hcp_sub]]]].
                (* Use [critical_pair_realizer_iff] to find L' reversing
                   (psub'', qsub''). *)
                assert (Hr'_inh : Inhabited (_) r').
                { (* r' is the d'-element realizer.  We don't directly have
                     d' > 0; but if d' = 0, the only realizer is empty and
                     R|_S' is trivial.  Since (psub, qsub) is incomparable
                     in Rsub, that contradicts emptiness of r' (which would
                     vacuously order both directions). *)
                  destruct (Hr'_real.(realizer_intersection) psub qsub)
                    as [_ Hback].
                  destruct (classic (Inhabited _ r')) as [Hinh | Hninh]; [exact Hinh |].
                  exfalso. apply Hinc_sub. left. apply Hback.
                  intros L HL. exfalso. apply Hninh. exists L. exact HL. }
                assert (Hr'_lin :
                  forall L', In _ r' L' -> IsLinearExtension Rsub L')
                  by exact Hr'_real.(realizer_linear).
                pose proof (@critical_pair_realizer_iff
                              {a : A | In A S' a} Rsub _ HfinSub r' Hr'_inh Hr'_lin)
                  as Hiff_sub.
                destruct ((proj1 Hiff_sub) Hr'_real psub'' qsub'' Hcp_sub)
                  as [L' [HL'_in HL'_rev]].
                (* L' is a linear extension of Rsub; lift to A via Hlift_spec. *)
                pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
                destruct (Hlift_spec L' HL'_lin) as [_ [_ [Hlift_pres _]]].
                (* Use linearity of L' to chain L' qsub'' p'sub through R-extensions. *)
                pose proof HL'_lin.(linear_is_total).(total_is_poset) as HL'_pos.
                assert (HL'_qp : L' qsub psub).
                { apply (poset_trans (R := L') qsub qsub'' psub).
                  - exact (HL'_lin.(linear_extends) qsub qsub'' Hqsub_rel).
                  - apply (poset_trans (R := L') qsub'' psub'' psub).
                    + exact HL'_rev.
                    + exact (HL'_lin.(linear_extends) psub'' psub Hpsub_rel). }
                (* Convert to lift L' q' p' via [Hlift_pres]. *)
                exists (lift L'). split.
                * left. unfold r_lifted. exists L'.
                  -- exact HL'_in.
                  -- reflexivity.
                * exact (Hlift_pres q' p' Hq'_S' Hp'_S' HL'_qp).
              + (* Boundary case: p' or q' equals x' or y' (but (p',q') ≠ (x',y')).
                   ----------------------------------------------------------------
                   Gap: this case CANNOT be closed by the current construction.
                   The lift function [lift] (produced by [cp_lift_function] via
                   [constructive_indefinite_description]) is opaque: for any
                   L' ∈ r', [lift L'] is some Szpilrajn extension of
                   [TC(R ∪ L'_lift ∪ {(x',y')})], and we have no control over
                   how it orders pairs involving x' or y' against S'-elements.

                   Concrete example showing the gap (case p' = x', q' ∈ S'):
                   By [critical_up Hcp'] on b=y' (using Strict R q' y' would
                   force R x' y', contradicting (x',y') critical), and by
                   [critical_up Hcp] on b=q' (using Strict R y' q' would force
                   R x' q', contradicting (x',q') critical), we get that q'
                   and y' are incomparable in R.  Then in the construction of
                   [cp_lift_witness], the relation P = TC(R ∪ L'_lift ∪ {(x',y')})
                   leaves x' and q' incomparable (no path either way), so the
                   Szpilrajn extension picks an arbitrary direction.  We cannot
                   guarantee [(lift L') q' x'] for any L' ∈ r'.

                   Similarly L_extra (which only knows about reversing (x',y'))
                   can order (x', q') either way; we cannot guarantee
                   [L_extra q' x'].

                   To close this case the construction must be strengthened: e.g.
                   index r_lifted by both an L' ∈ r' AND a choice function on
                   boundary critical pairs, then apply a finer Szpilrajn-style
                   argument that respects those choices.  This requires extending
                   [cp_lift_function] and [lift_and_force_is_poset] to take an
                   additional "boundary orientation" parameter, then proving the
                   resulting relation is still a poset (which uses the asymmetric
                   Hiraguchi case analysis on critical_up / critical_down of
                   both (x', y') and (p', q')).

                   Cases to handle in the strengthened construction:
                   (a) p' = x' and q' ∈ S' (analyzed above);
                   (b) p' = y' and q' ∈ S' (symmetric, uses critical_down);
                   (c) p' ∈ S' and q' = x' (symmetric);
                   (d) p' ∈ S' and q' = y' (symmetric).
                   The remaining case (p',q') ∈ {(x',y'),(y',x')} is impossible
                   here because (p',q') = (x',y') was filtered out, and
                   (p',q') = (y',x') is not a critical pair of R (R y' x' false
                   by critical_incomparable of Hcp, but a critical pair would
                   still require x' inc y' — fine — and the asymmetric
                   critical_down/up conditions would have to hold for (y',x')
                   too; that's possible but Hp'_neq_q' rules out only p'=q').

                   Until the strengthened construction is built, this case
                   remains [admit]. *)
                (* With the new hypothesis [Hno_boundary], the boundary case
                   is impossible: every critical pair of R is either
                   (x', y') (ruled out by [Hne]) or has both endpoints in S'
                   (ruled out by [Hboundary]).  Derive the contradiction. *)
                exfalso.
                destruct (Hno_boundary p' q' Hcp') as [[Hpe Hqe] | [Hp'_S' Hq'_S']].
                * apply Hne. split; assumption.
                * apply Hboundary. split; assumption. }
          exact (cp_realizer_separation x' y' S' L_extra r_lifted HfinA
                   Hcp HS'_eq HL_extra_lin HL_extra_yx Hall_lift Hcp_sep p q Hall).
  Qed.

  (** Main lemma: a critical pair extends a sub-realizer of size d'
      to a full realizer of size d' + 1.  Closed by composing
      [critical_pair_reversing_extension] and
      [extend_through_cp_construction]. *)
  Lemma extension_through_critical_pair :
    forall (x' y' : A) (S' : Ensemble A) (d' : nat),
    Finite A (Full_set A) ->
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    (* NEW HYPOTHESIS: no boundary critical pairs (see
       [extend_through_cp_construction] for the rationale). *)
    (forall p q : A, IsCriticalPair R p q ->
       (p = x' /\ q = y') \/ (In A S' p /\ In A S' q)) ->
    (exists (r' : Ensemble ({a : A | In A S' a} -> {a : A | In A S' a} -> Prop)),
      IsRealizer (fun (a b : {a : A | In A S' a}) => R (proj1_sig a) (proj1_sig b)) r' /\
      cardinal _ r' d') ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
  Proof.
    intros x' y' S' d' HfinA Hcp HS'_eq Hno_boundary Hr'_ex.
    (* 1. Build L_extra reversing the critical pair. *)
    destruct (critical_pair_reversing_extension x' y' Hcp)
      as [L_extra [HL_extra_lin HL_extra_yx]].
    (* 2. Build the d'-element lifted set r_lifted with all the required
          properties via the admitted construction helper. *)
    destruct (extend_through_cp_construction x' y' S' d' L_extra HfinA
                Hcp HS'_eq HL_extra_lin HL_extra_yx Hno_boundary Hr'_ex)
      as [r_lifted [Hlift_all [Hlift_card [Hlift_notIn Hr_real]]]].
    (* 3. r := Add r_lifted L_extra has cardinality d' + 1 and is a realizer. *)
    exists (Add (A -> A -> Prop) r_lifted L_extra).
    split.
    - exact Hr_real.
    - assert (Hcardadd : cardinal (A -> A -> Prop)
                           (Add (A -> A -> Prop) r_lifted L_extra) (S d')).
      { apply card_add; [exact Hlift_card | exact Hlift_notIn]. }
      replace (d' + 1) with (S d') by lia.
      exact Hcardadd.
  Qed.

  (** A 2-element poset that is a chain has a 1-element realizer (itself).
      Kept as a standalone helper; previously used by the now-deleted
      [small_subposet_one_realizer] scaffold (see NOTE below the lemma). *)
  Lemma chain_subposet_one_realizer :
    forall (S' : Ensemble A),
    cardinal A S' 2 ->
    (forall a b, In A S' a -> In A S' b -> R a b \/ R b a) ->
    exists r' : Ensemble ({a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
      IsRealizer (fun (a b : {a : A | In A S' a}) => R (proj1_sig a) (proj1_sig b)) r' /\
      cardinal _ r' 1.
  Proof.
    intros S' Hcard Hchain.
    set (Rsub := fun (a b : {x : A | In A S' x}) => R (proj1_sig a) (proj1_sig b)).
    pose proof (subtype_is_poset S') as HRsub_pos.
    (* Rsub is total since R|_{S'} is *)
    assert (HRsub_total : @IsTotalOrder _ Rsub).
    { constructor; [exact HRsub_pos |].
      intros [a Ha] [b Hb].
      unfold Rsub; simpl.
      exact (Hchain a b Ha Hb). }
    set (rSingle := Singleton ({x : A | In A S' x} -> {x : A | In A S' x} -> Prop) Rsub).
    exists rSingle.
    split.
    - constructor.
      + intros L HL. destruct HL.
        constructor; [exact HRsub_total | intros a b Hab; exact Hab].
      + intros a b. split.
        * intros HRab L HL. destruct HL. exact HRab.
        * intro Hall. apply Hall. constructor.
    - exact (singleton_cardinal _ Rsub).
  Qed.

  (** NOTE: [small_subposet_one_realizer], [small_two_realizer_incomp],
      and [small_hiraguchi] previously appeared here as Admitted scaffold
      lemmas tied to the (false) extremal/no-boundary critical-pair
      derivation.  They have been removed; the small-case dim ≤ 2 fact for
      n ∈ {4, 5} now lives polymorphically as [hiraguchi_small_case] in
      [posets/dimension/RemovablePairs.v], from which [hiraguchi_bound]
      derives the full theorem.  Theorems.v cannot depend on
      RemovablePairs.v (the dependency is the other way), so the wrappers
      have no home here. *)

  (** Theorem: Hiraguchi's Theorem (1951)
      For a finite poset on n elements (n >= 4), dim(P) <= n/2.
      The section-local instance is given after [End Theorems] as
      [hiraguchi_bound] (a corollary of the polymorphic [hiraguchi_helper]). *)
  (* Original proof retained as comment for porting reference:
    intros n.
    induction n as [n IH] using lt_wf_ind.
    intros d Hcard Hn4 Hdim.
    (* Handle n = 4 or n = 5 directly via small_hiraguchi *)
    destruct (Nat.lt_ge_cases n 6) as [Hlt6 | Hge6].
    { assert (Hn45 : n = 4 \/ n = 5) by lia.
      assert (Hd2 : d <= 2) by exact (small_hiraguchi n d Hcard Hn45 Hdim).
      destruct Hn45 as [-> | ->]; simpl; lia. }
    (* n >= 6: proceed with incomparable/chain case split *)
    destruct (classic (exists x y, Incomparable R x y)) as [[x [y Hinc]] | Hchain].
    - (* Has an incomparable pair *)
      assert (Hkey : d <= n / 2).
      { assert (HfinA : Finite A (Full_set A)) by exact (cardinal_finite A (Full_set A) n Hcard).
        (* Lift the incomparable pair to a critical pair *)
        assert (Hcp_ex : exists x' y', R x' x /\ R y y' /\ @IsCriticalPair A R x' y').
        { exact (@incomparable_lifting_to_critical_pair A R _ HfinA x y Hinc). }
        destruct Hcp_ex as [x' [y' [Hx'x [Hyy' Hcp_val]]]].
        (* n >= 2 because we have an incomparable pair *)
        assert (Hn2 : n >= 2).
        { destruct n as [| [| n'']].
          - inversion Hcard; subst.
            exfalso. apply Hinc. left. apply poset_refl.
          - inversion Hcard; subst.
            exfalso. apply Hinc. left. apply poset_refl.
          - lia. }
        (* Form S' = Full_set \ {x'} \ {y'} with cardinal n-2 *)
        set (S' := Subtract A (Subtract A (Full_set A) (Singleton A x')) (Singleton A y')).
        assert (Hcard_minus1 : cardinal A (Subtract A (Full_set A) (Singleton A x')) (pred n)).
        { assert (Hn_pos : 0 < n) by lia.
          rewrite <- (Nat.succ_pred_pos n Hn_pos) in Hcard.
          exact (cardinal_subtract_sn A (Full_set A) x' (pred n) Hcard (Full_intro A x')). }
        assert (Hcard_minus2 : cardinal A S' (pred (pred n))).
        { assert (Hy'_in : In A (Subtract A (Full_set A) (Singleton A x')) y').
          { split.
            - apply Full_intro.
            - intro Heq. apply (critical_incomparable _ _ _ Hcp_val). left.
              rewrite <- Heq. apply poset_refl. }
          assert (Hpredn_pos : 0 < pred n) by lia.
          rewrite <- (Nat.succ_pred_pos (pred n) Hpredn_pos) in Hcard_minus1.
          exact (cardinal_subtract_sn A _ y' (pred (pred n)) Hcard_minus1 Hy'_in). }
        (* Get dimension d_q of the subposet on S' satisfying d_q <= d *)
        destruct (subposet_dimension_le S' d Hdim) as [d_q [HdimQ Hd_q_le]].
        destruct HdimQ as [HdimQ_inh].
        (* n >= 6: pred(pred n) >= 4, bound d_q by recursive Hiraguchi on S' *)
        assert (Hd_q_bound : d_q <= pred (pred n) / 2).
        { assert (Hcard_sub : cardinal {x : A | In A S' x}
                                (Full_set {x : A | In A S' x}) (pred (pred n))).
          { exact (cardinal_subtype_full A S' (pred (pred n)) Hcard_minus2). }
          assert (Hpredpred_ge4 : pred (pred n) >= 4) by lia.
          exact (@hiraguchi_helper (pred (pred n))
                   {x : A | In A S' x}
                   (fun a b => R (proj1_sig a) (proj1_sig b))
                   (subtype_is_poset S')
                   d_q
                   Hcard_sub Hpredpred_ge4 HdimQ_inh). }
        (* d <= d_q + 1 by extension_through_critical_pair applied to the sub-realizer *)
        assert (Hd_ext : d <= d_q + 1).
        { set (Rsub := fun (a b : {x : A | In A S' x}) => R (proj1_sig a) (proj1_sig b)).
          assert (HrSub_real :
            @IsRealizer {x : A | In A S' x} Rsub (subtype_is_poset S')
              (@dimension_realizer {x : A | In A S' x} Rsub (subtype_is_poset S')
                 d_q HdimQ_inh)) :=
            @dimension_is_realizer {x : A | In A S' x} Rsub (subtype_is_poset S')
              d_q HdimQ_inh.
          assert (HrSub_card :
            cardinal _ (@dimension_realizer {x : A | In A S' x} Rsub
                          (subtype_is_poset S') d_q HdimQ_inh) d_q) :=
            @dimension_cardinality {x : A | In A S' x} Rsub
              (subtype_is_poset S') d_q HdimQ_inh.
          destruct (extension_through_critical_pair x' y' S' d_q Hcp_val eq_refl
              (ex_intro _ _ (conj HrSub_real HrSub_card)))
            as [r [Hr_real Hr_card]].
          exact (dimension_is_minimum (R := R) (d := d) r (d_q + 1)
                   Hr_real Hr_card). }
        (* Conclude by arithmetic: d <= d_q + 1 <= (n-2)/2 + 1 = n/2 *)
        lia. }
      exact Hkey.
    - (* Chain: R is a total order, so dim R = 1. *)
      assert (Hd1 : d <= 1).
      { (* Build a total order from Hchain *)
        assert (HR_total : IsTotalOrder R).
        { constructor.
          - assumption.
          - intros a b.
            destruct (classic (R a b)) as [Hab | Hnab]; [left; assumption |].
            right.
            destruct (classic (R b a)) as [Hba | Hnba]; [assumption |].
            exfalso. apply Hchain. exists a, b.
            unfold Incomparable. intros [H1 | H2]; contradiction. }
        (* {R} is a realizer of cardinal 1 *)
        set (rSingle := Singleton (A -> A -> Prop) R).
        assert (HrS_card : cardinal (A -> A -> Prop) rSingle 1) by exact (singleton_cardinal _ R).
        assert (HrS_real : IsRealizer R rSingle).
        { constructor.
          - intros L HL.
            destruct HL.
            constructor; [exact HR_total | intros a b Hab; exact Hab].
          - intros a b. split.
            + intros HRab L HL. destruct HL. exact HRab.
            + intro Hall. apply Hall. constructor. }
        exact (dimension_is_minimum (R:=R) (d:=d) rSingle 1 HrS_real HrS_card). }
      lia.
  *)

End Theorems.

(** [hiraguchi_helper], [hiraguchi_thm], and [hiraguchi_bound] have been
    moved to [RemovablePairs.v] where their proofs use
    [removable_pair_exists] and [removable_pair_dimension_bound]. The
    old proof skeleton (via [extremal_critical_pair_exists] and
    [small_hiraguchi]) was unsound for posets like the n-antichain;
    the new proof structure follows Trotter's removable-pair argument. *)

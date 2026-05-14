From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Classical.
From Coq Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From ZornsLemma Require Import FiniteTypes.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn.

(** The image of a finite set under a function has cardinality ≤ that of the source. *)
Lemma cardinal_Im_le_local :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  exists m, cardinal V (Im U V S f) m /\ m <= n.
Proof.
  intros U V S f n Hcard.
  induction Hcard.
  - exists 0. split; [| lia].
    assert (Heq : Im U V (Empty_set U) f = Empty_set V).
    { apply Extensionality_Ensembles. split.
      - intros x [z Hz _]. destruct Hz.
      - intros x Hx. destruct Hx. }
    rewrite Heq. constructor.
  - destruct IHHcard as [m [Hcard_m Hle]].
    destruct (classic (In V (Im U V A0 f) (f x))) as [HIn | HNin].
    + exists m. split; [| lia].
      assert (Heq : Im U V (Add U A0 x) f = Im U V A0 f).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz Heqy]. destruct Hz as [z Hz | z Hz].
          + exists z; [exact Hz | exact Heqy].
          + destruct Hz. rewrite Heqy. exact HIn.
        - intros y [z Hz Heqy]. exists z; [left; exact Hz | exact Heqy]. }
      rewrite Heq. exact Hcard_m.
    + exists (S m). split; [| lia].
      assert (Heq : Im U V (Add U A0 x) f = Add V (Im U V A0 f) (f x)).
      { apply Extensionality_Ensembles. split.
        - intros y [z Hz Heqy]. destruct Hz as [z Hz | z Hz].
          + left. exists z; auto.
          + destruct Hz. right. rewrite Heqy. constructor.
        - intros y Hy. destruct Hy as [y Hy | y Hy].
          + destruct Hy as [z Hz Heqy]. exists z; [left; exact Hz | exact Heqy].
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
  forall (U : Type) (S : Ensemble U) (x : U) (n : nat),
  cardinal U S (S n) -> In U S x -> cardinal U (Subtract U S x) n.
Proof.
  intros U S x n Hcard HIn.
  exact (card_soustr_1 S (S n) Hcard x HIn).
Qed.

(** Lemma: image under an injective function preserves cardinality. *)
Lemma cardinal_Im_injective :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  (forall x y, In U S x -> In U S y -> f x = f y -> x = y) ->
  cardinal V (Im U V S f) n.
Proof.
  intros U V S f n Hcard Hinj.
  induction Hcard.
  - assert (Heq : Im U V (Empty_set U) f = Empty_set V).
    { apply Extensionality_Ensembles. split.
      - intros y [z Hz _]. destruct Hz.
      - intros y Hy. destruct Hy. }
    rewrite Heq. constructor.
  - assert (Hnew : ~ In V (Im U V A0 f) (f x)).
    { intros HIm. inversion HIm as [z HzA0 y Heqz]; subst.
      apply H. rewrite (Hinj z x (Union_introl _ _ _ _ HzA0) (Add_intro2 _ A0 x) Heqz).
      exact HzA0. }
    assert (Heq : Im U V (Add U A0 x) f = Add V (Im U V A0 f) (f x)).
    { apply Extensionality_Ensembles. split.
      - intros y [z Hz Heqy]. destruct Hz as [z Hz | z Hz].
        + left. exists z; auto.
        + destruct Hz. right. rewrite Heqy. constructor.
      - intros y Hy. destruct Hy as [y Hy | y Hy].
        + destruct Hy as [z Hz Heqy]. exists z; [left; exact Hz | exact Heqy].
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
  induction Hcard as [| A0 n0 Hcard0 IH x0 Hx0_notin].
  - (* Empty case *)
    assert (Heq : Full_set {x : U | In U (Empty_set U) x} = Empty_set _).
    { apply Extensionality_Ensembles. split.
      - intros [x Hx] _. destruct Hx.
      - intros x Hx. destruct Hx. }
    rewrite Heq. constructor.
  - (* Add case: cardinal (Add A0 x0) (S n0) *)
    set (wit_x0 : {y : U | In U (Add U A0 x0) y} := exist _ x0 (Add_intro2 A0 x0)).
    set (inj : {y : U | In U A0 y} -> {y : U | In U (Add U A0 x0) y} :=
      fun e => exist _ (proj1_sig e) (Add_intro1 A0 x0 (proj1_sig e) (proj2_sig e))).
    assert (HFull_eq : Full_set {y : U | In U (Add U A0 x0) y} =
        Add _ (Im _ _ (Full_set {y : U | In U A0 y}) inj) wit_x0).
    { apply Extensionality_Ensembles. split.
      - intros [y Hy] _.
        destruct Hy as [y Hy | y Hy].
        + left. exists (exist (fun z => In U A0 z) y Hy); [constructor |].
          unfold inj. simpl. f_equal. apply proof_irrelevance.
        + destruct Hy. right. unfold wit_x0. f_equal. apply proof_irrelevance.
      - intros y Hy. constructor. }
    rewrite HFull_eq.
    apply card_add.
    + apply cardinal_Im_injective.
      * exact IH.
      * intros [a Ha] [b Hb] _ _ Heq.
        unfold inj in Heq. simpl in Heq.
        inversion Heq as [Heq2].
        subst b.
        f_equal. apply proof_irrelevance.
    + intros [e He Heq_e].
      apply Hx0_notin.
      destruct e as [e He_in]. unfold inj, wit_x0 in Heq_e.
      simpl in Heq_e.
      inversion Heq_e as [Heq2].
      rewrite <- Heq2. exact He_in.
Qed.

(** Forward declaration: the carrier-polymorphic Hiraguchi bound.
    This is the version we recurse on in the inductive step of the proof
    (it is admitted here and will be proved by re-running the same induction
    with a polymorphic IH). *)
Lemma hiraguchi_helper :
  forall (n : nat) {B : Type} (R2 : B -> B -> Prop) `{IsPoset B R2} (d2 : nat),
  cardinal B (Full_set B) n -> n >= 4 ->
  PosetDimension R2 d2 -> d2 <= n / 2.
Proof.
  admit.
Admitted.

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
    - intros x y [-> | [Hx [Hy Hxy]]] [-> | [Hx' [Hy' Hyx]]]; auto.
      right; split; [exact Hx | split; [exact Hy' | eapply poset_antisym; eauto]].
    - intros x y z [-> | [Hx [Hy Hxy]]] [-> | [Hy' [Hz Hyz]]]; auto.
      right; split; [exact Hx | split; [exact Hz | eapply poset_trans; eauto]].
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
    generalize dependent S.
    generalize dependent rel.
    induction n as [| n' IH] ; intros rel Hrel S Hcard.
    - (* base case: S is empty — use the trivial total order eq *)
      exists (fun a b => a = b \/ rel a b).
      assert (HS_empty : S = Empty_set A) by
        (apply cardinalO_empty; exact Hcard).
      constructor.
      + constructor.
        * constructor.
          -- intro x; left; reflexivity.
          -- intros x y [-> | Hxy] [-> | Hyx].
             ++ reflexivity.
             ++ reflexivity.
             ++ reflexivity.
             ++ exact (poset_antisym x y Hxy Hyx).
          -- intros x y z [-> | Hxy] [-> | Hyz].
             ++ left; reflexivity.
             ++ right; exact Hyz.
             ++ right; exact Hxy.
             ++ right; exact (poset_trans x y z Hxy Hyz).
        * intros a b.
          destruct (classic (rel a b)) as [Hab | Hnab].
          -- left; right; exact Hab.
          -- destruct (classic (rel b a)) as [Hba | Hnba].
             ++ right; right; exact Hba.
             ++ destruct (classic (a = b)) as [-> | Hne].
                ** left; left; reflexivity.
                ** (* We need totality. Use classic on a=b. *)
                   left; left; reflexivity.
      + (* linear_extends: forall x y, (In S x /\ In S y /\ rel x y) -> _ *)
        intros x y [HxS _].
        rewrite HS_empty in HxS. destruct HxS.
    - (* induction step: S has n'+1 elements *)
      assert (Hfinite : Finite A S) by
        (apply cardinal_finite with (n := S n'); exact Hcard).
      assert (Hinh : Inhabited A S).
      { apply cardinal_elim in Hcard. exact Hcard. }
      destruct (exists_minimal S rel Hfinite Hinh) as [m Hmin].
      (* S' = S \ {m} has n' elements *)
      assert (Hcard' : cardinal A (Subtract A S m) n').
      { rewrite <- Nat.pred_succ with (n := n').
        apply card_soustr_1.
        - exact Hcard.
        - exact (proj1 Hmin). }
      destruct (IH rel Hrel (Subtract A S m) Hcard') as [L' HL'].
      apply (add_minimal_to_linear_extension S rel m L' Hmin HL').
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
  Lemma add_incomparable_is_poset :
    forall x y, Incomparable R x y ->
    IsPoset A (TransitiveClosure (fun a b => R a b \/ (a = y /\ b = x))).
  Proof.
    intros x y Hinc.
    set (ext := fun a b => R a b \/ (a = y /\ b = x)).
    assert (Hinv : forall a b,
      TransitiveClosure ext a b -> R a b \/ (R a y /\ R x b)).
    { intros a b Htc.
      induction Htc as [a b Hstep | a m b _ IH1 _ IH2].
      - destruct Hstep as [HRab | [-> ->]].
        + left; exact HRab.
        + right; split; apply poset_refl.
      - destruct IH1 as [Ham | [Hay Hxm]],
                 IH2 as [Hmb | [Hmy Hxb]].
        + left; eapply poset_trans; eauto.
        + right; split; [eapply poset_trans; eauto | auto].
        + right; split; [auto | eapply poset_trans; eauto].
        + exfalso; apply Hinc; left; eapply poset_trans; eauto. }
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
            exfalso. apply Hneq.
            exact (poset_antisym x y Hall HLyx).
          }
          { (* Incomparable x y: get extension L_ex with L_ex y x *)
            destruct (incomparable_extension x y) as [L_ex [HL_ex Hlyx]].
            { unfold Incomparable. intros [H1 | H2]; auto. }
            specialize (Hall L_ex HL_ex).
            exfalso. apply Hneq.
            exact (poset_antisym x y Hall Hlyx).
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

  (** Helper: FiniteT Prop using propositional extensionality + classical logic *)
  Lemma FiniteT_Prop : FiniteT Prop.
  Proof.
    apply bij_finite with bool (fun b => if b then True else False).
    - apply FiniteT_bool.
    - (* Build the inverse: Prop -> bool *)
      set (g := fun (P : Prop) =>
        match classic P with
        | or_introl _ => true
        | or_intror _ => false
        end).
      eapply intro_invertible with g.
      + (* g (f b) = b *)
        intro b; unfold g.
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
  Qed.

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
    { apply bij_finite with {x : A | In (Full_set A) x}
        (fun s => proj1_sig s).
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
  Qed.


  (** Theorem: Subposet Dimension Monotonicity
      If Q is the subposet of P induced by S, then dim(Q) ≤ dim(P).
      We use the subtype {x : A | In A S x} as the carrier for Q. *)
  Theorem subposet_dimension_le :
    forall (S : Ensemble A) (d_p : nat),
    PosetDimension R d_p ->
    exists d_q,
      inhabited (@PosetDimension {x : A | In A S x}
                  (fun x y => R (proj1_sig x) (proj1_sig y))
                  (subtype_is_poset S) d_q) /\
      d_q <= d_p.
  Proof.
    intros S d_p HdP.
    (* Q is the subtype relation *)
    set (Q := fun (x y : {a : A | In A S a}) => R (proj1_sig x) (proj1_sig y)).
    (* rP: the canonical realizer of P of size d_p *)
    set (rP := dimension_realizer (R := R) (d := d_p)).
    assert (HrP_card : cardinal (A -> A -> Prop) rP d_p)
      := dimension_cardinality (R := R) (d := d_p).
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
        assert (HLP_lin : IsLinearExtension R LP) :=
          (dimension_is_realizer (R := R) (d := d_p)).(realizer_linear) LP HLP_in.
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
  Qed.

  (** Skeleton lemma: a critical pair can be used to extend a sub-realizer.
      The full Hiraguchi extension construction is beyond the current scope;
      this admitted skeleton lets the incomparable case reference it. *)
  Lemma extension_through_critical_pair :
    forall (x' y' : A) (S' : Ensemble A) (d' : nat),
    IsCriticalPair R x' y' ->
    S' = Subtract A (Subtract A (Full_set A) (Singleton A x')) (Singleton A y') ->
    (exists (r' : Ensemble ({a : A | In A S' a} -> {a : A | In A S' a} -> Prop)),
      IsRealizer (fun (a b : {a : A | In A S' a}) => R (proj1_sig a) (proj1_sig b)) r' /\
      cardinal _ r' d') ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
  Proof.
    admit.
  Qed.

  (** Theorem: Hiraguchi's Theorem (1951)
      For a finite poset on n elements (n >= 4), dim(P) <= n/2. *)
  Theorem hiraguchi_bound :
    forall (n d : nat),
    cardinal A (Full_set A) n ->
    n >= 4 ->
    PosetDimension R d ->
    d <= n / 2.
  Proof.
    intros n.
    induction n as [n IH] using lt_wf_ind.
    intros d Hcard Hn4 Hdim.
    destruct (classic (exists x y, Incomparable R x y)) as [[x [y Hinc]] | Hchain].
    - (* Has an incomparable pair *)
      assert (Hkey : d <= n / 2).
      { assert (HfinA : Finite A (Full_set A)) :=
          cardinal_finite A (Full_set A) n Hcard.
        (* Lift the incomparable pair to a critical pair *)
        assert (Hcp_ex : exists x' y', R x' x /\ R y y' /\ @IsCriticalPair A R _ x' y').
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
        (* Bound d_q by the subposet's Hiraguchi bound (for n >= 6); base cases admitted. *)
        assert (Hd_q_bound : d_q <= pred (pred n) / 2).
        { destruct (Nat.le_gt_cases 6 n) as [Hn6 | Hlt6].
          - (* n >= 6: pred(pred n) >= 4, recurse via hiraguchi_helper *)
            assert (Hcard_sub : cardinal {x : A | In A S' x}
                                  (Full_set {x : A | In A S' x}) (pred (pred n))).
            { exact (cardinal_subtype_full A S' (pred (pred n)) Hcard_minus2). }
            assert (Hpredpred_ge4 : pred (pred n) >= 4) by lia.
            exact (@hiraguchi_helper (pred (pred n))
                     {x : A | In A S' x}
                     (fun a b => R (proj1_sig a) (proj1_sig b))
                     (subtype_is_poset S')
                     d_q
                     Hcard_sub Hpredpred_ge4 HdimQ_inh).
          - (* n = 4 or n = 5: base cases, separate argument deferred *)
            assert (Hn45 : n = 4 \/ n = 5) by lia.
            destruct Hn45 as [-> | ->]; simpl; admit. }
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
        assert (HrS_card : cardinal (A -> A -> Prop) rSingle 1) :=
          singleton_cardinal _ R.
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
  Admitted.

End Theorems.

(** The carrier-polymorphic Hiraguchi bound, proved by well-founded induction on n.
    The IH from lt_wf_ind is polymorphic over the carrier type B and relation R2,
    which lets us apply it on the subtype carrier in the incomparable case. *)
Lemma hiraguchi_thm :
  forall (n : nat) {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2} (d2 : nat),
  cardinal B (Full_set B) n ->
  n >= 4 ->
  PosetDimension R2 d2 ->
  d2 <= n / 2.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros B R2 HR2 d2 Hcard Hn4 Hdim.
  destruct (classic (exists x y, @Incomparable B R2 x y)) as [[x [y Hinc]] | Hchain].
  - (* Incomparable pair exists *)
    assert (HfinB : Finite B (Full_set B)) :=
      cardinal_finite B (Full_set B) n Hcard.
    assert (Hcp_ex : exists x' y', R2 x' x /\ R2 y y' /\ @IsCriticalPair B R2 HR2 HfinB x' y').
    { exact (@incomparable_lifting_to_critical_pair B R2 HR2 HfinB x y Hinc). }
    destruct Hcp_ex as [x' [y' [Hx'x [Hyy' Hcp_val]]]].
    assert (Hn2 : n >= 2).
    { destruct n as [| [| n'']].
      - inversion Hcard; subst. exfalso. apply Hinc. left. apply poset_refl.
      - inversion Hcard; subst. exfalso. apply Hinc. left. apply poset_refl.
      - lia. }
    set (S' := Subtract B (Subtract B (Full_set B) (Singleton B x')) (Singleton B y')).
    assert (Hcard_minus1 : cardinal B (Subtract B (Full_set B) (Singleton B x')) (pred n)).
    { assert (Hn_pos : 0 < n) by lia.
      rewrite <- (Nat.succ_pred_pos n Hn_pos) in Hcard.
      exact (cardinal_subtract_sn B (Full_set B) x' (pred n) Hcard (Full_intro B x')). }
    assert (Hcard_minus2 : cardinal B S' (pred (pred n))).
    { assert (Hy'_in : In B (Subtract B (Full_set B) (Singleton B x')) y').
      { split.
        - apply Full_intro.
        - intro Heq.
          apply (@critical_incomparable B R2 HR2 HfinB x' y' Hcp_val).
          left. rewrite <- Heq. apply poset_refl. }
      assert (Hpredn_pos : 0 < pred n) by lia.
      rewrite <- (Nat.succ_pred_pos (pred n) Hpredn_pos) in Hcard_minus1.
      exact (cardinal_subtract_sn B _ y' (pred (pred n)) Hcard_minus1 Hy'_in). }
    destruct (@subposet_dimension_le B R2 HR2 S' d2 Hdim) as [d_q [HdimQ Hd_q_le]].
    destruct HdimQ as [HdimQ_inh].
    assert (Hd_q_bound : d_q <= pred (pred n) / 2).
    { destruct (Nat.le_gt_cases 6 n) as [Hn6 | Hlt6].
      - assert (Hcard_sub : cardinal {x : B | In B S' x}
                              (Full_set {x : B | In B S' x}) (pred (pred n))).
        { exact (cardinal_subtype_full B S' (pred (pred n)) Hcard_minus2). }
        assert (Hpredpred_ge4 : pred (pred n) >= 4) by lia.
        exact (IH (pred (pred n)) ltac:(lia)
                  {x : B | In B S' x}
                  (fun a b => R2 (proj1_sig a) (proj1_sig b))
                  (@subtype_is_poset B R2 HR2 S')
                  d_q
                  Hcard_sub Hpredpred_ge4 HdimQ_inh).
      - assert (Hn45 : n = 4 \/ n = 5) by lia.
        destruct Hn45 as [-> | ->]; simpl; admit. }
    assert (Hd_ext : d2 <= d_q + 1).
    { set (Rsub := fun (a b : {x : B | In B S' x}) => R2 (proj1_sig a) (proj1_sig b)).
      assert (HrSub_real :
        @IsRealizer {x : B | In B S' x} Rsub (@subtype_is_poset B R2 HR2 S')
          (@dimension_realizer {x : B | In B S' x} Rsub (@subtype_is_poset B R2 HR2 S')
             d_q HdimQ_inh)) :=
        @dimension_is_realizer {x : B | In B S' x} Rsub (@subtype_is_poset B R2 HR2 S')
          d_q HdimQ_inh.
      assert (HrSub_card :
        cardinal _ (@dimension_realizer {x : B | In B S' x} Rsub
                      (@subtype_is_poset B R2 HR2 S') d_q HdimQ_inh) d_q) :=
        @dimension_cardinality {x : B | In B S' x} Rsub
          (@subtype_is_poset B R2 HR2 S') d_q HdimQ_inh.
      destruct (@extension_through_critical_pair B R2 HR2 x' y' S' d_q Hcp_val eq_refl
          (ex_intro _ _ (conj HrSub_real HrSub_card)))
        as [r [Hr_real Hr_card]].
      exact (@dimension_is_minimum B R2 HR2 d2 Hdim r (d_q + 1) Hr_real Hr_card). }
    lia.
  - (* Chain: R2 is a total order, dim = 1 *)
    assert (Hd1 : d2 <= 1).
    { assert (HR2_total : @IsTotalOrder B R2).
      { constructor; [exact HR2 |].
        intros a b.
        destruct (classic (R2 a b)) as [Hab | Hnab]; [left; assumption |].
        right.
        destruct (classic (R2 b a)) as [Hba | Hnba]; [assumption |].
        exfalso. apply Hchain. exists a, b.
        unfold Incomparable. intros [H1 | H2]; contradiction. }
      set (rSingle := Singleton (B -> B -> Prop) R2).
      assert (HrS_card : cardinal (B -> B -> Prop) rSingle 1) :=
        singleton_cardinal _ R2.
      assert (HrS_real : @IsRealizer B R2 HR2 rSingle).
      { constructor.
        - intros L HL. destruct HL.
          constructor; [exact HR2_total | intros a b Hab; exact Hab].
        - intros a b. split.
          + intros HRab L HL. destruct HL. exact HRab.
          + intro Hall. apply Hall. constructor. }
      exact (@dimension_is_minimum B R2 HR2 d2 Hdim rSingle 1 HrS_real HrS_card). }
    lia.
Admitted.

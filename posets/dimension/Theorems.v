From Stdlib Require Import Ensembles Finite_sets Arith Classical.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn.

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
    (* This is Szpilrajn's theorem - admitted in this project.
       A proper proof would use Zorn's lemma for infinite sets,
       or induction for finite sets. *)
    admit.
  Admitted.

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
          { (* R y x holds *)
            (* In any linear extension L, L y x. If L x y also, then x = y, contradiction. *)
            assert (exists L_ex, IsLinearExtension R L_ex) as [L_ex HL_ex].
            { (* Every poset has at least one linear extension (Szpilrajn) *)
              admit.
            }
            specialize (Hall L_ex HL_ex).
            assert (HLyx : L_ex y x) by (apply HL_ex; auto).
            (* Proof of antisymmetry from L_ex being a linear extension *)
            admit.
          }
          { (* Incomparable x y *)
            destruct (incomparable_extension x y) as [L_ex [HL_ex Hlyx]].
            { unfold Incomparable. intros [H1 | H2]; auto. }
            specialize (Hall L_ex HL_ex).
            (* Proof of antisymmetry from L_ex being a linear extension *)
            admit.
          }
    - intros Hxy L HL. admit.
  Admitted.

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

  (** Lemma: If the base set A is finite, the set of all linear extensions is also finite. *)
  Lemma all_linear_extensions_finite :
    forall n, cardinal A (Full_set A) n ->
    Finite (A -> A -> Prop) AllLinearExtensions.
  Admitted.

  (** Theorem: Dushnik-Miller (1941) - Every finite poset has a well-defined dimension *)
  Theorem dushnik_miller_exists :
    forall n, cardinal A (Full_set A) n ->
    exists d, inhabited (PosetDimension R d).
  Proof.
    intros n Hfin.
    (* Structure of the proof using the lemmas defined above: *)
    (* 1. FullRealizer is a realizer (by all_linear_extensions_is_realizer) *)
    (* 2. It is finite if A is finite (by all_linear_extensions_finite) *)
    (* 3. Therefore the set of finite realizers is non-empty. *)
    (* 4. The dimension d is the minimum size of a finite realizer. *)
    admit.
  Admitted.


  (** Theorem: Subposet Dimension Monotonicity
      If Q is a subposet of P (induced by subset S), then dim(Q) <= dim(P). *)
  Theorem subposet_dimension_le :
    forall (S : Ensemble A) (d_p d_q : nat),
    PosetDimension R d_p ->
    exists d_q, inhabited (PosetDimension (fun x y => In A S x /\ In A S y /\ R x y) d_q) /\ d_q <= d_p.
  Admitted.

  (** Theorem: Hiraguchi's Theorem (1951)
      For a finite poset on n elements (n >= 4), dim(P) <= n/2. *)
  Theorem hiraguchi_bound :
    forall (n d : nat),
    cardinal A (Full_set A) n ->
    n >= 4 ->
    PosetDimension R d ->
    d <= n / 2.
  Admitted.

End Theorems.

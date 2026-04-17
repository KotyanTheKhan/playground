From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Dilworth Require Import CardinalArithmetic CardinalLemmas.

(** Generic disjoint-union cardinality, used for both L and R below *)
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

Section Hall.
  Variables L R : Type.

  (** N(S) = the union of nbrs(x) for x ∈ S *)
  Definition set_neighbors (nbrs : L -> Ensemble R) (S : Ensemble L) : Ensemble R :=
    fun y => exists x, In L S x /\ In R (nbrs x) y.

  (** Hall's condition: every S ⊆ X satisfies |S| ≤ |N(S)| *)
  Definition HallCondition (X : Ensemble L) (nbrs : L -> Ensemble R) : Prop :=
    forall S ns nn,
      Included L S X ->
      cardinal L S ns ->
      cardinal R (set_neighbors nbrs S) nn ->
      ns <= nn.

  (** Perfect matching: injective f : X → Y with f(x) ∈ nbrs(x) *)
  Definition IsPerfectMatching
      (X : Ensemble L) (Y : Ensemble R)
      (nbrs : L -> Ensemble R) (m : L -> R) : Prop :=
    (forall x, In L X x -> In R Y (m x)) /\
    (forall x, In L X x -> In R (nbrs x) (m x)) /\
    (forall x1 x2, In L X x1 -> In L X x2 -> m x1 = m x2 -> x1 = x2).

  Lemma set_neighbors_empty : forall nbrs,
    set_neighbors nbrs (Empty_set L) = Empty_set R.
  Proof.
    intros nbrs. apply Extensionality_Ensembles. intros y. split.
    - intros [x [Hx _]]. inversion Hx.
    - intro Hy. inversion Hy.
  Qed.

  Lemma set_neighbors_mono : forall nbrs S T,
    Included L S T ->
    Included R (set_neighbors nbrs S) (set_neighbors nbrs T).
  Proof.
    intros nbrs S T Hincl y [x [Hx Hy]].
    exists x. split; [exact (Hincl x Hx) | exact Hy].
  Qed.

  Lemma set_neighbors_union : forall nbrs S T,
    set_neighbors nbrs (Union L S T) =
    Union R (set_neighbors nbrs S) (set_neighbors nbrs T).
  Proof.
    intros nbrs S T. apply Extensionality_Ensembles. intros y. split.
    - intros [x [Hx Hy]]. destruct Hx as [x' Hx' | x' Hx'].
      + apply Union_introl. exists x'. split; assumption.
      + apply Union_intror. exists x'. split; assumption.
    - intros Hy. destruct Hy as [z Hz | z Hz].
      + destruct Hz as [x [Hx Hyx]].
        exists x. split; [apply Union_introl; exact Hx | exact Hyx].
      + destruct Hz as [x [Hx Hyx]].
        exists x. split; [apply Union_intror; exact Hx | exact Hyx].
  Qed.

  Lemma set_neighbors_remove_point :
      forall (nbrs : L -> Ensemble R) (S : Ensemble L) (y0 : R),
    set_neighbors (fun x z => In R (nbrs x) z /\ z <> y0) S =
    fun z => In R (set_neighbors nbrs S) z /\ z <> y0.
  Proof.
    intros nbrs S y0. apply Extensionality_Ensembles. intros z. split.
    - intros [x [Hx [Hzx Hneq]]].
      split; [exists x; split; assumption | exact Hneq].
    - intros [[x [Hx Hzx]] Hneq].
      exists x. split; [exact Hx | split; assumption].
  Qed.

  Lemma set_neighbors_remove_set :
      forall (nbrs : L -> Ensemble R) (S : Ensemble L) (T : Ensemble R),
    set_neighbors (fun x z => In R (nbrs x) z /\ ~ In R T z) S =
    fun z => In R (set_neighbors nbrs S) z /\ ~ In R T z.
  Proof.
    intros nbrs S T. apply Extensionality_Ensembles. intros z. split.
    - intros [x [Hx [Hzx Hnot]]].
      split; [exists x; split; assumption | exact Hnot].
    - intros [[x [Hx Hzx]] Hnot].
      exists x. split; [exact Hx | split; assumption].
  Qed.

  Lemma Finite_diff_set : forall (S T : Ensemble R),
    Finite R S ->
    Finite R (fun y => In R S y /\ ~ In R T y).
  Proof.
    intros S T HS.
    apply (Finite_downward_closed R S HS).
    intros x [Hx _]. exact Hx.
  Qed.

  Lemma card_remove_point_R : forall (E : Ensemble R) (x : R) n,
    In R E x ->
    cardinal R E (S n) ->
    cardinal R (fun y => In R E y /\ y <> x) n.
  Proof.
    intros. exact (cardinal_remove R E x n H H0).
  Qed.

  Lemma cardinal_disjoint_union : forall (S T : Ensemble L) n m,
    (forall x, In L S x -> ~ In L T x) ->
    cardinal L S n ->
    cardinal L T m ->
    cardinal L (Union L S T) (n + m).
  Proof.
    intros S T n m Hdisj HcardS HcardT.
    exact (cardinal_disjoint_union_gen L S T n m Hdisj HcardS HcardT).
  Qed.

  Lemma proper_subset_card_lt : forall (X T : Ensemble L) n m,
    cardinal L X n ->
    cardinal L T m ->
    Included L T X ->
    Inhabited L T ->
    T <> X ->
    m < n.
  Proof.
    intros X T n m HcardX HcardT Hincl HinhT Hneq.
    assert (Hm_le : m <= n).
    { apply (incl_card_le L T X m n HcardT HcardX Hincl). }
    destruct (Nat.eq_dec m n) as [Heqmn | Hnemn]; [| lia].
    exfalso. apply Hneq.
    apply Extensionality_Ensembles. intros x. split.
    - intro Hx. exact (Hincl x Hx).
    - intro Hx.
      apply NNPP. intro Hnotin.
      assert (Hx_notT : ~ In L T x) by exact Hnotin.
      assert (Hcard_Tx : cardinal L (Add L T x) (S m)).
      { apply card_add; assumption. }
      assert (Hincl_Tx : Included L (Add L T x) X).
      { intros z Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
        - exact (Hincl z Hz').
        - inversion Hz'. subst. exact Hx. }
      assert (Hle : S m <= n).
      { apply (incl_card_le L (Add L T x) X (S m) n Hcard_Tx HcardX Hincl_Tx). }
      lia.
  Qed.

  Lemma cardinal_singleton_L : forall (x : L), cardinal L (Singleton L x) 1.
  Proof.
    intro x. apply (cardinal_extensional_poly L (Add L (Empty_set L) x)).
    - intros z. split.
      + intro Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
        * destruct (Hz' : Empty_set L z).
        * exact Hz'.
      + intro Hz. apply Union_intror. exact Hz.
    - change 1 with (S 0). apply card_add; [apply card_empty | intro H; destruct (H : Empty_set L x)].
  Qed.

  (** Main theorem *)
  Theorem hall_marriage_theorem :
      forall (X : Ensemble L) (Y : Ensemble R) nx (nbrs : L -> Ensemble R),
    cardinal L X nx ->
    Finite R Y ->
    inhabited R ->
    (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
    HallCondition X nbrs ->
    exists m : L -> R, IsPerfectMatching X Y nbrs m.
  Proof.
    enough (Hall_ind : forall nx (X : Ensemble L) (Y : Ensemble R) (nbrs : L -> Ensemble R),
        cardinal L X nx ->
        Finite R Y ->
        inhabited R ->
        (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
        HallCondition X nbrs ->
        exists m : L -> R, IsPerfectMatching X Y nbrs m)
      by (intros X Y nx nbrs HcardX HfinY HinhR Hnbrs_Y Hhall;
          exact (Hall_ind nx X Y nbrs HcardX HfinY HinhR Hnbrs_Y Hhall)).
    refine (Fix lt_wf
      (fun nx => forall (X : Ensemble L) (Y : Ensemble R) (nbrs : L -> Ensemble R),
        cardinal L X nx ->
        Finite R Y ->
        inhabited R ->
        (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
        HallCondition X nbrs ->
        exists m : L -> R, IsPerfectMatching X Y nbrs m)
      (fun nx IH X Y nbrs Hcard_X HfinY HinhR Hnbrs_Y Hhall => _)).
    destruct nx as [| nx'].
    - (* Base case: X = ∅ *)
      inversion Hcard_X. subst.
      destruct HinhR as [r0].
      exists (fun _ => r0).
      assert (Hempty : forall x, ~ In L (Empty_set L) x).
      { intros x Hx. unfold In in Hx. inversion Hx. }
      unfold IsPerfectMatching.
      repeat split; intros; exfalso; eapply Hempty; eassumption.
    - (* Inductive case: |X| = S nx' *)
      assert (Hinhab_X : Inhabited L X).
      { inversion Hcard_X as [| X' n Hcard' x Hnotin]. subst.
        apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
      destruct (classic (exists (T : Ensemble L),
          Inhabited L T /\ T <> X /\ Included L T X /\
          exists nt nn : nat,
            cardinal L T nt /\
            cardinal R (set_neighbors nbrs T) nn /\
            nt = nn))
        as [Htight | Hntight].
      + (* ===== Tight case: some T ⊊ X has |N(T)| = |T| ===== *)
        destruct Htight as [T [HinhT [HneqT [HinclT [nt [nn [HcardT [HcardNT Heq]]]]]]]].
        subst nn.
        assert (HcardT_lt : nt < S nx').
        { apply (proper_subset_card_lt X T (S nx') nt); assumption. }
        assert (HhallT : HallCondition T nbrs).
        { intros S ns nn HinclS HcardS HcardNS.
          exact (Hhall S ns nn (fun x Hx => HinclT x (HinclS x Hx)) HcardS HcardNS). }
        assert (HnbrsT_Y : forall x y, In L T x -> In R (nbrs x) y -> In R Y y)
          by (intros x y Hx Hy; exact (Hnbrs_Y x y (HinclT x Hx) Hy)).
        destruct (IH nt HcardT_lt T Y nbrs HcardT HfinY HinhR HnbrsT_Y HhallT)
          as [mT [HmT_Y [HmT_nbrs HmT_inj]]].
        pose (NT := set_neighbors nbrs T).
        pose (X'' := fun x => In L X x /\ ~ In L T x).
        assert (HfinX : Finite L X) by exact (cardinal_finite L X (S nx') Hcard_X).
        assert (HfinX'' : Finite L X'')
          by exact (Finite_downward_closed L X HfinX X'' (fun x Hx => proj1 Hx)).
        destruct (finite_cardinal L X'' HfinX'') as [nX'' HcardX''].
        assert (HX''_lt : nX'' < S nx').
        { destruct nt as [| nt'].
          - destruct HinhT as [a Ha]. inversion HcardT. subst. inversion Ha.
          - assert (Hdisj : forall x, In L X'' x -> ~ In L T x)
              by (intros x [_ H] Hxt; exact (H Hxt)).
            assert (Hcard_union : cardinal L (Union L X'' T) (nX'' + S nt'))
              by exact (cardinal_disjoint_union X'' T nX'' (S nt') Hdisj HcardX'' HcardT).
            assert (Hle : nX'' + S nt' <= S nx').
            { apply (incl_card_le L (Union L X'' T) X (nX'' + S nt') (S nx')
                       Hcard_union Hcard_X).
              intros x Hx. inversion Hx as [z Hz | z Hz]; subst.
              - exact (proj1 Hz).
              - exact (HinclT x Hz). }
            lia. }
        pose (nbrs'' := fun x z => In R (nbrs x) z /\ ~ In R NT z).
        assert (HfinY'' : Finite R (fun z => In R Y z /\ ~ In R NT z))
          by exact (Finite_downward_closed R Y HfinY _ (fun z Hz => proj1 Hz)).
        assert (Hnbrs'' : forall x y, In L X'' x -> In R (nbrs'' x) y ->
            In R (fun z => In R Y z /\ ~ In R NT z) y).
        { intros x y [Hx _] [Hy Hnot]. exact (conj (Hnbrs_Y x y Hx Hy) Hnot). }
        (* Hall's condition for X'' with nbrs'' *)
        assert (Hhall'' : HallCondition X'' nbrs'').
        { intros S ns nn HinclS HcardS HcardNS.
          unfold nbrs'' in HcardNS. rewrite set_neighbors_remove_set in HcardNS.
          assert (HinclSX : Included L S X) by (intros z Hz; exact (proj1 (HinclS z Hz))).
          assert (HdisS_T : forall x, In L S x -> ~ In L T x)
            by (intros x Hx; exact (proj2 (HinclS x Hx))).
          assert (HinclST_X : Included L (Union L S T) X).
          { intros x Hx. inversion Hx as [z Hz | z Hz]; subst.
            - exact (HinclSX x Hz).
            - exact (HinclT x Hz). }
          assert (HcardST : cardinal L (Union L S T) (ns + nt)).
          { apply cardinal_disjoint_union; [| exact HcardS | exact HcardT].
            intros x Hx. exact (HdisS_T x Hx). }
          assert (Hfin_NST : Finite R (set_neighbors nbrs (Union L S T))).
          { apply (Finite_downward_closed R Y HfinY).
            intros y [x [Hx Hy]]. exact (Hnbrs_Y x y (HinclST_X x Hx) Hy). }
          destruct (finite_cardinal R (set_neighbors nbrs (Union L S T)) Hfin_NST)
            as [nST HcardNST].
          assert (HnST_ge : ns + nt <= nST)
            by exact (Hhall (Union L S T) (ns + nt) nST HinclST_X HcardST HcardNST).
          (* N(S ∪ T) = N(S) ∪ NT, so cardinality nST holds for the union *)
          assert (HcardNS_union : cardinal R (Union R (set_neighbors nbrs S) NT) nST).
          { unfold NT. rewrite <- (set_neighbors_union nbrs S T). exact HcardNST. }
          (* N(S) ∪ NT = (N(S) \ NT) ∪ NT  (set equality) *)
          assert (Hset_eq : Union R (set_neighbors nbrs S) NT =
                            Union R (fun z => In R (set_neighbors nbrs S) z /\ ~ In R NT z) NT).
          { apply Extensionality_Ensembles. intros z. split.
            - intro Hz. inversion Hz as [w Hw | w Hw]; subst.
              + destruct (classic (In R NT z)) as [HinNT | HnotNT].
                * apply Union_intror. exact HinNT.
                * apply Union_introl. exact (conj Hw HnotNT).
              + apply Union_intror. exact Hw.
            - intro Hz. inversion Hz as [w Hw | w Hw]; subst.
              + apply Union_introl. exact (proj1 Hw).
              + apply Union_intror. exact Hw. }
          assert (HcardNST' : cardinal R
              (Union R (fun z => In R (set_neighbors nbrs S) z /\ ~ In R NT z) NT) nST).
          { rewrite <- Hset_eq. exact HcardNS_union. }
          (* |(N(S) \ NT) ∪ NT| = nn + nt  (disjoint union) *)
          assert (HcardUnion : cardinal R
              (Union R (fun z => In R (set_neighbors nbrs S) z /\ ~ In R NT z) NT) (nn + nt)).
          { apply cardinal_disjoint_union_gen.
            - intros x [_ Hnot]. exact Hnot.
            - exact HcardNS.
            - exact HcardNT. }
          assert (Heq_nST : nST = nn + nt)
            by exact (cardinal_unicity R _ nST HcardNST' (nn + nt) HcardUnion).
          lia. }
        destruct (IH nX'' HX''_lt X'' (fun z => In R Y z /\ ~ In R NT z) nbrs''
                     HcardX'' HfinY'' HinhR Hnbrs'' Hhall'')
          as [m'' [Hm''_Y [Hm''_nbrs Hm''_inj]]].
        (* Combine: f = mT on T, f = m'' on X'' *)
        set (f := fun x => if excluded_middle_informative (In L T x) then mT x else m'' x).
        assert (Hf_T : forall x, In L T x -> f x = mT x).
        { intros x Hx. unfold f.
          destruct (excluded_middle_informative (In L T x)) as [_ | Habs].
          - reflexivity.
          - exact (False_rect _ (Habs Hx)). }
        assert (Hf_nT : forall x, ~ In L T x -> f x = m'' x).
        { intros x Hnotx. unfold f.
          destruct (excluded_middle_informative (In L T x)) as [Habs | _].
          - exact (False_rect _ (Hnotx Habs)).
          - reflexivity. }
        exists f.
        unfold IsPerfectMatching. split; [| split].
        * intros x Hx.
          destruct (classic (In L T x)) as [HxT | HxnT].
          -- rewrite (Hf_T x HxT). exact (HmT_Y x HxT).
          -- rewrite (Hf_nT x HxnT). exact (proj1 (Hm''_Y x (conj Hx HxnT))).
        * intros x Hx.
          destruct (classic (In L T x)) as [HxT | HxnT].
          -- rewrite (Hf_T x HxT). exact (HmT_nbrs x HxT).
          -- rewrite (Hf_nT x HxnT).
             destruct (Hm''_nbrs x (conj Hx HxnT)) as [Hnbr _]. exact Hnbr.
        * intros x1 x2 Hx1 Hx2 Heqf.
          destruct (classic (In L T x1)) as [HxT1 | HxnT1];
          destruct (classic (In L T x2)) as [HxT2 | HxnT2].
          -- rewrite (Hf_T x1 HxT1), (Hf_T x2 HxT2) in Heqf.
             exact (HmT_inj x1 x2 HxT1 HxT2 Heqf).
          -- rewrite (Hf_T x1 HxT1), (Hf_nT x2 HxnT2) in Heqf.
             exfalso.
             assert (HmTx1_NT : In R NT (mT x1))
               by exact (ex_intro _ x1 (conj HxT1 (HmT_nbrs x1 HxT1))).
             destruct (Hm''_nbrs x2 (conj Hx2 HxnT2)) as [_ Hm''x2_notNT].
             rewrite <- Heqf in Hm''x2_notNT. exact (Hm''x2_notNT HmTx1_NT).
          -- rewrite (Hf_nT x1 HxnT1), (Hf_T x2 HxT2) in Heqf.
             exfalso.
             assert (HmTx2_NT : In R NT (mT x2))
               by exact (ex_intro _ x2 (conj HxT2 (HmT_nbrs x2 HxT2))).
             destruct (Hm''_nbrs x1 (conj Hx1 HxnT1)) as [_ Hm''x1_notNT].
             rewrite Heqf in Hm''x1_notNT. exact (Hm''x1_notNT HmTx2_NT).
          -- rewrite (Hf_nT x1 HxnT1), (Hf_nT x2 HxnT2) in Heqf.
             exact (Hm''_inj x1 x2 (conj Hx1 HxnT1) (conj Hx2 HxnT2) Heqf).
      + (* ===== Non-tight case: every proper S ⊊ X has |N(S)| > |S| ===== *)
        assert (Hstrict : forall S ns nn,
          Inhabited L S -> S <> X -> Included L S X ->
          cardinal L S ns -> cardinal R (set_neighbors nbrs S) nn ->
          nn > ns).
        { intros S ns nn HinhS HneqS HinclS HcardS HcardNS.
          assert (Hns_le : ns <= nn) by exact (Hhall S ns nn HinclS HcardS HcardNS).
          destruct (classic (ns < nn)) as [Hlt | Hnlt]; [exact Hlt |].
          exfalso. apply Hntight.
          assert (Heq : nn = ns) by lia.
          exists S. split; [exact HinhS | split; [exact HneqS | split; [exact HinclS |]]].
          exists ns, nn. exact (conj HcardS (conj HcardNS (eq_sym Heq))). }
        destruct Hinhab_X as [x0 Hx0].
        assert (Hnbrs_ne : Inhabited R (nbrs x0)).
        { destruct (classic (Inhabited R (nbrs x0))) as [H | H]; [exact H |].
          exfalso.
          assert (HcardNx0 : cardinal R (set_neighbors nbrs (Singleton L x0)) 0).
          { apply (cardinal_extensional_poly R (Empty_set R)); [| apply card_empty].
            intros y. split.
            - intro Hy. destruct (Hy : Empty_set R y).
            - intros [z [Hz Hzy]]. destruct (Hz : Singleton L x0 z).
              exfalso. apply H. apply Inhabited_intro with y. exact Hzy. }
          assert (Hcard_x0 : cardinal L (Singleton L x0) 1)
            by exact (cardinal_singleton_L x0).
          assert (HinclSing : Included L (Singleton L x0) X).
          { intros z Hz. destruct (Hz : Singleton L x0 z). exact Hx0. }
          assert (H1le0 : 1 <= 0)
            by exact (Hhall (Singleton L x0) 1 0 HinclSing Hcard_x0 HcardNx0).
          lia. }
        destruct Hnbrs_ne as [y0 Hy0_nbrs].
        pose (X' := fun x => In L X x /\ x <> x0).
        pose (nbrs' := fun x z => In R (nbrs x) z /\ z <> y0).
        assert (HcardX' : cardinal L X' nx')
          by exact (cardinal_remove L X x0 nx' Hx0 Hcard_X).
        assert (HfinY' : Finite R (fun z => In R Y z /\ z <> y0))
          by exact (Finite_downward_closed R Y HfinY _ (fun z Hz => proj1 Hz)).
        assert (Hnbrs' : forall x y, In L X' x -> In R (nbrs' x) y ->
            In R (fun z => In R Y z /\ z <> y0) y).
        { intros x y [Hx _] [Hy Hneq]. exact (conj (Hnbrs_Y x y Hx Hy) Hneq). }
        (* Hall's condition for X' with nbrs' *)
        assert (Hhall' : HallCondition X' nbrs').
        { intros S_set ns nn HinclS HcardS HcardNS.
          unfold nbrs' in HcardNS. rewrite set_neighbors_remove_point in HcardNS.
          destruct ns as [| ns']. { lia. }
          assert (HinhS : Inhabited L S_set).
          { inversion HcardS as [| S_rest n0 Hcard0 a Ha0]; subst.
            apply Inhabited_intro with a. apply Union_intror. apply In_singleton. }
          assert (HinclSX : Included L S_set X) by (intros z Hz; exact (proj1 (HinclS z Hz))).
          assert (HneqSX : S_set <> X).
          { intro Heq. subst S_set.
            assert (HxX' : In L X' x0) by exact (HinclS x0 Hx0).
            unfold X' in HxX'. destruct HxX' as [_ Hne]. exact (Hne eq_refl). }
          assert (Hfin_NS : Finite R (set_neighbors nbrs S_set)).
          { apply (Finite_downward_closed R Y HfinY).
            intros y [x [Hx Hy]]. exact (Hnbrs_Y x y (HinclSX x Hx) Hy). }
          destruct (finite_cardinal R (set_neighbors nbrs S_set) Hfin_NS) as [nsN HcardNS_orig].
          assert (HnsN_gt : nsN > S ns')
            by exact (Hstrict S_set (S ns') nsN HinhS HneqSX HinclSX HcardS HcardNS_orig).
          destruct (classic (In R (set_neighbors nbrs S_set) y0)) as [Hy0_in | Hy0_out].
          - destruct nsN as [| nsN']. { lia. }
            assert (Hcard_diff : cardinal R (fun z => In R (set_neighbors nbrs S_set) z /\ z <> y0) nsN')
              by exact (cardinal_remove R (set_neighbors nbrs S_set) y0 nsN' Hy0_in HcardNS_orig).
            assert (Heq_nn : nn = nsN')
              by exact (cardinal_unicity R _ nn HcardNS nsN' Hcard_diff).
            lia.
          - assert (Hset_eq : (fun z => In R (set_neighbors nbrs S_set) z /\ z <> y0) = set_neighbors nbrs S_set).
            { apply Extensionality_Ensembles. intros z. split.
              - intros [Hz _]. exact Hz.
              - intro Hz. split; [exact Hz | intro Heqz; subst z; exact (Hy0_out Hz)]. }
            rewrite Hset_eq in HcardNS.
            assert (Heq_nn : nn = nsN)
              by exact (cardinal_unicity R _ nn HcardNS nsN HcardNS_orig).
            lia. }
        destruct (IH nx' (Nat.lt_succ_diag_r nx') X'
                     (fun z => In R Y z /\ z <> y0) nbrs'
                     HcardX' HfinY' HinhR Hnbrs' Hhall')
          as [m' [Hm'_Y [Hm'_nbrs Hm'_inj]]].
        set (f := fun x => if excluded_middle_informative (x = x0) then y0 else m' x).
        assert (Hf_x0 : f x0 = y0).
        { unfold f. destruct (excluded_middle_informative (x0 = x0)) as [_ | Habs].
          - reflexivity.
          - exact (False_rect _ (Habs eq_refl)). }
        assert (Hf_ne : forall x, x <> x0 -> f x = m' x).
        { intros x Hne. unfold f.
          destruct (excluded_middle_informative (x = x0)) as [Heq | _].
          - exact (False_rect _ (Hne Heq)).
          - reflexivity. }
        exists f.
        unfold IsPerfectMatching. split; [| split].
        * intros x Hx.
          destruct (classic (x = x0)) as [Heq | Hne].
          -- subst x. rewrite Hf_x0. exact (Hnbrs_Y x0 y0 Hx0 Hy0_nbrs).
          -- rewrite (Hf_ne x Hne). exact (proj1 (Hm'_Y x (conj Hx Hne))).
        * intros x Hx.
          destruct (classic (x = x0)) as [Heq | Hne].
          -- subst x. rewrite Hf_x0. exact Hy0_nbrs.
          -- rewrite (Hf_ne x Hne).
             destruct (Hm'_nbrs x (conj Hx Hne)) as [Hnbr _]. exact Hnbr.
        * intros x1 x2 Hx1 Hx2 Heqf.
          destruct (classic (x1 = x0)) as [Heq1 | Hne1];
          destruct (classic (x2 = x0)) as [Heq2 | Hne2].
          -- rewrite Heq1, Heq2. reflexivity.
          -- rewrite Heq1 in Heqf. rewrite Hf_x0, (Hf_ne x2 Hne2) in Heqf.
             exfalso. exact (proj2 (Hm'_Y x2 (conj Hx2 Hne2)) (eq_sym Heqf)).
          -- rewrite Heq2 in Heqf. rewrite Hf_x0, (Hf_ne x1 Hne1) in Heqf.
             exfalso. exact (proj2 (Hm'_Y x1 (conj Hx1 Hne1)) Heqf).
          -- rewrite (Hf_ne x1 Hne1), (Hf_ne x2 Hne2) in Heqf.
             exact (Hm'_inj x1 x2 (conj Hx1 Hne1) (conj Hx2 Hne2) Heqf).
  Qed.

End Hall.

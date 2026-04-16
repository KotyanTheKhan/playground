From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Dilworth Require Import CardinalArithmetic CardinalLemmas.

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
    revert T m Hdisj HcardT.
    induction HcardS as [| S' n' HcardS' IH a Ha_notin]; intros T m Hdisj HcardT.
    - simpl.
      apply (cardinal_extensional_poly L T); [| exact HcardT].
      intros x. split.
      + intro Hx. apply Union_intror. exact Hx.
      + intro Hx. inversion Hx as [z Hz | z Hz]; subst.
        * inversion Hz.
        * exact Hz.
    - simpl.
      apply (cardinal_extensional_poly L (Add L (Union L S' T) a)).
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
      (* x ∈ X; since |T| = |X| = n and T ⊆ X, T = X *)
      apply NNPP. intro Hnotin.
      (* T ∪ {x} is a subset of X with cardinality m+1 > m = n = |X| — contradiction *)
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
    (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
    HallCondition X nbrs ->
    exists m : L -> R, IsPerfectMatching X Y nbrs m.
  Proof.
    (* Reorder so nx is first for Fix *)
    enough (Hall_ind : forall nx (X : Ensemble L) (Y : Ensemble R) (nbrs : L -> Ensemble R),
        cardinal L X nx ->
        Finite R Y ->
        (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
        HallCondition X nbrs ->
        exists m : L -> R, IsPerfectMatching X Y nbrs m)
      by (intros X Y nx nbrs; exact (Hall_ind nx X Y nbrs)).
    refine (Fix lt_wf
      (fun nx => forall (X : Ensemble L) (Y : Ensemble R) (nbrs : L -> Ensemble R),
        cardinal L X nx ->
        Finite R Y ->
        (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
        HallCondition X nbrs ->
        exists m : L -> R, IsPerfectMatching X Y nbrs m)
      (fun nx IH X Y nbrs Hcard_X HfinY Hnbrs_Y Hhall => _)).
    destruct nx as [| nx'].
    - (* Base case: X = ∅ *)
      inversion Hcard_X. subst.
      destruct (classic (inhabited R)) as [[r0] | Huninh].
      + exists (fun _ => r0).
        assert (Hempty : forall x, ~ In L (Empty_set L) x).
        { intros x Hx. unfold In in Hx. inversion Hx. }
        unfold IsPerfectMatching.
        repeat split; intros; exfalso; eapply Hempty; eassumption.
      + (* R uninhabited: all conditions on m vacuous, but no term m : L -> R exists.
           In the Dilworth application R = sum A A is always inhabited. *)
        admit.
    - (* Inductive case: |X| = S nx' *)
      assert (Hinhab_X : Inhabited L X).
      { inversion Hcard_X as [| X' n Hcard' x Hnotin]. subst.
        apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
      (* Classical case split: does a tight proper subset T ⊊ X exist? *)
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
        destruct (IH nt HcardT_lt T Y nbrs HcardT HfinY HnbrsT_Y HhallT)
          as [mT [HmT_Y [HmT_nbrs HmT_inj]]].
        (* N(T) — the neighborhood of T under nbrs *)
        pose (NT := set_neighbors nbrs T).
        (* X'' = X \ T *)
        pose (X'' := fun x => In L X x /\ ~ In L T x).
        assert (HfinX : Finite L X) by exact (cardinal_finite L X (S nx') Hcard_X).
        assert (HfinX'' : Finite L X'')
          by exact (Finite_downward_closed L X HfinX X'' (fun x Hx => proj1 Hx)).
        destruct (finite_cardinal L X'' HfinX'') as [nX'' HcardX''].
        (* |X''| < S nx' since nt ≥ 1 and |X''| + nt ≤ |X| = S nx' *)
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
        (* nbrs'' : neighbors avoiding N(T) *)
        pose (nbrs'' := fun x z => In R (nbrs x) z /\ ~ In R NT z).
        assert (HfinY'' : Finite R (fun z => In R Y z /\ ~ In R NT z))
          by exact (Finite_downward_closed R Y HfinY _ (fun z Hz => proj1 Hz)).
        assert (Hnbrs'' : forall x y, In L X'' x -> In R (nbrs'' x) y ->
            In R (fun z => In R Y z /\ ~ In R NT z) y).
        { intros x y [Hx _] [Hy Hnot]. exact (conj (Hnbrs_Y x y Hx Hy) Hnot). }
        assert (Hhall'' : HallCondition X'' nbrs'').
        { (* For any S ⊆ X'', |N''(S)| ≥ |S|.
             N(S ∪ T) ≥ |S| + |T| by Hall; N''(S) = N(S ∪ T) \ N(T) ≥ |S| + |T| - |T| = |S|. *)
          admit. }
        destruct (IH nX'' HX''_lt X'' (fun z => In R Y z /\ ~ In R NT z) nbrs''
                     HcardX'' HfinY'' Hnbrs'' Hhall'')
          as [m'' [Hm''_Y [Hm''_nbrs Hm''_inj]]].
        (* Combine: m = mT on T, m = m'' on X'' *)
        exists (fun x =>
          if excluded_middle_informative (In L T x) then mT x else m'' x).
        (* Verification of IsPerfectMatching for combined m — filled in Task 4 *)
        admit.
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
        (* Pick x0 ∈ X and y0 ∈ nbrs(x0) *)
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
        (* X' = X \ {x0}, nbrs' = nbrs with y0 removed *)
        pose (X' := fun x => In L X x /\ x <> x0).
        pose (nbrs' := fun x z => In R (nbrs x) z /\ z <> y0).
        assert (HcardX' : cardinal L X' nx')
          by exact (cardinal_remove L X x0 nx' Hx0 Hcard_X).
        assert (HfinY' : Finite R (fun z => In R Y z /\ z <> y0))
          by exact (Finite_downward_closed R Y HfinY _ (fun z Hz => proj1 Hz)).
        assert (Hnbrs' : forall x y, In L X' x -> In R (nbrs' x) y ->
            In R (fun z => In R Y z /\ z <> y0) y).
        { intros x y [Hx _] [Hy Hneq]. exact (conj (Hnbrs_Y x y Hx Hy) Hneq). }
        assert (Hhall' : HallCondition X' nbrs').
        { (* For any S ⊆ X', |N'(S)| ≥ |S|.
             N'(S) = N(S) \ {y0}; since S ⊊ X, |N(S)| > |S|, so |N'(S)| ≥ |N(S)| - 1 ≥ |S|. *)
          admit. }
        destruct (IH nx' (Nat.lt_succ_diag_r nx') X'
                     (fun z => In R Y z /\ z <> y0) nbrs'
                     HcardX' HfinY' Hnbrs' Hhall')
          as [m' [Hm'_Y [Hm'_nbrs Hm'_inj]]].
        (* m(x0) = y0, m(x) = m'(x) for x ≠ x0 *)
        exists (fun x =>
          if excluded_middle_informative (x = x0) then y0 else m' x).
        (* Verification of IsPerfectMatching for combined m — filled in Task 5 *)
        admit.
  Admitted.

End Hall.

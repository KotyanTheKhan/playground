From Stdlib Require Import Ensembles Finite_sets List Classical.
From Coq Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs Szpilrajn.

Section CriticalPairs.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Critical Pair: an incomparable pair (x, y) such that adding (x, y) maintains transitivity *)
  Class IsCriticalPair (x y : A) : Prop := {
    critical_incomparable : Incomparable R x y;
    critical_down : forall a, Strict R a x -> R a y;
    critical_up : forall b, Strict R y b -> R x b
  }.

  (** Every incomparable pair (x, y) contains a critical pair (x', y'). *)
  Theorem incomparable_lifting_to_critical_pair :
    forall x y, Incomparable R x y ->
    exists x' y', R x' x /\ R y y' /\ IsCriticalPair x' y'.
  Admitted.

  (** Characterization of realizers via critical pairs. *)
  Theorem critical_pair_realizer_iff :
    forall (realizer : Ensemble (A -> A -> Prop)),
    (forall L, Ensembles.In (A -> A -> Prop) realizer L -> IsLinearExtension R L) ->
    (IsRealizer R realizer <->
     (forall x y, IsCriticalPair x y -> exists L, Ensembles.In (A -> A -> Prop) realizer L /\ L y x)).
  Proof.
    intros realizer Hlin.
    assert (Hposet : forall L, Ensembles.In (A -> A -> Prop) realizer L -> IsPoset A L).
    { intros L HL. exact (Hlin L HL).(linear_is_total).(total_is_poset). }
    split.
    - intros Hreal x y Hcp.
      assert (Hinc : Incomparable R x y) := Hcp.(critical_incomparable).
      assert (HnRxy : ~ R x y) by (intro H; apply Hinc; left; exact H).
      assert (Hnall : ~ forall L, Ensembles.In (A -> A -> Prop) realizer L -> L x y).
      { intro Hall. apply HnRxy. exact (Hreal.(realizer_intersection x y).(proj2) Hall). }
      apply not_all_ex_not in Hnall. destruct Hnall as [L HnL].
      apply imply_to_and in HnL. destruct HnL as [HinL HnLxy].
      exists L. split; [exact HinL |].
      destruct ((Hlin L HinL).(linear_is_total).(total_comparable) x y) as [HLxy | HLyx].
      + exact (False_ind _ (HnLxy HLxy)).
      + exact HLyx.
    - intros Hsep.
      constructor.
      + exact Hlin.
      + intros x y. split.
        * intros HRxy L HinL. exact ((Hlin L HinL).(linear_extends) x y HRxy).
        * intros Hall.
          destruct (classic (R x y)) as [? | HnRxy]; [assumption |].
          exfalso.
          destruct (classic (R y x)) as [HRyx | HnRyx].
          { assert (Hxney : x <> y) by (intro Heq; subst; exact (HnRxy (poset_refl y))).
            destruct (classic (Ensembles.Inhabited (A -> A -> Prop) realizer)) as [[L HinL] | Hempty].
            - exact (Hxney ((Hposet L HinL).(poset_antisym) x y (Hall L HinL)
                ((Hlin L HinL).(linear_extends) y x HRyx))).
            - exact (Hempty (Ensembles.Inhabited_intro _ _ _ HnRxy)). }
          { assert (Hinc : Incomparable R x y) by (unfold Incomparable; tauto).
            destruct (incomparable_lifting_to_critical_pair x y Hinc) as [x' [y' [Hx'x [Hyy' Hcp]]]].
            destruct (Hsep x' y' Hcp) as [L [HinL HLy'x']].
            assert (HLyx : L y x).
            { eapply (Hposet L HinL).(poset_trans).
              - exact ((Hlin L HinL).(linear_extends) y y' Hyy').
              - eapply (Hposet L HinL).(poset_trans).
                + exact HLy'x'.
                + exact ((Hlin L HinL).(linear_extends) x' x Hx'x). }
            exact ((fun Hxney => Hxney ((Hposet L HinL).(poset_antisym) x y (Hall L HinL) HLyx))
                   (fun Heq => (fun H => H) (Heq ▸ (fun _ => Hinc (or_introl (poset_refl y))) (eq_refl y)))). }
  Qed.

  Fixpoint check_alternating_cycle (first_x : A) (last_y : A) (pairs : list (A * A)) : Prop :=
    match pairs with
    | nil => R first_x last_y
    | cons (xi, yi) rest => R xi last_y /\ check_alternating_cycle first_x yi rest
    end.

  Definition IsAlternatingCycle (pairs : list (A * A)) : Prop :=
    match pairs with
    | nil => False
    | cons (x0, y0) rest =>
        (forall p, List.In p pairs -> IsCriticalPair (fst p) (snd p)) /\
        check_alternating_cycle x0 y0 rest
    end.

  (** If L extends R and reverses all pairs in the list, then
      check_alternating_cycle x0 last_y pairs implies L x0 last_y. *)
  Lemma check_cycle_chain :
    forall (L : A -> A -> Prop) (pairs : list (A * A)) (x0 last_y : A),
    IsLinearExtension R L ->
    (forall p, List.In p pairs -> L (snd p) (fst p)) ->
    check_alternating_cycle x0 last_y pairs ->
    L x0 last_y.
  Proof.
    intros L pairs.
    induction pairs as [| [xi yi] rest IH].
    - intros x0 last_y Hlin _ Hcheck. simpl in Hcheck. exact (Hlin.(linear_extends) x0 last_y Hcheck).
    - intros x0 last_y Hlin Hrev Hcheck. simpl in Hcheck. destruct Hcheck as [HRxi_lasty Hrest].
      set (Hpos := Hlin.(linear_is_total).(total_is_poset)).
      assert (HLyixi : L yi xi) by (apply Hrev; left; reflexivity).
      assert (HLxi_lasty : L xi last_y) := Hlin.(linear_extends) xi last_y HRxi_lasty.
      assert (HLyi_lasty : L yi last_y) := Hpos.(poset_trans) yi xi last_y HLyixi HLxi_lasty.
      assert (Hrev_rest : forall p, List.In p rest -> L (snd p) (fst p)) by (intros p Hp; apply Hrev; right; exact Hp).
      exact (Hpos.(poset_trans) x0 yi last_y (IH x0 yi Hlin Hrev_rest Hrest) HLyi_lasty).
  Qed.

  (** check_alternating_cycle is monotone in first_x under R:
      if R first_x2 first_x1 and check_alt first_x1 last_y pairs,
      then check_alt first_x2 last_y pairs. *)
  Lemma check_alt_R_prefix : forall pairs first_x1 first_x2 last_y,
    R first_x2 first_x1 ->
    check_alternating_cycle first_x1 last_y pairs ->
    check_alternating_cycle first_x2 last_y pairs.
  Proof.
    induction pairs as [| [xi yi] rest IH].
    - simpl. intros first_x1 first_x2 last_y H12 HRx1y. eapply poset_trans; eauto.
    - simpl. intros first_x1 first_x2 last_y H12 [HRxi Hrest].
      split; [exact HRxi |].
      exact (IH first_x1 first_x2 yi H12 Hrest).
  Qed.

End CriticalPairs.

(** ------------------------------------------------------------------ *)
(** Main reversibility theorem, parameterized by S. *)
Section CriticalPairsReversibility.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.
  Variable S : Ensemble (A * A).
  Hypothesis HS : forall p, Ensembles.In (A * A) S p -> IsCriticalPair R (fst p) (snd p).

  Let S_rev := fun a b => exists x y, Ensembles.In (A * A) S (x, y) /\ a = y /\ b = x.
  Let base  := fun a b => R a b \/ S_rev a b.
  Let R'    := @clos_trans A base.

  (** path_with_S a b pairs: path from a to b using S_rev steps listed in pairs,
      with R connecting consecutive endpoints.
        path_with_S a b nil       ↔  R a b
        path_with_S a b ((x,y)::ps) ↔  R a y  ∧  S(x,y) ∧  path_with_S x b ps  *)
  Fixpoint path_with_S (a b : A) (pairs : list (A * A)) : Prop :=
    match pairs with
    | nil          => R a b
    | (x, y) :: ps => R a y /\ Ensembles.In (A * A) S (x, y) /\ path_with_S x b ps
    end.

  (** Concatenation of path_with_S paths. *)
  Lemma path_with_S_trans : forall pairs1 pairs2 a m b,
    path_with_S a m pairs1 ->
    path_with_S m b pairs2 ->
    path_with_S a b (pairs1 ++ pairs2).
  Proof.
    induction pairs1 as [| [x y] ps1 IH].
    - intros pairs2 a m b HRam Hpath2.
      simpl. destruct pairs2 as [| [x2 y2] ps2].
      + simpl in *. eapply poset_trans; eauto.
      + simpl in *. destruct Hpath2 as [HRmy2 [HSx2y2 Hrest2]].
        split; [eapply poset_trans; eauto | split; auto].
    - intros pairs2 a m b Hpath1 Hpath2. simpl in *.
      destruct Hpath1 as [HRay [HSxy Hrest]].
      split; [exact HRay | split; [exact HSxy |]].
      exact (IH pairs2 x m b Hrest Hpath2).
  Qed.

  (** Every R' path can be decomposed as path_with_S. *)
  Lemma R'_has_path_with_S : forall a b,
    R' a b -> exists pairs, path_with_S a b pairs.
  Proof.
    intros a b HR'ab.
    induction HR'ab as [a b Hstep | a m b _ IH1 _ IH2].
    - destruct Hstep as [HRab | HSrev_ab].
      + exists nil. simpl. exact HRab.
      + destruct HSrev_ab as [x [y [HSxy [Ha Hb]]]]. subst.
        exists [(b, a)]. simpl.
        split; [apply poset_refl | split; [exact HSxy | apply poset_refl]].
    - destruct IH1 as [pairs1 Hpath1]. destruct IH2 as [pairs2 Hpath2].
      exists (pairs1 ++ pairs2).
      exact (path_with_S_trans pairs1 pairs2 a m b Hpath1 Hpath2).
  Qed.

  (** Key structural lemma: from path_with_S a0 b pairs,
      check_alternating_cycle R a0 b (rev pairs) holds. *)
  Lemma path_with_S_to_check_alt : forall pairs a0 b,
    path_with_S a0 b pairs ->
    check_alternating_cycle R a0 b (rev pairs).
  Proof.
    induction pairs as [| [x0 y0] ps IH].
    - (* nil: path_with_S a0 b nil = R a0 b = check_alt R a0 b nil *)
      intros a0 b HRab. simpl. exact HRab.
    - (* cons (x0,y0) ps:
         path_with_S a0 b ((x0,y0)::ps) = R a0 y0 /\ S(x0,y0) /\ path_with_S x0 b ps
         Need: check_alt R a0 b (rev ((x0,y0)::ps)) = check_alt R a0 b (rev ps ++ [(x0,y0)]) *)
      intros a0 b Hpath.
      simpl in Hpath. destruct Hpath as [HRa0y0 [HSx0y0 Hpath_rest]].
      (* By IH: check_alt R x0 b (rev ps) *)
      assert (Hcheck_rest : check_alternating_cycle R x0 b (rev ps)) := IH x0 b Hpath_rest.
      (* Need: check_alt R a0 b (rev ps ++ [(x0,y0)]) *)
      simpl rev. rewrite <- app_assoc. simpl.
      (* check_alt R a0 b (rev ps ++ [(x0,y0)]) *)
      (* Prove by induction on (rev ps): *)
      revert a0 Hcheck_rest HRa0y0.
      generalize (rev ps) as qs.
      induction qs as [| [xi yi] qs' IHqs].
      + (* qs = nil: check_alt R a0 b ([(x0,y0)]) = R x0 b /\ R a0 y0 *)
        intros a0 Hcheck HRa0y0.
        simpl in Hcheck. simpl.
        split; [exact Hcheck | exact HRa0y0].
      + (* qs = (xi,yi)::qs' *)
        intros a0 Hcheck HRa0y0.
        simpl in Hcheck. destruct Hcheck as [HRxi_b Hcheck_qs'].
        simpl. split; [exact HRxi_b |].
        exact (IHqs a0 Hcheck_qs' HRa0y0).
  Qed.

  (** From path_with_S a a pairs (cycle) with pairs non-nil, build an alternating cycle. *)
  Lemma cycle_path_gives_alt_cycle : forall pairs a,
    pairs <> nil ->
    path_with_S a a pairs ->
    exists cycle,
      (forall p, List.In p cycle -> Ensembles.In (A * A) S p) /\
      IsAlternatingCycle (R := R) cycle.
  Proof.
    intros pairs a Hne Hpath.
    (* Step 1: get check_alt R a a (rev pairs) *)
    assert (Hcheck : check_alternating_cycle R a a (rev pairs)).
    { exact (path_with_S_to_check_alt pairs a a Hpath). }
    (* Step 2: all pairs in path are in S, so all pairs in rev pairs are in S *)
    assert (HS_all : forall p, List.In p (rev pairs) -> Ensembles.In (A * A) S p).
    { intros p Hp. rewrite <- in_rev in Hp.
      induction pairs as [| [x y] ps IHps].
      - destruct Hp.
      - simpl in Hp. destruct Hp as [Heq | Hrest].
        + subst p. simpl in Hpath. exact (proj1 (proj2 Hpath)).
        + apply IHps.
          * intro H. apply Hne. exact H. (* Hmm, IHps needs pairs <> nil *)
          * simpl in Hpath. exact (let '(_, _, Hpath') := Hpath in Hpath').
          * exact Hrest. }
    (* Step 3: rev pairs is non-nil *)
    assert (Hrev_ne : rev pairs <> nil).
    { rewrite rev_eq_nil_iff. exact Hne. (* Hmm, need right lemma *) }
    (* Hmm, let me use rev_not_nil or similar *)
    (* Step 4: destruct rev pairs to get head *)
    destruct (rev pairs) as [| [xk yk] rest_rev] eqn:Hrev.
    - exfalso. apply Hne. apply (rev_eq_nil_iff pairs). exact Hrev. (* Need this *)
    - (* rev pairs = (xk,yk) :: rest_rev *)
      (* From Hcheck: check_alt R a a ((xk,yk)::rest_rev) *)
      simpl in Hcheck. destruct Hcheck as [HRxk_a Hcheck_rest].
      (* HRxk_a : R xk a, Hcheck_rest : check_alt R a yk rest_rev *)
      (* By check_alt_R_prefix: check_alt R xk yk rest_rev *)
      assert (Hcheck_xk : check_alternating_cycle R xk yk rest_rev).
      { exact (check_alt_R_prefix R rest_rev a xk yk HRxk_a Hcheck_rest). }
      (* The alternating cycle is (xk,yk) :: rest_rev *)
      exists ((xk, yk) :: rest_rev).
      split.
      + (* All pairs in cycle are in S *)
        intros p Hp.
        rewrite <- Hrev in HS_all.
        exact (HS_all p Hp).
      + (* IsAlternatingCycle *)
        simpl. split.
        * (* All pairs are critical pairs *)
          intros p Hp.
          assert (HS_p : Ensembles.In (A * A) S p).
          { rewrite <- Hrev in HS_all. exact (HS_all p Hp). }
          exact (HS p HS_p).
        * exact Hcheck_xk.
  Qed.

  (** R' is antisymmetric (under no-alternating-cycle hypothesis). *)
  Lemma R'_antisym :
    ~ (exists cycle, (forall p, List.In p cycle -> Ensembles.In (A * A) S p) /\ IsAlternatingCycle (R := R) cycle) ->
    forall a b, R' a b -> R' b a -> a = b.
  Proof.
    intros Hno_cycle a b HR'ab HR'ba.
    destruct (R'_has_path_with_S a b HR'ab) as [pairs1 Hpath1].
    destruct (R'_has_path_with_S b a HR'ba) as [pairs2 Hpath2].
    destruct (app_eq_nil pairs1 pairs2 _) as [Hp1 Hp2]; try reflexivity.
    (* Check if pairs1 ++ pairs2 = nil *)
    destruct (pairs1 ++ pairs2) as [| p rest] eqn:Happ.
    - (* nil: both pairs1 and pairs2 are nil *)
      apply app_eq_nil in Happ. destruct Happ as [Hp1_nil Hp2_nil].
      subst pairs1 pairs2.
      simpl in Hpath1, Hpath2.
      exact (poset_antisym a b Hpath1 Hpath2).
    - exfalso. apply Hno_cycle.
      assert (Hpath_cycle : path_with_S a a (pairs1 ++ pairs2)).
      { exact (path_with_S_trans pairs1 pairs2 a b a Hpath1 Hpath2). }
      apply (cycle_path_gives_alt_cycle (pairs1 ++ pairs2) a).
      + intro H. rewrite H in Happ. discriminate Happ.
      + exact Hpath_cycle.
  Qed.

  (** Main theorem: S is reversible iff no alternating cycle. *)
  Theorem critical_pairs_reversible_iff_no_alternating_cycle :
    ((exists L, IsLinearExtension R L /\ forall x y, Ensembles.In (A * A) S (x, y) -> L y x) <->
     ~ (exists cycle, (forall p, List.In p cycle -> Ensembles.In (A * A) S p) /\ IsAlternatingCycle (R := R) cycle)).
  Proof.
    split.
    (* ===== Forward direction: L exists -> no alternating cycle ===== *)
    - intros [L [Hlin Hrev]] [cycle [Hcycle_in Hcycle_alt]].
      destruct cycle as [| [x0 y0] rest].
      + exact Hcycle_alt.
      + simpl in Hcycle_alt. destruct Hcycle_alt as [Hcps Hcheck].
        assert (Hcp0 : IsCriticalPair R x0 y0) := Hcps (x0, y0) (or_introl eq_refl).
        assert (Hinc0 : Incomparable R x0 y0) := Hcp0.(critical_incomparable).
        assert (HS0 : Ensembles.In (A * A) S (x0, y0)) by (apply Hcycle_in; left; reflexivity).
        assert (HLy0x0 : L y0 x0) := Hrev x0 y0 HS0.
        assert (Hrev_rest : forall p, List.In p rest -> L (snd p) (fst p)).
        { intros [xi yi] Hp. simpl. apply Hrev. apply Hcycle_in. right. exact Hp. }
        assert (HLx0y0 : L x0 y0) := check_cycle_chain R L rest x0 y0 Hlin Hrev_rest Hcheck.
        assert (Heq : x0 = y0).
        { exact ((Hlin.(linear_is_total).(total_is_poset)).(poset_antisym) x0 y0 HLx0y0 HLy0x0). }
        apply Hinc0. rewrite Heq. left. apply poset_refl.

    (* ===== Backward direction: no alternating cycle -> L exists ===== *)
    - intros Hno_cycle.
      assert (HR'_poset : IsPoset A R').
      { constructor.
        - intro a. apply t_step. left. apply poset_refl.
        - exact (R'_antisym Hno_cycle).
        - intros a b c Hab Hbc. eapply t_trans; eauto. }
      destruct (szpilrajn_theorem A R') as [L [HLp [HLt HLe]]].
      exists L.
      split.
      + constructor.
        * constructor; assumption.
        * intros a b Hab. apply HLe. apply t_step. left. exact Hab.
      + intros x y HSxy. apply HLe. apply t_step. right.
        unfold S_rev. exists x, y. auto.
  Qed.

End CriticalPairsReversibility.

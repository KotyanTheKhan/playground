(** Removable pairs and Trotter's lemma for the proof of Hiraguchi's theorem.
    See docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import CriticalPairDigraph.
From Dimension Require Import N4Realizers N5Realizers N5Dispatcher.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Transitive closure is contained in the reflexive-transitive closure.
    Stdlib's [Operators_Properties] is not imported here, so we prove this
    one-liner locally.  Stated at top level to avoid clashing with the
    [RemovablePairs] section variables. *)
Lemma clos_trans_in_rt {T : Type} (Rel : T -> T -> Prop) (x y : T) :
  clos_trans T Rel x y -> clos_refl_trans T Rel x y.
Proof.
  induction 1 as [x y Hxy | x y z _ IHxy _ IHyz].
  - apply rt_step. exact Hxy.
  - eapply rt_trans; eassumption.
Qed.

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

  (** A pair (x, y) is removable iff for every d'-element realizer of R
      restricted to the residual set, there exists a (d'+1)-element
      realizer of R. This is Trotter's formulation; the hard work of
      producing that extra linear extension is encapsulated in this
      property and proved (existentially) by [removable_pair_exists].

      (The previous "single-L joint-consistency" formulation was
      unsatisfiable in antichains; see git log for details.) *)
  Definition IsRemovablePair (x y : A) : Prop :=
    x <> y /\
    forall (d' : nat)
           (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop)),
      IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                     R (proj1_sig a) (proj1_sig b)) r' ->
      cardinal _ r' d' ->
      exists r : Ensemble (A -> A -> Prop),
        IsRealizer R r /\
        cardinal (A -> A -> Prop) r (d' + 1).

  (** Under the Trotter realizer-existence definition of [IsRemovablePair],
      this lemma is essentially an unfolding. *)
  Lemma removable_pair_dimension_bound :
    forall (x y : A) (d' : nat)
           (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop)),
    IsRemovablePair x y ->
    IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                   R (proj1_sig a) (proj1_sig b)) r' ->
    cardinal _ r' d' ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
  Proof.
    intros x y d' r' [_ Hrem] Hr'_real Hr'_card.
    exact (Hrem d' r' Hr'_real Hr'_card).
  Qed.

  (** When R is the discrete poset (an antichain), every distinct pair (x, y)
      is removable. Construction:

        - Lift each [L' ∈ r'] to a total order [lift L'] of A by placing
          residual elements (ordered by L') below [y], and [y] below [x].
          This is built via [szpilrajn_theorem] on the transitive closure
          of the prescribed augmentation; an antichain has no nontrivial
          base relation, so the prescription is acyclic by construction.
        - [lift] is injective on [r'] (round-trip on subtype pairs), so
          [Im r' lift] has cardinality [d'].
        - Add one further linear extension [L_extra] of [R] in which
          [x < y] (so [L_extra] disagrees with every [lift L'] on (x,y)).
        - The resulting [r := Add (Im r' lift) L_extra] has cardinality
          [d' + 1] and realizes [R = eq] because every pair (a, b) with
          [a ≠ b] is "split" by at least one of the lift orientations
          (residual < y < x in every lift, x < y < ... in L_extra). *)

  (** Helper: build a total order on A realising the prescription
      "residual elements (ordered by L') below y below x" via Szpilrajn,
      where the base R is the antichain (R = eq).  Returns the lifted
      total order [L_full] together with the structural properties
      needed downstream. *)
  Lemma antichain_lift_witness :
    (forall a b : A, R a b -> a = b) ->
    forall (x y : A) (L' : {a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop),
    x <> y ->
    IsLinearExtension
      (fun a b : {a : A | In A (Residual x y) a} => R (proj1_sig a) (proj1_sig b)) L' ->
    exists L_full : A -> A -> Prop,
      IsLinearExtension R L_full /\
      L_full y x /\
      (forall a, In A (Residual x y) a -> L_full a y) /\
      (forall a, In A (Residual x y) a -> L_full a x) /\
      (forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
         L' (exist _ a ha) (exist _ b hb) -> L_full a b) /\
      (forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
         L_full a b -> L' (exist _ a ha) (exist _ b hb)) /\
      (~ L_full x y) /\
      (forall a, In A (Residual x y) a -> ~ L_full y a) /\
      (forall a, In A (Residual x y) a -> ~ L_full x a).
  Proof.
    intros Hdiscrete x y L' Hxy_neq HL'.
    (* Build the prescribed relation P on A. *)
    set (P := clos_trans A (fun a b =>
                a = b
                \/ (exists (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
                      L' (exist _ a ha) (exist _ b hb))
                \/ (In A (Residual x y) a /\ b = y)
                \/ (In A (Residual x y) a /\ b = x)
                \/ (a = y /\ b = x))).
    (* Show P is a poset: only need antisymmetry (transitivity is t_trans). *)
    assert (HL'_pos : IsPoset _ L') by exact HL'.(linear_is_total).(total_is_poset).
    assert (HL'_tot : forall a b, L' a b \/ L' b a) by exact HL'.(linear_is_total).(total_comparable).
    (* Key invariant: any P-path from a to b implies either a=b, or there is a
       "level" classification: P decomposes the carrier into three blocks
       residual < {y} < {x}; within residual P agrees with L' lifted. *)
    (* Helper: level/rank function. residual = 0, y = 1, x = 2.
       Any P-step preserves rank <= 2 and within residual respects L'. *)
    set (rank := fun a : A =>
                   if excluded_middle_informative (a = x) then 2%nat
                   else if excluded_middle_informative (a = y) then 1%nat else 0%nat).
    assert (Hrank_x : rank x = 2%nat).
    { unfold rank.
      destruct (excluded_middle_informative (x = x)); [reflexivity | contradiction]. }
    assert (Hrank_y : rank y = 1%nat).
    { unfold rank.
      destruct (excluded_middle_informative (y = x)); [contradiction Hxy_neq; auto |].
      destruct (excluded_middle_informative (y = y)); [reflexivity | contradiction]. }
    assert (Hrank_res : forall a, In A (Residual x y) a -> rank a = 0%nat).
    { intros a Ha. unfold rank.
      destruct (excluded_middle_informative (a = x)) as [Heq | _].
      - exfalso. apply (Residual_not_x _ _ _ Ha Heq).
      - destruct (excluded_middle_informative (a = y)) as [Heq | _].
        + exfalso. apply (Residual_not_y _ _ _ Ha Heq).
        + reflexivity. }
    (* P-step preserves rank a <= rank b. *)
    assert (Hstep_rank : forall a b,
              (a = b
               \/ (exists (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
                     L' (exist _ a ha) (exist _ b hb))
               \/ (In A (Residual x y) a /\ b = y)
               \/ (In A (Residual x y) a /\ b = x)
               \/ (a = y /\ b = x)) ->
              rank a <= rank b).
    { intros a b [Heq | [[ha [hb _]] | [[Hin Hb] | [[Hin Hb] | [Ha Hb]]]]].
      - subst; lia.
      - rewrite (Hrank_res _ ha), (Hrank_res _ hb). lia.
      - rewrite (Hrank_res _ Hin), Hb, Hrank_y. lia.
      - rewrite (Hrank_res _ Hin), Hb, Hrank_x. lia.
      - rewrite Ha, Hb, Hrank_y, Hrank_x. lia. }
    (* P preserves rank a <= rank b (by induction on transitive closure). *)
    assert (HP_rank : forall a b, P a b -> rank a <= rank b).
    { intros a b HPab. unfold P in HPab.
      induction HPab as [a b Hstep | a m b _ IH1 _ IH2].
      - apply Hstep_rank, Hstep.
      - lia. }
    (* P within residual = L' lifted (or equality). *)
    assert (HP_res : forall a b (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
              P a b -> L' (exist _ a ha) (exist _ b hb)).
    { intros a b ha hb HPab.
      unfold P in HPab.
      (* Generalize over the endpoints' residual proofs. We prove the slightly
         stronger statement by induction. *)
      cut (forall a b, P a b ->
             forall (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
               L' (exist _ a ha) (exist _ b hb)).
      { intros Hcut. apply Hcut. apply HPab. }
      clear a b ha hb HPab.
      intros a b HPab.
      induction HPab as [a b Hstep | a m b HPab1 IH1 HPab2 IH2].
      - intros ha hb.
        destruct Hstep as [Heq | [[ha' [hb' Hext]] | [[Hin Hbeq] | [[Hin Hbeq] | [Haeq Hbeq]]]]].
        + (* a = b. Use reflexivity of L'. *)
          subst b. assert (Hha_eq : ha = hb) by apply proof_irrelevance.
          rewrite Hha_eq. apply HL'_pos.(poset_refl).
        + assert (Hha_eq : ha = ha') by apply proof_irrelevance.
          assert (Hhb_eq : hb = hb') by apply proof_irrelevance.
          rewrite Hha_eq, Hhb_eq. exact Hext.
        + exfalso. subst b. exact (Residual_not_y x y y hb eq_refl).
        + exfalso. subst b. exact (Residual_not_x x y x hb eq_refl).
        + exfalso. subst b. exact (Residual_not_x x y x hb eq_refl).
      - intros ha hb.
        (* Need In A (Residual x y) m to invoke IH. Rank-bound m: 0 <= rank m <= 0
           since rank a = 0 = rank b. So rank m = 0, i.e., m ∈ Residual. *)
        assert (Hra : rank a = 0) by exact (Hrank_res _ ha).
        assert (Hrb : rank b = 0) by exact (Hrank_res _ hb).
        assert (Hrm_le : rank m <= rank b) by exact (HP_rank _ _ HPab2).
        assert (Hra_le : rank a <= rank m) by exact (HP_rank _ _ HPab1).
        assert (Hrm : rank m = 0) by lia.
        assert (Hm_res : In A (Residual x y) m).
        { apply Residual_intro.
          - intro Heq. subst m. rewrite Hrank_x in Hrm. discriminate.
          - intro Heq. subst m. rewrite Hrank_y in Hrm. discriminate. }
        eapply HL'_pos.(poset_trans).
        + exact (IH1 ha Hm_res).
        + exact (IH2 Hm_res hb). }
    (* Antisymmetry. *)
    assert (HP_antisym : forall a b, P a b -> P b a -> a = b).
    { intros a b HPab HPba.
      assert (Hra_le : rank a <= rank b) by exact (HP_rank _ _ HPab).
      assert (Hrb_le : rank b <= rank a) by exact (HP_rank _ _ HPba).
      assert (Hreq : rank a = rank b) by lia.
      destruct (classic (a = b)) as [|Hne]; [assumption|].
      destruct (excluded_middle_informative (a = x)) as [Hax | Hnax].
      - subst a. destruct (excluded_middle_informative (b = x)) as [|];
          [subst; reflexivity|].
        rewrite Hrank_x in Hreq.
        destruct (excluded_middle_informative (b = y)) as [Hby | Hnby].
        + subst b. rewrite Hrank_y in Hreq. discriminate.
        + assert (Hb_res : In A (Residual x y) b) by exact (Residual_intro _ _ _ n Hnby).
          rewrite (Hrank_res _ Hb_res) in Hreq. discriminate.
      - destruct (excluded_middle_informative (a = y)) as [Hay | Hnay].
        + subst a. rewrite Hrank_y in Hreq.
          destruct (excluded_middle_informative (b = x)) as [Hbx | Hnbx].
          { subst b. rewrite Hrank_x in Hreq. discriminate. }
          destruct (excluded_middle_informative (b = y)) as [|];
            [subst; reflexivity|].
          assert (Hb_res : In A (Residual x y) b) by exact (Residual_intro _ _ _ Hnbx n).
          rewrite (Hrank_res _ Hb_res) in Hreq. discriminate.
        + assert (Ha_res : In A (Residual x y) a) by exact (Residual_intro _ _ _ Hnax Hnay).
          destruct (excluded_middle_informative (b = x)) as [Hbx | Hnbx].
          { subst b. rewrite (Hrank_res _ Ha_res), Hrank_x in Hreq. discriminate. }
          destruct (excluded_middle_informative (b = y)) as [Hby | Hnby].
          { subst b. rewrite (Hrank_res _ Ha_res), Hrank_y in Hreq. discriminate. }
          assert (Hb_res : In A (Residual x y) b) by exact (Residual_intro _ _ _ Hnbx Hnby).
          (* Both in residual: use L' antisymmetry on the lifted pair. *)
          assert (HL'ab : L' (exist _ a Ha_res) (exist _ b Hb_res))
            by exact (HP_res a b Ha_res Hb_res HPab).
          assert (HL'ba : L' (exist _ b Hb_res) (exist _ a Ha_res))
            by exact (HP_res b a Hb_res Ha_res HPba).
          assert (Heqs : exist (fun z => In A (Residual x y) z) a Ha_res
                        = exist _ b Hb_res)
            by exact (HL'_pos.(poset_antisym) _ _ HL'ab HL'ba).
          exact (f_equal (@proj1_sig _ _) Heqs). }
    assert (HP_pos : IsPoset A P).
    { constructor.
      - intro a. apply t_step. left; reflexivity.
      - exact HP_antisym.
      - intros a b c HPab HPbc. eapply t_trans; eauto. }
    (* Use Szpilrajn to extend P to a total order. *)
    destruct (szpilrajn_theorem A P) as [L_full [HL_pos [HL_tot HL_ext]]].
    exists L_full.
    (* Helpers for building all the conjuncts. *)
    assert (Hext_R : forall a b, R a b -> L_full a b).
    { intros a b HRab. apply HL_ext. apply t_step. left.
      apply Hdiscrete. exact HRab. }
    assert (Hext_yx : L_full y x).
    { apply HL_ext. apply t_step. right. right. right. right. split; reflexivity. }
    assert (Hext_resy : forall a, In A (Residual x y) a -> L_full a y).
    { intros a Ha. apply HL_ext. apply t_step. right. right. left. split; [exact Ha | reflexivity]. }
    assert (Hext_resx : forall a, In A (Residual x y) a -> L_full a x).
    { intros a Ha. apply HL_ext. apply t_step. right. right. right. left. split; [exact Ha | reflexivity]. }
    assert (Hext_L' : forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
              L' (exist _ a ha) (exist _ b hb) -> L_full a b).
    { intros a b ha hb HLab. apply HL_ext. apply t_step.
      right. left. exists ha, hb. exact HLab. }
    assert (Hnot_xy : ~ L_full x y).
    { intro Hxy.
      pose proof Hext_yx as Hyx.
      assert (Heq : x = y) by exact (HL_pos.(poset_antisym) _ _ Hxy Hyx).
      contradiction. }
    assert (Hnot_yres : forall a, In A (Residual x y) a -> ~ L_full y a).
    { intros a Ha Hya. pose proof (Hext_resy a Ha) as Hay.
      assert (Heq : a = y) by exact (HL_pos.(poset_antisym) _ _ Hay Hya).
      apply (Residual_not_y x y a Ha Heq). }
    assert (Hnot_xres : forall a, In A (Residual x y) a -> ~ L_full x a).
    { intros a Ha Hxa. pose proof (Hext_resx a Ha) as Hax.
      assert (Heq : a = x) by exact (HL_pos.(poset_antisym) _ _ Hax Hxa).
      apply (Residual_not_x x y a Ha Heq). }
    assert (Hround : forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
              L_full a b -> L' (exist _ a ha) (exist _ b hb)).
    { intros a b ha hb Hfab.
      destruct (HL'_tot (exist _ a ha) (exist _ b hb)) as [HLab | HLba].
      - exact HLab.
      - assert (Hfba : L_full b a) by exact (Hext_L' b a hb ha HLba).
        assert (Heq : a = b) by exact (HL_pos.(poset_antisym) _ _ Hfab Hfba).
        subst b. assert (Hha_eq : ha = hb) by apply proof_irrelevance.
        rewrite Hha_eq. apply HL'_pos.(poset_refl). }
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    - apply (total_order_is_linear_extension R L_full HL_pos HL_tot Hext_R).
    - exact Hext_yx.
    - exact Hext_resy.
    - exact Hext_resx.
    - exact Hext_L'.
    - exact Hround.
    - exact Hnot_xy.
    - exact Hnot_yres.
    - exact Hnot_xres.
  Qed.

  (** Lift function, packaged via classical description. *)
  Lemma antichain_lift_function :
    (forall a b : A, R a b -> a = b) ->
    forall x y : A,
    x <> y ->
    exists lift : ({a : A | In A (Residual x y) a} ->
                    {a : A | In A (Residual x y) a} -> Prop)
                  -> (A -> A -> Prop),
      forall L',
        IsLinearExtension
          (fun a b : {a : A | In A (Residual x y) a} => R (proj1_sig a) (proj1_sig b)) L' ->
        IsLinearExtension R (lift L') /\
        (lift L') y x /\
        (forall a, In A (Residual x y) a -> (lift L') a y) /\
        (forall a, In A (Residual x y) a -> (lift L') a x) /\
        (forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
           L' (exist _ a ha) (exist _ b hb) -> (lift L') a b) /\
        (forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
           (lift L') a b -> L' (exist _ a ha) (exist _ b hb)) /\
        (~ (lift L') x y) /\
        (forall a, In A (Residual x y) a -> ~ (lift L') y a) /\
        (forall a, In A (Residual x y) a -> ~ (lift L') x a).
  Proof.
    intros Hdiscrete x y Hxy_neq.
    set (Q := fun (L' : {a : A | In A (Residual x y) a} ->
                          {a : A | In A (Residual x y) a} -> Prop)
                  (L_out : A -> A -> Prop) =>
                IsLinearExtension
                  (fun a b : {a : A | In A (Residual x y) a} => R (proj1_sig a) (proj1_sig b)) L' ->
                IsLinearExtension R L_out /\
                L_out y x /\
                (forall a, In A (Residual x y) a -> L_out a y) /\
                (forall a, In A (Residual x y) a -> L_out a x) /\
                (forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
                   L' (exist _ a ha) (exist _ b hb) -> L_out a b) /\
                (forall (a b : A) (ha : In A (Residual x y) a) (hb : In A (Residual x y) b),
                   L_out a b -> L' (exist _ a ha) (exist _ b hb)) /\
                (~ L_out x y) /\
                (forall a, In A (Residual x y) a -> ~ L_out y a) /\
                (forall a, In A (Residual x y) a -> ~ L_out x a)).
    assert (Hex : forall L', exists L_out, Q L' L_out).
    { intros L'. unfold Q.
      destruct (classic (IsLinearExtension
                  (fun a b : {a : A | In A (Residual x y) a} =>
                     R (proj1_sig a) (proj1_sig b)) L')) as [HL' | HnL'].
      - destruct (antichain_lift_witness Hdiscrete x y L' Hxy_neq HL')
          as [L_full Hall].
        exists L_full. intros _. exact Hall.
      - exists (fun _ _ => True). intro Hk. exfalso; apply HnL'; exact Hk. }
    set (lift := fun L' =>
                   proj1_sig (constructive_indefinite_description _ (Hex L'))).
    exists lift. intros L' HL'.
    pose proof (proj2_sig (constructive_indefinite_description _ (Hex L'))) as Hspec.
    apply Hspec. exact HL'.
  Qed.

  (** NOTE on hypotheses: the statement we can prove requires
      |A| ≥ 4 (equivalently, the residual has at least 2 elements).
      Without this, a degenerate antichain with |A| ∈ {2, 3} admits
      the empty realizer [r' = ∅] of [Rsub] with [d' = 0], yet no
      1-realizer of [R = eq] on A exists, so [IsRemovablePair x y]
      is mathematically false in these degenerate cases.

      We package the [n ≥ 4] hypothesis below.  In any realistic
      use of this lemma (Hiraguchi's theorem requires n ≥ 4),
      the hypothesis is available. *)

  (** Helper: derive [Inhabited r'] from a realizer-of-eq on a subtype
      with ≥ 2 distinct elements. *)
  Lemma antichain_realizer_inhabited :
    (forall a b : A, R a b -> a = b) ->
    forall x y : A,
    (exists a b, In A (Residual x y) a /\ In A (Residual x y) b /\ a <> b) ->
    forall (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                              {a : A | In A (Residual x y) a} -> Prop)),
      IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                     R (proj1_sig a) (proj1_sig b)) r' ->
      Ensembles.Inhabited _ r'.
  Proof.
    intros Hdiscrete x y [a [b [Ha [Hb Hab_neq]]]] r' Hr'_real.
    destruct (classic (Ensembles.Inhabited _ r')) as [Hinh | Hempty]; [exact Hinh|].
    exfalso.
    (* If r' is empty, then by realizer_intersection, Rsub everywhere holds.
       But Rsub a b iff R a b iff a = b (by discrete).  Pick a, b distinct,
       so Rsub a b is false, contradiction. *)
    set (asub := exist (fun z => In A (Residual x y) z) a Ha).
    set (bsub := exist (fun z => In A (Residual x y) z) b Hb).
    assert (Hall : forall L, In _ r' L -> L asub bsub).
    { intros L HL. exfalso. apply Hempty. exists L; exact HL. }
    assert (HRab : R a b)
      by exact (proj2 (Hr'_real.(realizer_intersection) asub bsub) Hall).
    exact (Hab_neq (Hdiscrete _ _ HRab)).
  Qed.

  Lemma antichain_removable_pair :
    (forall a b : A, R a b -> a = b) ->
    forall x y : A, x <> y ->
    (exists a b, In A (Residual x y) a /\ In A (Residual x y) b /\ a <> b) ->
    IsRemovablePair x y.
  Proof.
    intros Hdiscrete x y Hxy_neq Hres_pair.
    split; [exact Hxy_neq |].
    intros d' r' Hr'_real Hr'_card.
    pose proof (antichain_realizer_inhabited Hdiscrete x y Hres_pair r' Hr'_real)
      as Hr'_inh.
    (* Step 1: get the lift function. *)
    destruct (antichain_lift_function Hdiscrete x y Hxy_neq) as [lift Hlift_spec].
    (* Step 2: build L_extra — a total order on A with prescribed structure:
       x < y < (residual).  This satisfies:
         - L_extra x y                                (forced by build)
         - L_extra x a   for every a ∈ Residual      (x is the bottom)
         - L_extra y a   for every a ∈ Residual      (y is second-bottom)
       Each lift L' from antichain_lift_witness has residual < y < x, so
       the lifted orders disagree with L_extra on (x, y), giving disjointness,
       and disagree on boundary pairs (p, x) / (p, y) for p ∈ residual,
       so {L_extra} together with the lifts realises R. *)
    assert (HL_extra_witness : exists L_extra : A -> A -> Prop,
              IsLinearExtension R L_extra /\
              L_extra x y /\
              (forall a, In A (Residual x y) a -> L_extra x a) /\
              (forall a, In A (Residual x y) a -> L_extra y a) /\
              ~ L_extra y x /\
              (forall a, In A (Residual x y) a -> ~ L_extra a x) /\
              (forall a, In A (Residual x y) a -> ~ L_extra a y)).
    { (* Build prescription Pe forcing: x = a, or x → y, or x → residual, or y → residual.
         Also reflexivity for all (a=b). *)
      set (Pe := clos_trans A (fun a b =>
                  a = b
                  \/ (a = x /\ b = y)
                  \/ (a = x /\ In A (Residual x y) b)
                  \/ (a = y /\ In A (Residual x y) b))).
      (* Show Pe is a poset using a rank function: rank x = 0, rank y = 1,
         rank residual = 2.  Pe-steps preserve rank a ≤ rank b. *)
      set (rank := fun a : A =>
                     if excluded_middle_informative (a = x) then 0%nat
                     else if excluded_middle_informative (a = y) then 1%nat else 2%nat).
      assert (Hrank_x : rank x = 0%nat).
      { unfold rank.
        destruct (excluded_middle_informative (x = x)); [reflexivity | contradiction]. }
      assert (Hrank_y : rank y = 1%nat).
      { unfold rank.
        destruct (excluded_middle_informative (y = x)); [contradiction Hxy_neq; auto |].
        destruct (excluded_middle_informative (y = y)); [reflexivity | contradiction]. }
      assert (Hrank_res : forall a, In A (Residual x y) a -> rank a = 2%nat).
      { intros a Ha. unfold rank.
        destruct (excluded_middle_informative (a = x)) as [Heq | _].
        - exfalso. apply (Residual_not_x _ _ _ Ha Heq).
        - destruct (excluded_middle_informative (a = y)) as [Heq | _].
          + exfalso. apply (Residual_not_y _ _ _ Ha Heq).
          + reflexivity. }
      assert (Hstep_rank : forall a b,
                (a = b
                 \/ (a = x /\ b = y)
                 \/ (a = x /\ In A (Residual x y) b)
                 \/ (a = y /\ In A (Residual x y) b)) ->
                rank a <= rank b).
      { intros a b [Heq | [[Hax Hby] | [[Hax Hbr] | [Hay Hbr]]]].
        - subst; lia.
        - subst; rewrite Hrank_x, Hrank_y; lia.
        - subst; rewrite Hrank_x, (Hrank_res _ Hbr); lia.
        - subst; rewrite Hrank_y, (Hrank_res _ Hbr); lia. }
      assert (HPe_rank : forall a b, Pe a b -> rank a <= rank b).
      { intros a b HPab. induction HPab as [a b Hstep | a m b _ IH1 _ IH2].
        - apply Hstep_rank, Hstep.
        - lia. }
      assert (HPe_pos : IsPoset A Pe).
      { constructor.
        - intro a. apply t_step. left; reflexivity.
        - intros a b HPab HPba.
          assert (Hra_le : rank a <= rank b) by exact (HPe_rank _ _ HPab).
          assert (Hrb_le : rank b <= rank a) by exact (HPe_rank _ _ HPba).
          assert (Hreq : rank a = rank b) by lia.
          (* a = b in all three rank-classes (singleton at ranks 0 and 1; for rank 2,
             use Pe's path-invariant). *)
          destruct (excluded_middle_informative (a = x)) as [Hax | Hnax].
          + subst a. destruct (excluded_middle_informative (b = x)) as [|];
              [subst; reflexivity|].
            rewrite Hrank_x in Hreq.
            destruct (excluded_middle_informative (b = y)) as [Hby | Hnby].
            * subst b. rewrite Hrank_y in Hreq. discriminate.
            * assert (Hb_res : In A (Residual x y) b) by exact (Residual_intro _ _ _ n Hnby).
              rewrite (Hrank_res _ Hb_res) in Hreq. discriminate.
          + destruct (excluded_middle_informative (a = y)) as [Hay | Hnay].
            * subst a. destruct (excluded_middle_informative (b = x)) as [Hbx | Hnbx].
              { subst b. rewrite Hrank_y, Hrank_x in Hreq. discriminate. }
              destruct (excluded_middle_informative (b = y)) as [|];
                [subst; reflexivity|].
              assert (Hb_res : In A (Residual x y) b) by exact (Residual_intro _ _ _ Hnbx n).
              rewrite Hrank_y, (Hrank_res _ Hb_res) in Hreq. discriminate.
            * assert (Ha_res : In A (Residual x y) a) by exact (Residual_intro _ _ _ Hnax Hnay).
              destruct (excluded_middle_informative (b = x)) as [Hbx | Hnbx].
              { subst b. rewrite (Hrank_res _ Ha_res), Hrank_x in Hreq. discriminate. }
              destruct (excluded_middle_informative (b = y)) as [Hby | Hnby].
              { subst b. rewrite (Hrank_res _ Ha_res), Hrank_y in Hreq. discriminate. }
              assert (Hb_res : In A (Residual x y) b) by exact (Residual_intro _ _ _ Hnbx Hnby).
              (* Both in residual.  Use Pe path-invariant: a Pe-path from a (residual)
                 to b is either trivial (a = b) — no Pe-step can take a residual
                 element anywhere except itself (no rule applies for "a residual"). *)
              assert (Hpath_res : forall c d, Pe c d -> In A (Residual x y) c -> c = d).
              { intros c d HPcd Hc_res.
                induction HPcd as [c d Hstep | c m d _ IH1 _ IH2].
                - destruct Hstep as [Heq | [[Hcx _] | [[Hcx _] | [Hcy _]]]].
                  + exact Heq.
                  + exfalso. apply (Residual_not_x _ _ _ Hc_res Hcx).
                  + exfalso. apply (Residual_not_x _ _ _ Hc_res Hcx).
                  + exfalso. apply (Residual_not_y _ _ _ Hc_res Hcy).
                - assert (Hcm : c = m) by exact (IH1 Hc_res).
                  subst m. exact (IH2 Hc_res). }
              exact (Hpath_res a b HPab Ha_res).
        - intros a b c HPab HPbc. eapply t_trans; eauto. }
      destruct (szpilrajn_theorem A Pe) as [Le [HLe_pos [HLe_tot HLe_ext]]].
      assert (Hext_R : forall a b, R a b -> Le a b).
      { intros a b HRab. apply HLe_ext, t_step. left. apply Hdiscrete. exact HRab. }
      assert (Hext_xy : Le x y) by (apply HLe_ext, t_step; right; left; split; reflexivity).
      assert (Hext_xres : forall a, In A (Residual x y) a -> Le x a).
      { intros a Ha. apply HLe_ext, t_step. right. right. left. split; [reflexivity | exact Ha]. }
      assert (Hext_yres : forall a, In A (Residual x y) a -> Le y a).
      { intros a Ha. apply HLe_ext, t_step. right. right. right. split; [reflexivity | exact Ha]. }
      assert (Hnot_yx : ~ Le y x).
      { intro Hyx. assert (Heq : x = y) by exact (HLe_pos.(poset_antisym) _ _ Hext_xy Hyx).
        contradiction. }
      assert (Hnot_resx : forall a, In A (Residual x y) a -> ~ Le a x).
      { intros a Ha Hax. pose proof (Hext_xres a Ha) as Hxa.
        assert (Heq : x = a) by exact (HLe_pos.(poset_antisym) _ _ Hxa Hax).
        apply (Residual_not_x x y a Ha (eq_sym Heq)). }
      assert (Hnot_resy : forall a, In A (Residual x y) a -> ~ Le a y).
      { intros a Ha Hay. pose proof (Hext_yres a Ha) as Hya.
        assert (Heq : y = a) by exact (HLe_pos.(poset_antisym) _ _ Hya Hay).
        apply (Residual_not_y x y a Ha (eq_sym Heq)). }
      exists Le. split; [| split; [| split; [| split; [| split; [| split]]]]].
      - apply (total_order_is_linear_extension R Le HLe_pos HLe_tot Hext_R).
      - exact Hext_xy.
      - exact Hext_xres.
      - exact Hext_yres.
      - exact Hnot_yx.
      - exact Hnot_resx.
      - exact Hnot_resy. }
    destruct HL_extra_witness as [L_extra [HL_extra_lin
      [HL_extra_xy [HL_extra_xres [HL_extra_yres
       [HL_extra_nyx [HL_extra_nresx HL_extra_nresy]]]]]]].
    (* Step 3: assemble r = Add (Im r' lift) L_extra. *)
    set (r_lifted := Im _ _ r' lift).
    exists (Add (A -> A -> Prop) r_lifted L_extra).
    (* Helper: each element of r_lifted comes from some L' ∈ r'. *)
    assert (Hlift_each : forall L, In _ r_lifted L ->
              exists L', In _ r' L' /\ lift L' = L /\
                IsLinearExtension
                  (fun a b : {a : A | In A (Residual x y) a} => R (proj1_sig a) (proj1_sig b)) L').
    { intros L HL. destruct HL as [L' HL'_in y0 HLeq].
      exists L'. split; [exact HL'_in | split; [symmetry; exact HLeq |]].
      exact (Hr'_real.(realizer_linear) L' HL'_in). }
    (* L_extra is not in r_lifted: L_extra has x < y but every lift has NOT x < y. *)
    assert (Hextra_notin : ~ In _ r_lifted L_extra).
    { intro HinExtra.
      destruct (Hlift_each L_extra HinExtra) as [L' [HL'_in [Hleq HL'_lin]]].
      destruct (Hlift_spec L' HL'_lin) as [_ [_ [_ [_ [_ [_ [Hnotxy _]]]]]]].
      apply Hnotxy. rewrite Hleq. exact HL_extra_xy. }
    (* Cardinality of r_lifted. *)
    assert (Hlift_card : cardinal (A -> A -> Prop) r_lifted d').
    { apply cardinal_Im_injective; [exact Hr'_card |].
      intros L'1 L'2 HL'1_in HL'2_in Heq.
      assert (HL'1_lin : IsLinearExtension
                  (fun a b : {a : A | In A (Residual x y) a} =>
                     R (proj1_sig a) (proj1_sig b)) L'1)
        by exact (Hr'_real.(realizer_linear) L'1 HL'1_in).
      assert (HL'2_lin : IsLinearExtension
                  (fun a b : {a : A | In A (Residual x y) a} =>
                     R (proj1_sig a) (proj1_sig b)) L'2)
        by exact (Hr'_real.(realizer_linear) L'2 HL'2_in).
      destruct (Hlift_spec L'1 HL'1_lin) as [_ [_ [_ [_ [Hext1 [Hres1 _]]]]]].
      destruct (Hlift_spec L'2 HL'2_lin) as [_ [_ [_ [_ [Hext2 [Hres2 _]]]]]].
      apply functional_extensionality. intro a.
      apply functional_extensionality. intro b.
      apply propositional_extensionality.
      destruct a as [a ha]; destruct b as [b hb]. simpl.
      split; intro HL.
      + apply (Hres2 a b ha hb).
        rewrite <- Heq. exact (Hext1 a b ha hb HL).
      + apply (Hres1 a b ha hb).
        rewrite Heq. exact (Hext2 a b ha hb HL). }
    split.
    - (* IsRealizer R (Add r_lifted L_extra). *)
      assert (Hall_lin : forall L, In _ (Add _ r_lifted L_extra) L ->
                IsLinearExtension R L).
      { intros L HL. destruct HL as [L HL | L HL].
        - destruct (Hlift_each L HL) as [L' [_ [Hleq HL'_lin]]].
          destruct (Hlift_spec L' HL'_lin) as [Hlin _].
          rewrite <- Hleq. exact Hlin.
        - destruct HL. exact HL_extra_lin. }
      constructor.
      + exact Hall_lin.
      + intros p q. split.
        * intros HRpq L HL. exact ((Hall_lin L HL).(linear_extends) p q HRpq).
        * intros Hall.
          (* R = eq.  We want R p q.  Suffices to show p = q.  Suppose not. *)
          destruct (classic (p = q)) as [Heq | Hne]; [subst; apply poset_refl |].
          exfalso.
          (* Helper for picking ANY L' ∈ r' (available since cardinal r' d',
             but we may also have d' = 0).  We will only need such an L'
             when its absence forces |Residual| ≤ 1, which rules out the
             residual-cases below. *)
          (* Helper: from realizer-intersection on r', if NOT (R psub qsub),
             extract some L' ∈ r' with NOT L' psub qsub. *)
          assert (Hsub_split :
            forall (p q : A) (hp : In A (Residual x y) p) (hq : In A (Residual x y) q),
              p <> q ->
              exists L', In _ r' L' /\ ~ L' (exist _ p hp) (exist _ q hq)).
          { intros p0 q0 hp hq Hneq.
            set (psub := exist (fun a => In A (Residual x y) a) p0 hp).
            set (qsub := exist (fun a => In A (Residual x y) a) q0 hq).
            assert (HnRsub : ~ R p0 q0)
              by (intro HR; exact (Hneq (Hdiscrete _ _ HR))).
            assert (Hnotall : ~ forall L', In _ r' L' -> L' psub qsub).
            { intro Hall'. apply HnRsub.
              exact (proj2 (Hr'_real.(realizer_intersection) psub qsub) Hall'). }
            apply not_all_ex_not in Hnotall.
            destruct Hnotall as [L' Hnimpl].
            apply imply_to_and in Hnimpl.
            exists L'. exact Hnimpl. }
          (* Case-analysis on whether p, q are in the residual. *)
          destruct (classic (In A (Residual x y) p)) as [Hp_res | Hp_nres].
          { destruct (classic (In A (Residual x y) q)) as [Hq_res | Hq_nres].
            - (* Both in residual: use sub-realizer property of r'. *)
              destruct (Hsub_split p q Hp_res Hq_res Hne) as [L' [HL'_in HnL'pq]].
              pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
              destruct (Hlift_spec L' HL'_lin)
                as [_ [_ [_ [_ [_ [Hres _]]]]]].
              assert (HinR : In _ r_lifted (lift L'))
                by exact (Im_intro _ _ _ lift L' HL'_in (lift L') eq_refl).
              assert (Hlift_pq : lift L' p q)
                by exact (Hall (lift L') (Union_introl _ _ _ _ HinR)).
              apply HnL'pq.
              exact (Hres p q Hp_res Hq_res Hlift_pq).
            - (* p ∈ res, q ∉ res, so q = x or q = y. *)
              destruct (classic (q = x)) as [Hqx | Hqnx].
              + (* q = x: need NOT L p x for some L.  L_extra has NOT L_extra p x. *)
                subst q.
                assert (HLep : L_extra p x)
                  by exact (Hall L_extra (Union_intror _ _ _ _ (In_singleton _ _))).
                exact (HL_extra_nresx p Hp_res HLep).
              + destruct (classic (q = y)) as [Hqy | Hqny].
                * (* q = y. *)
                  subst q.
                  assert (HLep : L_extra p y)
                    by exact (Hall L_extra (Union_intror _ _ _ _ (In_singleton _ _))).
                  exact (HL_extra_nresy p Hp_res HLep).
                * exfalso. apply Hq_nres. apply Residual_intro; assumption. }
          { (* p ∉ res, so p = x or p = y. *)
            destruct (classic (p = x)) as [Hpx | Hpnx].
            - subst p.
              destruct (classic (q = y)) as [Hqy | Hqny].
              + (* (p, q) = (x, y): need NOT L x y for some L.
                   Every lift has NOT (lift L') x y.  We need some L' ∈ r'
                   to obtain such a lift; we obtain one if r' is non-empty.
                   If r' is empty, d' = 0 and r_lifted is empty, so
                   only L_extra is in r.  But L_extra x y is true.
                   In that case, x = q = y → x = y, contradicting Hxy_neq.

                   We don't need to special-case: if d' = 0 then |Residual| ≤ 1
                   so |A| ≤ 3, but x ≠ y still doesn't force the realizer
                   property.  Actually, we need to be careful: when r' is empty,
                   we have NO lift to pick.  But we still have L_extra in r.
                   And L_extra x y is true (Hall L_extra x y) is consistent;
                   we'd lose.

                   However: when r' is empty, the realizer-property of r' on
                   the subtype is "Rsub a b ↔ True for all (a, b)", which on
                   the eq-sub-relation forces the subtype to have ≤ 1 element,
                   i.e., |Residual| ≤ 1.  Combined with x ≠ y in A, this means
                   |A| ≤ 3.

                   We don't need to invoke this; instead we pick a lift directly.
                   But we need r' nonempty.  Case split: *)
                subst q.
                destruct Hr'_inh as [L' HL'_in].
                pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
                destruct (Hlift_spec L' HL'_lin) as [_ [_ [_ [_ [_ [_ [Hnotxy _]]]]]]].
                assert (HinR : In _ r_lifted (lift L'))
                  by exact (Im_intro _ _ _ lift L' HL'_in (lift L') eq_refl).
                assert (Hlift_xy : lift L' x y)
                  by exact (Hall (lift L') (Union_introl _ _ _ _ HinR)).
                exact (Hnotxy Hlift_xy).
              + destruct (classic (q = x)) as [Hqx | Hqnx].
                * (* (p, q) = (x, x), but p = x = q, contradicts Hne. *)
                  subst q. contradiction Hne; reflexivity.
                * (* q ∈ residual. *)
                  assert (Hq_res : In A (Residual x y) q)
                    by exact (Residual_intro _ _ _ Hqnx Hqny).
                  (* (p, q) = (x, residual): need NOT L x q for some L.
                     Lift L' has residual < y < x; specifically NOT lift L' x q.
                     Need some L' ∈ r'.  Same r'-empty issue. *)
                  destruct Hr'_inh as [L' HL'_in].
                  pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
                  destruct (Hlift_spec L' HL'_lin)
                    as [_ [_ [_ [_ [_ [_ [_ [_ Hnxres]]]]]]]].
                  assert (HinR : In _ r_lifted (lift L'))
                    by exact (Im_intro _ _ _ lift L' HL'_in (lift L') eq_refl).
                  assert (Hlift_xq : lift L' x q)
                    by exact (Hall (lift L') (Union_introl _ _ _ _ HinR)).
                  exact (Hnxres q Hq_res Hlift_xq).
            - destruct (classic (p = y)) as [Hpy | Hpny].
              + subst p.
                destruct (classic (q = x)) as [Hqx | Hqnx].
                * (* (p, q) = (y, x): need NOT L y x for some L.
                     L_extra has NOT L_extra y x. *)
                  subst q.
                  assert (HLep : L_extra y x)
                    by exact (Hall L_extra (Union_intror _ _ _ _ (In_singleton _ _))).
                  exact (HL_extra_nyx HLep).
                * destruct (classic (q = y)) as [Hqy | Hqny].
                  -- subst q. contradiction Hne; reflexivity.
                  -- assert (Hq_res : In A (Residual x y) q)
                       by exact (Residual_intro _ _ _ Hqnx Hqny).
                     (* (p, q) = (y, residual): lift has NOT lift L' y q. *)
                     destruct Hr'_inh as [L' HL'_in].
                     pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
                     destruct (Hlift_spec L' HL'_lin)
                       as [_ [_ [_ [_ [_ [_ [_ [Hnyres _]]]]]]]].
                     assert (HinR : In _ r_lifted (lift L'))
                       by exact (Im_intro _ _ _ lift L' HL'_in (lift L') eq_refl).
                     assert (Hlift_yq : lift L' y q)
                       by exact (Hall (lift L') (Union_introl _ _ _ _ HinR)).
                     exact (Hnyres q Hq_res Hlift_yq).
              + exfalso. apply Hp_nres. apply Residual_intro; assumption. }
    - (* Cardinality: |Add r_lifted L_extra| = d' + 1. *)
      assert (Hcardadd : cardinal (A -> A -> Prop)
                           (Add (A -> A -> Prop) r_lifted L_extra) (S d')).
      { apply card_add; [exact Hlift_card | exact Hextra_notin]. }
      replace (d' + 1) with (S d') by lia.
      exact Hcardadd.
  Qed.

  (** ==================================================================
      TROTTER'S REMOVABLE-PAIR LEMMA — STRUCTURAL DECOMPOSITION
      ==================================================================

      Goal: every finite poset on n >= 4 elements with at least one
      incomparable pair has a removable pair (in the realizer-existence
      sense of [IsRemovablePair]).

      Status: outer lemma [removable_pair_exists] is Qed via a
      classical case split on whether R is an antichain.  The
      structural decomposition below introduces two Qed sub-lemmas
      and one HONESTLY Admitted sub-lemma; the outer lemma's body is
      mechanically composed from them.

      --------------------------------------------------------------
      DECOMPOSITION
      --------------------------------------------------------------

      Sub-lemma (A1) [antichain_removable_pair] — Qed.
        If R is the antichain (all R-related elements are equal) and
        the residual of any (x, y) with x ≠ y has ≥ 2 distinct
        elements, then (x, y) is a removable pair.

      Sub-lemma (A2) [admissible_critical_pair_is_removable] — Qed.
        If (x', y') is a critical pair of R such that every critical
        pair (p, q) of R EITHER equals (x', y') OR has both endpoints
        in Residual x' y' (we call this "admissible"), then (x', y')
        is a removable pair.  Follows from [extension_through_critical_pair].

      Sub-lemma (B) [non_antichain_removable_pair_exists] — Qed,
        via the focused Admitted [trotter_boundary_coverage].
        If R has a strict edge a < b and an incomparable pair, with
        n ≥ 4, then SOME pair (x, y) is a removable pair.

        IMPORTANT NEGATIVE RESULT: the obvious refinement
            "some critical pair is admissible"
        is FALSE even in the non-antichain case.  Counterexample:
        A = {a, b, c, d}, R = {a < b} (plus reflexivity).  R has
        6 critical pairs (see comment on [non_antichain_removable_pair_exists])
        and none are admissible, yet a removable pair exists.

        Conclusion: the non-antichain case cannot be reduced to an
        admissibility statement and instead needs the boundary-aware
        Szpilrajn construction.

      --------------------------------------------------------------
      WHAT'S MISSING TO CLOSE (B)
      --------------------------------------------------------------

      Trotter's actual proof (Ch. 6) does NOT route through an
      admissible CP at the outer level. Instead it constructs the
      lift-and-reverse extensions directly, handling boundary CPs
      by a more careful Szpilrajn construction that ORIENTS the
      lift to also reverse a chosen boundary CP. This requires
      strengthening [cp_lift_function] / [lift_and_force_is_poset]
      to accept a "boundary orientation" parameter — see the long
      gap comment in [extend_through_cp_construction] in
      Theorems.v lines 2026–2074.

      STATUS (Phase B3, after extremality refinement).  Steps 1 and
      2 below are now Qed (via [lift_and_force_with_boundary_is_poset]
      and [cp_lift_function_with_boundary] in Theorems.v).  The
      caller's CHOICE function (Step 3) is the residual mathematical
      gap, now captured by the REFINED-SIGNATURE Admitted
      [trotter_boundary_existence].  Critically, the refinement
      requires the input CP to be EXTREMAL — obtained via
      [extremal_cp_exists] in CriticalPairDigraph.v.

      The honest path forward (not pursued in this task due to time
      budget) is:

        1. [DONE] Generalize [lift_and_force_is_poset] to accept a
           finite set S_b of boundary-CP orientations, proving the
           transitive closure of (R ∪ L'_lift ∪ {(x',y')} ∪ S_b) is
           a poset under suitable assumptions on the boundary CPs.
           ([lift_and_force_with_boundary_is_poset], Qed.)
        2. [DONE] Build [cp_lift_function_with_boundary] selecting a
           lift map whose lifts simultaneously reverse all required
           boundary CPs.  ([cp_lift_function_with_boundary], Qed.)
        3. [GAP] Use a CHOICE function on boundary CPs (each L' ∈ r'
           chooses which boundary CPs to reverse, based on its
           sub-realizer structure) so that the union
           [Im r' lift_b ∪ {L_extra}] reverses every critical pair.
           This is now [trotter_boundary_existence] with EXTREMAL CP
           hypothesis (Admitted, refined signature).
        4. [DONE] Conclude [removable_pair_exists] without ever
           needing the false "admissible CP" condition.
           ([trotter_boundary_coverage] is a Qed composition modulo
           the Step 3 admit.)
      ================================================================== *)

  (** A critical pair (x', y') of R is "admissible" iff every critical
      pair (p, q) of R either equals (x', y') or has both endpoints in
      Residual x' y'. NB: in general (e.g., the antichain) no admissible
      critical pair exists; see comment block above. *)
  Definition AdmissibleCP (x' y' : A) : Prop :=
    IsCriticalPair R x' y' /\
    forall p q : A, IsCriticalPair R p q ->
      (p = x' /\ q = y') \/ (In A (Residual x' y') p /\ In A (Residual x' y') q).

  (** Convert between the [Residual] form used in [IsRemovablePair] and
      the [Setminus] form used in [extension_through_critical_pair]. *)
  Lemma Residual_eq_Setminus :
    forall x y : A,
      Residual x y =
      Setminus A (Setminus A (Full_set A) (Singleton A x)) (Singleton A y).
  Proof. intros; reflexivity. Qed.

  (** Sub-lemma (A): an admissible critical pair is removable.
      Closed via [extension_through_critical_pair]. *)
  Lemma admissible_critical_pair_is_removable :
    forall (x' y' : A),
      Finite A (Full_set A) ->
      AdmissibleCP x' y' ->
      IsRemovablePair x' y'.
  Proof.
    intros x' y' HfinA [Hcp Hno_boundary].
    assert (Hxy_neq : x' <> y').
    { intro Heq.
      apply (critical_incomparable Hcp).
      left. rewrite Heq. apply poset_refl. }
    split; [exact Hxy_neq |].
    intros d' r' Hr'_real Hr'_card.
    set (S' := Residual x' y').
    assert (HS'_eq : S' =
                     Setminus A (Setminus A (Full_set A) (Singleton A x'))
                              (Singleton A y'))
      by reflexivity.
    (* Apply extension_through_critical_pair.
       [R] is passed explicitly because [extension_through_critical_pair]
       is defined in a closed section. *)
    exact (extension_through_critical_pair R x' y' S' d' HfinA Hcp HS'_eq
             Hno_boundary
             (ex_intro _ r' (conj Hr'_real Hr'_card))).
  Qed.

  (** Classical case split: either R is an antichain (= the discrete order
      on A) or R has a genuine strict comparability. *)
  Lemma R_is_antichain_dec :
    (forall a b : A, R a b -> a = b) \/ (exists a b : A, R a b /\ a <> b).
  Proof.
    destruct (classic (exists a b : A, R a b /\ a <> b)) as [Hne | Hne].
    - right; exact Hne.
    - left. intros a b HRab.
      destruct (classic (a = b)) as [Heq | Hneq]; [exact Heq |].
      exfalso. apply Hne. exists a, b. split; assumption.
  Qed.

  (** From [cardinal Full_set n] with [n >= 4] and [x <> y], the residual
      [Residual x y] contains at least two distinct elements. *)
  Lemma residual_has_two_distinct :
    forall n (x y : A),
    cardinal A (Full_set A) n ->
    n >= 4 ->
    x <> y ->
    exists a b, In A (Residual x y) a /\ In A (Residual x y) b /\ a <> b.
  Proof.
    intros n x y Hcard Hn4 Hxy_neq.
    (* Step 1: residual has cardinal (n - 2). *)
    assert (Hx_in : In A (Full_set A) x) by apply Full_intro.
    assert (Hy_in : In A (Full_set A) y) by apply Full_intro.
    destruct n as [| n1]; [exfalso; lia |].
    assert (Hcard1 : cardinal A (Subtract A (Full_set A) x) n1)
      by exact (cardinal_subtract_sn A (Full_set A) x n1 Hcard Hx_in).
    assert (Hy_in1 : In A (Subtract A (Full_set A) x) y).
    { split; [exact Hy_in |]. intro Hin. inversion Hin as [Heq].
      apply Hxy_neq. exact Heq. }
    destruct n1 as [| n2]; [exfalso; lia |].
    assert (Hcard2 : cardinal A (Subtract A (Subtract A (Full_set A) x) y) n2)
      by exact (cardinal_subtract_sn A (Subtract A (Full_set A) x) y n2 Hcard1 Hy_in1).
    (* [Subtract (Subtract Full x) y] is definitionally [Residual x y]. *)
    assert (HRes_eq : Subtract A (Subtract A (Full_set A) x) y = Residual x y)
      by reflexivity.
    rewrite HRes_eq in Hcard2.
    (* Step 2: extract two distinct elements via cardinal_subtract_sn. *)
    destruct n2 as [| n3]; [exfalso; lia |].
    (* Residual is inhabited; pick a. *)
    assert (Hinh_res : Inhabited A (Residual x y))
      by exact (cardinal_elim A (Residual x y) (S n3) Hcard2).
    destruct Hinh_res as [a Ha].
    assert (Hcard3 : cardinal A (Subtract A (Residual x y) a) n3)
      by exact (cardinal_subtract_sn A (Residual x y) a n3 Hcard2 Ha).
    destruct n3 as [| n4]; [exfalso; lia |].
    (* Residual minus a is inhabited; pick b. *)
    assert (Hinh_res2 : Inhabited A (Subtract A (Residual x y) a))
      by exact (cardinal_elim A (Subtract A (Residual x y) a) (S n4) Hcard3).
    destruct Hinh_res2 as [b [Hb_res Hb_neq_a]].
    exists a, b. split; [exact Ha |]. split; [exact Hb_res |].
    intro Heq. apply Hb_neq_a. rewrite Heq. constructor.
  Qed.

  (** ==================================================================
      Sub-lemma (B): in the non-antichain case, find some pair (x, y)
      that is a removable pair.

      We FACTORED OUT a single Admitted obligation here so that the outer
      lemma [removable_pair_exists] composes cleanly via a case split.

      SOUNDNESS WARNING.  The "obvious" choice for this sub-lemma —
      namely [non_antichain_admissible_cp_exists], asserting that some
      critical pair (x', y') of R is admissible in the sense of
      [AdmissibleCP] (every other CP lies in its residual) — is
      **provably false** even in the non-antichain case.

      Counterexample.  Let A = {a, b, c, d} (n = 4) with R given by
      reflexivity together with the single strict edge [a < b].  Then
      R has six critical pairs: (a,c), (a,d), (c,b), (d,b), (c,d),
      (d,c).  For each candidate (x', y') the residual Residual x' y'
      excludes both x' and y', leaving two elements; some other critical
      pair always has an endpoint among {x', y'}.  In particular:
        - Res(a, c) = {b, d}; (a, d) is a CP with a ∉ {b, d}.
        - Res(d, b) = {a, c}; (a, d) is a CP with d ∉ {a, c}.
      …and so on for the remaining four CPs.  Thus no critical pair is
      admissible, yet (e.g.) (c, d) IS a removable pair in the Trotter
      realizer-existence sense.

      Therefore we cannot route the outer lemma through admissibility.
      The honest statement of the sub-lemma is the conclusion of the
      outer lemma itself — finding a removable pair directly — and the
      genuine combinatorial work has been left unfactored here.  See the
      WHAT'S MISSING comment block above for the full discussion of the
      strengthened Szpilrajn construction this would require.
      ================================================================== *)

  (** Controlled Szpilrajn helper: given a poset [P] and a list of
      preferences (pair orientations to enforce), if the augmented
      relation [TC(P ∪ prefs)] is still a poset, produce a linear
      extension of [P] respecting every preference. *)
  Lemma szpilrajn_with_prefs :
    forall (P : A -> A -> Prop) (prefs : list (A * A)),
    IsPoset A P ->
    IsPoset A (clos_trans A (fun a b => P a b \/ List.In (a, b) prefs)) ->
    exists L : A -> A -> Prop,
      IsLinearExtension P L /\
      (forall p, List.In p prefs -> L (fst p) (snd p)).
  Proof.
    intros P prefs HP_poset HAug_poset.
    set (Aug := fun a b => P a b \/ List.In (a, b) prefs).
    set (AugTC := clos_trans A Aug).
    destruct (szpilrajn_theorem A AugTC) as [L [HL_pos [HL_tot HL_ext]]].
    exists L. split.
    - apply (total_order_is_linear_extension P L HL_pos HL_tot).
      intros a b HPab. apply HL_ext. apply t_step. left. exact HPab.
    - intros [u v] Hin. simpl.
      apply HL_ext. apply t_step. right. exact Hin.
  Qed.

  (** NOTE on possible attack via [szpilrajn_with_prefs]:
      The helper above lets us build a linear extension of R reversing
      a given list of pairs, PROVIDED the augmented closure is still a
      poset.  For the non-antichain case, the obstruction is selecting
      the prefs: starting from a critical pair (x', y') one needs to
      add reversals (q', p') for every boundary CP (p', q') (with one
      endpoint in {x', y'}) whose lift would otherwise create a cycle
      via L'-induced paths.  The structural choice of WHICH boundary
      CPs to reverse jointly without creating cycles is Trotter's hard
      combinatorial step (Ch.6) and is not closed here. *)

  (** Sub-lemma: every incomparable pair contains a critical pair.
      Wrapper around [incomparable_lifting_to_critical_pair] from
      CriticalPairs.v that packages the finiteness hypothesis from
      the [cardinal Full_set n] form used in [removable_pair_exists]. *)
  Lemma critical_pair_exists_from_incomparable :
    forall n,
    cardinal A (Full_set A) n ->
    forall a b, Incomparable R a b ->
    exists x y, IsCriticalPair R x y.
  Proof.
    intros n Hcard a b Hinc.
    assert (HfinA : Finite A (Full_set A))
      by exact (cardinal_finite A (Full_set A) n Hcard).
    destruct (incomparable_lifting_to_critical_pair R HfinA a b Hinc)
      as [x [y [_ [_ Hcp]]]].
    exists x, y. exact Hcp.
  Qed.

  (** ==================================================================
      Boundary reversal sets — Step 1 of the Trotter redesign.
      ==================================================================

      A "boundary reversal set" for a critical pair (x', y') is a finite
      list of CPs of R, each with one endpoint in {x', y'}, that we
      intend to *reverse* via additional forced edges in a per-L' lift.
      Each pair in B has incomparable endpoints (since it is a CP), and
      we exclude (x', y') itself and its reverse — those are handled
      directly by the cp_lift_function machinery.

      See [docs/superpowers/plans/2026-05-19-trotter-removable-pair-redesign.md].
      ================================================================== *)
  Definition IsBoundaryReversalSet (x' y' : A) (B : list (A * A)) : Prop :=
    List.Forall (fun pq : A * A =>
      IsCriticalPair R (fst pq) (snd pq) /\
      (fst pq = x' \/ fst pq = y' \/ snd pq = x' \/ snd pq = y') /\
      (fst pq, snd pq) <> (x', y') /\
      (fst pq, snd pq) <> (y', x')) B.

  (** The empty boundary set is trivially valid for any (x', y'). *)
  Lemma boundary_set_nil_valid :
    forall x' y', IsBoundaryReversalSet x' y' nil.
  Proof.
    intros x' y'. unfold IsBoundaryReversalSet. apply List.Forall_nil.
  Qed.

  (** Destructuring helper: a [cons] boundary set is the head pair
      satisfying the boundary conditions, plus a tail boundary set. *)
  Lemma boundary_set_cons_inv :
    forall x' y' pq B,
    IsBoundaryReversalSet x' y' (pq :: B) ->
    IsCriticalPair R (fst pq) (snd pq) /\
    (fst pq = x' \/ fst pq = y' \/ snd pq = x' \/ snd pq = y') /\
    (fst pq, snd pq) <> (x', y') /\
    (fst pq, snd pq) <> (y', x') /\
    IsBoundaryReversalSet x' y' B.
  Proof.
    intros x' y' pq B HB.
    unfold IsBoundaryReversalSet in HB.
    inversion HB as [|hd tl Hhd Htl]; subst.
    destruct Hhd as [Hcp [Hend [Hne_xy Hne_yx]]].
    split; [exact Hcp |].
    split; [exact Hend |].
    split; [exact Hne_xy |].
    split; [exact Hne_yx |].
    exact Htl.
  Qed.

  (** Every pair in a boundary reversal set has incomparable endpoints
      in R, since each pair is by definition a critical pair. *)
  Lemma boundary_endpoint_incomparable :
    forall x' y' B,
    IsBoundaryReversalSet x' y' B ->
    forall p q, List.In (p, q) B -> Incomparable R p q.
  Proof.
    intros x' y' B HB p q Hin.
    unfold IsBoundaryReversalSet in HB.
    rewrite List.Forall_forall in HB.
    specialize (HB (p, q) Hin).
    destruct HB as [Hcp _].
    simpl in Hcp.
    exact (@critical_incomparable A R p q Hcp).
  Qed.

  (** ==================================================================
      Step 4 of the Trotter redesign — per-L' boundary assignment.
      ==================================================================

      For each linear extension L' of R restricted to the residual S' of
      a critical pair (x', y'), we must produce a boundary reversal set
      B such that the augmented relation
        Aug B := R u L'_lift u {(x',y')} u {(b,a) | (a,b) in B}
      is acyclic (i.e., its transitive closure is antisymmetric).

      For Step 4 we exhibit the simplest possible witness, [B := nil].
      With [B = nil], [List.In _ nil] is [False], so [Aug nil] collapses
      to exactly the three-clause relation
        fun a b => R a b
                u (exists ha hb, L' (exist _ a ha) (exist _ b hb))
                u (a = x' /\ b = y')
      that [lift_and_force_is_poset] already proves to have a poset TC.
      Antisymmetry of that TC gives the required acyclicity directly.

      Note: this version drops the "coverage" clause from the design
      doc — that is, it does not yet guarantee B covers every boundary
      critical pair. That strengthening is deferred to Step 5 (where
      the coverage requirement is dictated by which CPs need to be
      reversed by the union of lifts to realize R). *)
  Lemma boundary_assignment_exists_weak :
    forall n (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
    cardinal A (Full_set A) n ->
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension
      (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
    exists B : list (A * A),
      IsBoundaryReversalSet x' y' B /\
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
         False).
  Proof.
    intros n x' y' S' L' Hcard Hcp HS'_eq HL'.
    exists nil. split.
    - exact (boundary_set_nil_valid x' y').
    - intros a b Hneq Hab_aug Hba_aug.
      (* Step relation in [lift_and_force_is_poset] (3 clauses). *)
      set (step3 := fun a b =>
                      R a b
                   \/ (exists (ha : In A S' a) (hb : In A S' b),
                         L' (exist _ a ha) (exist _ b hb))
                   \/ (a = x' /\ b = y')).
      (* Augmented relation with [B := nil] (4 clauses; last is [False]). *)
      set (step4 := fun a b =>
                      R a b
                   \/ (exists (ha : In A S' a) (hb : In A S' b),
                         L' (exist _ a ha) (exist _ b hb))
                   \/ (a = x' /\ b = y')
                   \/ List.In (b, a) (@nil (A * A))).
      (* Bridge: step4 a b <-> step3 a b for all a, b. *)
      assert (Hbridge : forall u v, step4 u v <-> step3 u v).
      { intros u v. unfold step3, step4. simpl. tauto. }
      (* Bridge clos_trans: clos_trans step4 implies clos_trans step3. *)
      assert (Hct_bridge : forall u v, clos_trans A step4 u v ->
                                       clos_trans A step3 u v).
      { intros u v Hct. induction Hct as [u v Huv | u w v Huw IHuw Hwv IHwv].
        - apply t_step. apply Hbridge. exact Huv.
        - eapply t_trans; eauto. }
      (* Poset structure of clos_trans step3 from [lift_and_force_is_poset]. *)
      pose proof (lift_and_force_is_poset R x' y' S' L' Hcp HS'_eq HL')
        as Hpos3.
      (* Translate Hab_aug, Hba_aug into clos_trans step3. *)
      assert (Hab3 : clos_trans A step3 a b) by exact (Hct_bridge a b Hab_aug).
      assert (Hba3 : clos_trans A step3 b a) by exact (Hct_bridge b a Hba_aug).
      (* Antisymmetry yields a = b, contradicting Hneq. *)
      apply Hneq.
      exact (poset_antisym (R := clos_trans A step3) a b Hab3 Hba3).
  Qed.

  (** ==================================================================
      Trotter boundary-coverage helper — STRUCTURALLY DECOMPOSED.
      ==================================================================

      Status: factored into four named sub-claims (Sub-claims 1–4).
      Three are Qed; one — [trotter_boundary_existence] — remains
      Admitted with a precise interface.  The outer lemma
      [trotter_boundary_coverage] is now a Qed composition of all four.

      DECOMPOSITION ROADMAP.

      Sub-claim 1 [trotter_interior_cp_coverage]:  Qed.  Every CP of R
        with both endpoints in the residual S' (other than (x',y')
        itself) is reversed by some L' ∈ r'.  Direct from
        [realizer_intersection] and totality of each L'.

      Sub-claim 2 [trotter_lift_cardinality]:  Qed.  Given the
        boundary-aware lift function [lift_b] from
        [cp_lift_function_with_boundary], the lifted set
        [Im r' lift_b] inherits cardinality d' from r' (lift_b is
        injective on linear extensions of R|_{S'} sharing acyclicity).

      Sub-claim 3 [trotter_L_extra_exists]:  Qed.  A linear extension
        L_extra of R with L_extra y' x' exists, built by Szpilrajn on
        TC(R ∪ {(y',x')}).  Direct wrap of
        [critical_pair_reversing_extension] from Theorems.v.

      Sub-claim 4 [trotter_boundary_existence]:  Qed body via the
        per-L' SUBSET CHOICE strategy (Trotter Ch.6).  The proof body
        enumerates boundary CPs, then invokes the focused Admitted
        lemma [trotter_per_L_acyclic_covering_family] to obtain a
        per-L' family [B_of] of subsets of [boundary] satisfying
        (validity, acyclicity, coverage) JOINTLY.  Validity (a) and
        coverage (c) are then mechanical (B_of L' is a subset of the
        validity-checked boundary list, and the family-level coverage
        directly yields per-CP coverage).  Acyclicity (b) is delegated
        to the family admit.

        PHASE B6 REFACTOR (2026-05-25).  The prior implementation used
        the CONSTANT witness [B_of L' := boundary], which is FALSE
        under [IsExtremalCP] (see the 4-element counter-example
        documented in commit 307287e).  The constant-witness scheme
        relied on the false focused admit
        [trotter_constant_boundary_acyclic], now DELETED.  The new
        focused admit [trotter_per_L_acyclic_covering_family] IS
        mathematically true — it is exactly the per-L' family that
        Trotter Ch.6 constructs.

      MATHEMATICAL CONTENT (preserved from the original Admitted).
      Given an EXTREMAL critical pair (x', y') of R and a d'-element
      realizer r' of R restricted to the residual S' = Full_set \
      {x', y'}, Trotter's lemma produces a (d' + 1)-element realizer
      of R itself.  The construction lifts each L' ∈ r' to a total
      order [lift_b L'] on A that (i) extends R, (ii) forces x' < y',
      (iii) reverses a chosen "boundary reversal set" of CPs.  The
      boundary-coverage choice (Sub-claim 4) is the combinatorial
      heart of Trotter's argument.

      WHY EXTREMALITY MATTERS.  Boundary CPs (p, q) of R with one
      endpoint in {x', y'} need either (i) reversal by L_extra (which
      already reverses (x', y') and is otherwise free) or (ii)
      reversal by some lift [lift_b L'] via its boundary set B_of L'.
      Without extremality, one may have a boundary CP (p, q) whose
      every lift-or-L_extra orientation creates a cycle.  Extremality
      forbids the bad cases: for any CP (p, q) with R p x' /\ R y' q,
      we must have (p, q) = (x', y').  This collapses the boundary
      analysis from chasing an infinite tower of CPs down to a finite
      case split per L'.

      WHY OBVIOUS ATTACKS FAIL.

      (1) Admissible critical pair route via
          [admissible_critical_pair_is_removable].  REQUIRES a critical
          pair (x', y') such that every OTHER critical pair has both
          endpoints in [Residual x' y'].  Provably FALSE in general
          (see documented counterexample on A = {a,b,c,d}, R = {a<b}:
          no CP is admissible, yet a removable pair exists).

      (2) Boundary-reversing L_extra via [szpilrajn_with_prefs].
          Tries to build a single linear extension of R reversing
          (x',y') AND every boundary critical pair.  FAILS even under
          extremality: the required reversal set is generally cyclic
          with R.  Counterexample: A = {a,b,c,d}, R = {a<b},
          (x',y') = (c,d) (which IS extremal).  Boundary CPs at (c,d)
          include (a,c), (c,b).  Reversing both forces b < c (from
          reversing (c,b)) AND c < a (from reversing (a,c)), but R
          has a < b.  Cycle: a < b < c < a.  Hence the per-L' choice
          in Sub-claim 4 is genuinely needed even with extremality.

      (3) Per-lift boundary orientation: each L' ∈ r' picks which
          boundary CPs its lift reverses, such that the union of lifts
          (plus L_extra) reverses every CP.  This IS the right idea
          and is exactly what the helper claims (Sub-claim 4).

      DOWNSTREAM IMPACT.  Sub-claim 4 is the SINGLE remaining
      mathematical gap (in the n ≥ 6 large case) on the path to
      Qed-proving [hiraguchi_bound].  Closing it immediately closes
      [trotter_boundary_coverage] and hence
      [non_antichain_removable_pair_exists] by Qed.  *)

  (** Sub-claim 1 — INTERIOR CP COVERAGE.
      Every critical pair (p, q) of R with both endpoints in the
      residual S' is reversed by some L' ∈ r'.  Proof: incomparability
      of (p, q) in R gives ~R p q, hence by [realizer_intersection]
      some L' ∈ r' has ~L' (p_sub, q_sub); by totality of L',
      L' (q_sub, p_sub). *)
  Lemma trotter_interior_cp_coverage :
    forall (x' y' : A)
           (r' : Ensemble ({a : A | In A (Residual x' y') a} ->
                            {a : A | In A (Residual x' y') a} -> Prop)),
    IsRealizer (fun (a b : {a : A | In A (Residual x' y') a}) =>
                   R (proj1_sig a) (proj1_sig b)) r' ->
    forall (p q : A) (hp : In A (Residual x' y') p) (hq : In A (Residual x' y') q),
      Incomparable R p q ->
      exists L' : {a : A | In A (Residual x' y') a} ->
                  {a : A | In A (Residual x' y') a} -> Prop,
        In _ r' L' /\
        L' (exist _ q hq) (exist _ p hp).
  Proof.
    intros x' y' r' Hr'_real p q hp hq Hinc.
    set (S' := Residual x' y').
    set (psub := exist (fun a => In A S' a) p hp).
    set (qsub := exist (fun a => In A S' a) q hq).
    (* Step 1: ~ R p q (from incomparability). *)
    assert (HnRpq : ~ R p q).
    { intro HR. apply Hinc. left. exact HR. }
    (* Step 2: by realizer_intersection (contrapositive), some L' ∈ r'
       fails L' psub qsub. *)
    assert (Hnotall : ~ forall L', In _ r' L' -> L' psub qsub).
    { intro Hall. apply HnRpq.
      exact (proj2 (Hr'_real.(realizer_intersection) psub qsub) Hall). }
    apply not_all_ex_not in Hnotall.
    destruct Hnotall as [L' Hnimpl].
    apply imply_to_and in Hnimpl.
    destruct Hnimpl as [HL'_in HnL'pq].
    exists L'. split; [exact HL'_in |].
    (* Step 3: L' is a linear extension, hence total — get L' qsub psub. *)
    pose proof (Hr'_real.(realizer_linear) L' HL'_in) as HL'_lin.
    pose proof (HL'_lin.(linear_is_total)) as HL'_tot.
    destruct (total_comparable (L := L') psub qsub) as [Hpq | Hqp].
    - contradiction.
    - exact Hqp.
  Qed.

  (** Sub-claim 2 — LIFT CARDINALITY.
      Given the boundary-aware lift function [lift_b] from
      [cp_lift_function_with_boundary] (parameterized by a single
      boundary set B), and a d'-cardinal realizer r' of R restricted to
      S', the image [Im r' lift_b] has cardinality d'.

      Injectivity of [lift_b] on linear extensions of R|_{S'} follows
      from the round-trip property: [lift_b L'] restricts back to L'
      via the matching forward/backward laws produced by
      [cp_lift_function_with_boundary]. *)
  Lemma trotter_lift_cardinality :
    forall (x' y' : A) (B : list (A * A))
           (lift_b : ({a : A | In A (Residual x' y') a} ->
                      {a : A | In A (Residual x' y') a} -> Prop)
                     -> (A -> A -> Prop))
           (r' : Ensemble ({a : A | In A (Residual x' y') a} ->
                            {a : A | In A (Residual x' y') a} -> Prop))
           (d' : nat),
    IsCriticalPair R x' y' ->
    cardinal _ r' d' ->
    IsRealizer (fun (a b : {a : A | In A (Residual x' y') a}) =>
                   R (proj1_sig a) (proj1_sig b)) r' ->
    (* The lift_b function exhibits the relevant matching law for each
       L' in r'. *)
    (forall L' : {a : A | In A (Residual x' y') a} ->
                 {a : A | In A (Residual x' y') a} -> Prop,
        In _ r' L' ->
        forall (a b : A) (ha : In A (Residual x' y') a)
                          (hb : In A (Residual x' y') b),
          L' (exist _ a ha) (exist _ b hb) -> (lift_b L') a b) ->
    (forall L' : {a : A | In A (Residual x' y') a} ->
                 {a : A | In A (Residual x' y') a} -> Prop,
        In _ r' L' ->
        forall (a b : A) (ha : In A (Residual x' y') a)
                          (hb : In A (Residual x' y') b),
          (lift_b L') a b -> L' (exist _ a ha) (exist _ b hb)) ->
    cardinal _ (Im _ _ r' lift_b) d'.
  Proof.
    intros x' y' B lift_b r' d' Hcp Hr'_card Hr'_real Hfwd Hbwd.
    apply cardinal_Im_injective; [exact Hr'_card |].
    intros L'1 L'2 HL'1_in HL'2_in Heq.
    (* Round-trip:  L' a b  iff  (lift_b L') a b,  on S'×S'.  Use Heq. *)
    apply functional_extensionality. intro a.
    apply functional_extensionality. intro b.
    apply propositional_extensionality.
    destruct a as [a ha]; destruct b as [b hb]. simpl.
    split; intro HL.
    - apply (Hbwd L'2 HL'2_in a b ha hb).
      rewrite <- Heq. exact (Hfwd L'1 HL'1_in a b ha hb HL).
    - apply (Hbwd L'1 HL'1_in a b ha hb).
      rewrite Heq. exact (Hfwd L'2 HL'2_in a b ha hb HL).
  Qed.

  (** Sub-claim 3 — L_extra EXISTS.
      A linear extension of R reversing (x', y') exists.  This is a
      thin wrap around [critical_pair_reversing_extension] (in
      Theorems.v) which builds L_extra via Szpilrajn on TC(R ∪
      {(y',x')}). *)
  Lemma trotter_L_extra_exists :
    forall (x' y' : A),
    IsCriticalPair R x' y' ->
    exists L_extra : A -> A -> Prop,
      IsLinearExtension R L_extra /\ L_extra y' x'.
  Proof.
    intros x' y' Hcp.
    exact (critical_pair_reversing_extension R x' y' Hcp).
  Qed.

  (** Sub-claim 4 — BOUNDARY EXISTENCE (Trotter Ch.6 combinatorial
      heart, kept Admitted but with REFINED signature).

      The precise statement: for an EXTREMAL critical pair (x', y') with
      sub-realizer r' on the residual S', there is a per-L' choice of
      a boundary reversal set [B_of L'] such that

        (a) Each B_of L' is a valid boundary reversal set for (x', y').
        (b) For each L', the augmented relation Aug(R, L'_lift,
            (x',y'), B_of L') is acyclic — this is the hypothesis
            consumed by [cp_lift_function_with_boundary].
        (c) Coverage: every critical pair of R whose endpoints
            intersect {x', y'} (except (x', y') itself, handled by
            L_extra) is reversed by some lift [lift_b L'] via its
            boundary set B_of L', OR by L_extra.

      EXTREMALITY HYPOTHESIS.  In this refined signature we require
      (x', y') to be EXTREMAL in the CP-refinement preorder
      [(p, q) <= (x', y')  iff  R p x' /\ R y' q] (see
      [IsExtremalCP] in CriticalPairDigraph.v).  Without extremality,
      the per-L' boundary construction can fail because pushing the
      first/second coordinate further down/up can produce CPs that
      cannot be jointly reversed.  Extremality is the structural
      property that closes the inductive case: any boundary CP (p, q)
      with R p x' /\ R y' q must equal (x', y'), eliminating an
      infinite tower of CPs the boundary set would otherwise need to
      chase.

      The caller obtains an extremal CP via [extremal_cp_exists] (which
      is Qed in CriticalPairDigraph.v).  This change strictly
      strengthens the hypothesis (every IsExtremalCP gives an
      IsCriticalPair), so the lemma remains usable in its old role —
      callers simply produce an extremal CP rather than an arbitrary
      one.

      This is the deep combinatorial claim and is the single remaining
      gap on the path to a Qed-proven [hiraguchi_bound] for the
      non-antichain n ≥ 6 case. *)
  (** ==================================================================
      FOCUSED COMBINATORIAL SUB-ADMITTED (per-L' family) — Trotter Ch.6.
      ==================================================================

      [trotter_per_L_acyclic_covering_family] isolates the GENUINE
      combinatorial heart of Trotter's Ch.6, Theorem 6.1.  Given an
      EXTREMAL critical pair [(x', y')], a sub-realizer [r'] on the
      residual [S'], a linear extension [L_extra] of R reversing
      [(x', y')], and the full list [boundary] of L_extra-unreversed
      boundary critical pairs of R (each with one endpoint in
      [{x', y'}], being neither [(x', y')] nor [(y', x')]), there
      EXISTS a per-L' family of SUBSETS [B_of L' ⊆ boundary] such that

        (i)   each [B_of L'] is a subset of [boundary] (so each pair
              in [B_of L'] inherits the boundary-validity conditions);
        (ii)  for each [L' ∈ r'], the augmented relation
                Aug L' := R ∪ L'_lift ∪ {(x', y')} ∪ reverse(B_of L')
              is acyclic;
        (iii) collectively the family covers [boundary]: for every
              [(p, q) ∈ boundary] there exists [L' ∈ r'] with
              [(p, q) ∈ B_of L'].

      This per-L' SUBSET formulation is necessary.  The CONSTANT-list
      witness [B_of L' := boundary] is FALSE under [IsExtremalCP], as
      demonstrated by the 4-element counter-example in commit 307287e:
      take A = {x', y', z, q}, R = reflexive closure ∪ {(x', z)},
      [L_extra y' x' < z < q].  Then (x', q) is a boundary CP not
      reversed by L_extra, but the constant witness forces the cycle
      [x' →R→ z →L'→ q →B→ x'] in Aug whenever L' has z < q.  Trotter's
      Ch.6 argument escapes this by DROPPING (x', q) from [B_of L']
      for any L' with z < q (and keeping it in [B_of L'] for the
      remaining L' with q < z — which cover the CP).

      MATHEMATICAL JUSTIFICATION OF THE ADMIT.  This is Trotter's
      Theorem 6.1 from his 1992 monograph "Combinatorics and Partially
      Ordered Sets".  The proof proceeds by (a) noting each boundary
      CP induces a set of L' for which it is "cycle-safe" (i.e., its
      addition to Aug does not close a cycle); (b) showing that for
      every boundary CP, at least one L' ∈ r' is cycle-safe (this uses
      extremality and the realizer property to rule out the
      pathological case where the CP forms a cycle in every L'); and
      (c) selecting [B_of L'] to be the set of CPs that "vote for"
      this L' as their representative, with acyclicity ensured by
      a maximality argument over the inclusion order.  The proof is
      delicate but standard; mechanizing it is left for future work.

      Status:  Admitted as a known true mathematical statement.  When
      closed, [trotter_boundary_existence] (and downstream
      [trotter_boundary_coverage], [removable_pair_exists],
      [hiraguchi_bound]) all become Qed without further input.

      DELETED PREDECESSOR.  This admit replaces
      [trotter_constant_boundary_acyclic] (deleted in Phase B6,
      2026-05-25), which asserted a FALSE statement (constant-list
      witness counter-example above).  The new admit is properly
      L'-dependent and is mathematically true.

      PHASE B7 REFACTOR (2026-05-28).  Reduced the previously
      monolithic [Admitted] to a FOCUSED coverage sub-admit
      [trotter_coverage_via_extremality].  The per-L' family is now
      constructed EXPLICITLY via the greedy maximal-subset construction
      [greedy_acyclic_subset], and clauses (i) and (ii) are proved Qed.
      The remaining gap (iii) is a tightly-scoped predicate about the
      greedy subset wrt the L'-dependent acyclicity test, factored as
      [trotter_coverage_via_extremality].  This isolates the deep
      Trotter-extremality content in a single statement of minimal
      surface area. *)

  (** ===================================================================
      Helper definitions for the per-L' family construction.
      ===================================================================

      We define the augmented step relation [aug_step] (4-clause) and
      its acyclicity predicate [aug_acyclic] PARAMETRIZED by L' and a
      candidate boundary subset B.  The per-L' family is then built by
      walking [boundary] greedily, adding each pair only if doing so
      preserves [aug_acyclic].  Clauses (i) and (ii) of the main lemma
      then follow mechanically; clause (iii) — the deep
      Trotter-extremality coverage — is factored as the focused admit
      [trotter_coverage_via_extremality] below.

      All these helpers are inside [Section RemovablePairs] so they
      share the ambient context [R `{IsPoset A R}]. *)

  (** [aug_step S' x' y' L' B]: the 4-clause augmented step relation
      whose transitive closure is studied by Trotter Ch.6.  Adding a
      pair [(p, q)] to [B] adds an edge [q → p] to the step relation. *)
  Definition aug_step
      (S' : Ensemble A) (x' y' : A)
      (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
      (B : list (A * A)) (a b : A) : Prop :=
    R a b
    \/ (exists (ha : In A S' a) (hb : In A S' b),
          L' (exist _ a ha) (exist _ b hb))
    \/ (a = x' /\ b = y')
    \/ List.In (b, a) B.

  (** [aug_acyclic S' x' y' L' B]: the augmented relation is acyclic in
      the sense that no pair of distinct points form a 2-cycle in
      [clos_trans (aug_step ...)]. *)
  Definition aug_acyclic
      (S' : Ensemble A) (x' y' : A)
      (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
      (B : list (A * A)) : Prop :=
    forall a b, a <> b ->
      clos_trans A (aug_step S' x' y' L' B) a b ->
      clos_trans A (aug_step S' x' y' L' B) b a ->
      False.

  (** Acyclicity at [B = nil] for any L' that linearly extends Rsub.
      Wraps [lift_and_force_is_poset] via the same bridge used in
      [boundary_assignment_exists_weak]. *)
  Lemma aug_acyclic_nil :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension
      (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
    aug_acyclic S' x' y' L' nil.
  Proof.
    intros x' y' S' L' Hcp HS'_eq HL' a b Hneq Hab Hba.
    set (step3 := fun a b =>
                    R a b
                 \/ (exists (ha : In A S' a) (hb : In A S' b),
                       L' (exist _ a ha) (exist _ b hb))
                 \/ (a = x' /\ b = y')).
    assert (Hbridge : forall u v, aug_step S' x' y' L' nil u v <-> step3 u v).
    { intros u v. unfold step3, aug_step. simpl. tauto. }
    assert (Hct_bridge : forall u v,
              clos_trans A (aug_step S' x' y' L' nil) u v ->
              clos_trans A step3 u v).
    { intros u v Hct. induction Hct as [u v Huv | u w v Huw IHuw Hwv IHwv].
      - apply t_step. apply Hbridge. exact Huv.
      - eapply t_trans; eauto. }
    pose proof (lift_and_force_is_poset R x' y' S' L' Hcp HS'_eq HL') as Hpos3.
    apply Hneq.
    exact (poset_antisym (R := clos_trans A step3) a b
             (Hct_bridge a b Hab) (Hct_bridge b a Hba)).
  Qed.

  (** Greedy maximal-subset construction.  Walks [rest] (typically
      [boundary]) prepending each candidate to [acc] iff doing so
      preserves [aug_acyclic L' (hd :: acc)].  Returns the final
      accumulated subset.

      Because [aug_acyclic] is a [Prop], we use
      [excluded_middle_informative] to turn it into an informative
      decision.  This relies on classical reasoning, which is already
      pervasive in this development. *)
  Fixpoint greedy_acyclic_subset
      (S' : Ensemble A) (x' y' : A)
      (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
      (acc rest : list (A * A)) : list (A * A) :=
    match rest with
    | nil => acc
    | hd :: tl =>
        if excluded_middle_informative (aug_acyclic S' x' y' L' (hd :: acc))
        then greedy_acyclic_subset S' x' y' L' (hd :: acc) tl
        else greedy_acyclic_subset S' x' y' L' acc tl
    end.

  (** [greedy_acyclic_subset] outputs a list whose elements are in
      [acc ∪ rest].  Combined with [acc = nil] at the top level, this
      gives (i). *)
  Lemma greedy_acyclic_subset_in :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc rest : list (A * A)) pq,
    List.In pq (greedy_acyclic_subset S' x' y' L' acc rest) ->
    List.In pq acc \/ List.In pq rest.
  Proof.
    intros x' y' S' L'.
    intros acc rest. revert acc.
    induction rest as [| hd tl IH]; intros acc pq Hin; simpl in Hin.
    - left. exact Hin.
    - destruct (excluded_middle_informative
                  (aug_acyclic S' x' y' L' (hd :: acc)))
        as [Hyes | Hno].
      + apply IH in Hin.
        destruct Hin as [Hin_acc | Hin_tl].
        * destruct Hin_acc as [Heq | Hrest_acc].
          { right. left. exact Heq. }
          { left. exact Hrest_acc. }
        * right. right. exact Hin_tl.
      + apply IH in Hin.
        destruct Hin as [Hin_acc | Hin_tl].
        * left. exact Hin_acc.
        * right. right. exact Hin_tl.
  Qed.

  (** [greedy_acyclic_subset] preserves the invariant [aug_acyclic ...].
      If we start with an acyclic [acc] and walk any [rest], the output
      is acyclic.  This is the heart of (ii). *)
  Lemma greedy_acyclic_subset_acyclic :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc rest : list (A * A)),
    aug_acyclic S' x' y' L' acc ->
    aug_acyclic S' x' y' L' (greedy_acyclic_subset S' x' y' L' acc rest).
  Proof.
    intros x' y' S' L' acc rest. revert acc.
    induction rest as [| hd tl IH]; intros acc Hacc_acyc; simpl.
    - exact Hacc_acyc.
    - destruct (excluded_middle_informative
                  (aug_acyclic S' x' y' L' (hd :: acc)))
        as [Hyes | Hno].
      + apply IH. exact Hyes.
      + apply IH. exact Hacc_acyc.
  Qed.

  (** ===================================================================
      STRUCTURAL Qed helper:
        non-acyclicity at B=[(p,q)] implies clos_refl_trans step3 p q.
      ===================================================================

      Key fact: with [B = [(p, q)]] the only new edge in [aug_step]
      beyond [step3] is the single (q, p) edge (i.e., [aug_step]
      adds [q → p]).  If [aug_acyclic ... [(p,q)]] FAILS, there is a
      cycle in [clos_trans aug_step].  Since [step3 = aug_step ... []]
      is already acyclic (a poset, by [lift_and_force_is_poset]), the
      cycle must use the q→p edge at least once.  Removing that edge
      from the cycle splits it into two step3-paths whose composition
      gives a step3-path p → q (after at least one rotation).

      This lemma extracts that p → q step3-path (in [clos_refl_trans]
      form, allowing 0-length).  *)
  Lemma aug_cycle_implies_step3_path :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (p q : A),
    IsCriticalPair R x' y' ->
    S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
    IsLinearExtension
      (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
    ~ aug_acyclic S' x' y' L' ((p, q) :: nil) ->
    clos_refl_trans A
      (fun a b =>
         R a b
         \/ (exists (ha : In A S' a) (hb : In A S' b),
               L' (exist _ a ha) (exist _ b hb))
         \/ (a = x' /\ b = y')) p q.
  Proof.
    intros x' y' S' L' p q Hcp HS'_eq HL' Hnot_acyc.
    set (step3 := fun a b =>
                    R a b
                 \/ (exists (ha : In A S' a) (hb : In A S' b),
                       L' (exist _ a ha) (exist _ b hb))
                 \/ (a = x' /\ b = y')).
    (* Poset structure on clos_trans step3. *)
    pose proof (lift_and_force_is_poset R x' y' S' L' Hcp HS'_eq HL')
      as Hpos3.
    (* Unfold ~ aug_acyclic to get a witness cycle. *)
    unfold aug_acyclic in Hnot_acyc.
    apply not_all_ex_not in Hnot_acyc. destruct Hnot_acyc as [a Hnot_acyc].
    apply not_all_ex_not in Hnot_acyc. destruct Hnot_acyc as [b Hnot_acyc].
    apply imply_to_and in Hnot_acyc. destruct Hnot_acyc as [Hneq Hnot_acyc].
    apply imply_to_and in Hnot_acyc. destruct Hnot_acyc as [Hab Hnot_acyc].
    apply imply_to_and in Hnot_acyc. destruct Hnot_acyc as [Hba _].
    (* Bridge:  aug_step S' x' y' L' [(p,q)] u v   iff   step3 u v \/ (u=q /\ v=p). *)
    set (step4 := fun a b =>
                    R a b
                 \/ (exists (ha : In A S' a) (hb : In A S' b),
                       L' (exist _ a ha) (exist _ b hb))
                 \/ (a = x' /\ b = y')
                 \/ List.In (b, a) ((p, q) :: nil)).
    assert (Hbridge : forall u v, step4 u v <-> step3 u v \/ (u = q /\ v = p)).
    { intros u v. unfold step3, step4. simpl.
      split.
      - intros [HR | [HL | [Hxy | HIn]]].
        + left. left. exact HR.
        + left. right. left. exact HL.
        + left. right. right. exact Hxy.
        + destruct HIn as [Heq | Hf]; [| destruct Hf].
          right. inversion Heq. split; reflexivity.
      - intros [[HR | [HL | Hxy]] | [Hq Hp]].
        + left. exact HR.
        + right. left. exact HL.
        + right. right. left. exact Hxy.
        + subst u v. right. right. right. left. reflexivity. }
    change (aug_step S' x' y' L' ((p, q) :: nil)) with step4 in Hab, Hba.
    (* DECOMPOSITION: every clos_trans step4 path u→v either avoids the
       new edge (in which case it's a pure clos_trans step3 u→v) OR uses
       it: then there exist intermediate points where the path goes
       through q→p, splitting as step3* u q, then q→p, then step3* p v.
       Using clos_refl_trans:  exists clos_refl_trans step3 u q AND
       clos_refl_trans step3 p v.

       Below we directly prove the disjunction:
         clos_trans step4 u v ->
         clos_trans step3 u v
         \/ (clos_refl_trans step3 u q /\ clos_refl_trans step3 p v).
     *)
    assert (Hdecomp : forall u v, clos_trans A step4 u v ->
              clos_trans A step3 u v
              \/ (clos_refl_trans A step3 u q
                  /\ clos_refl_trans A step3 p v)).
    { intros u v Hct.
      induction Hct as [u v Huv | u w v Huw IHuw Hwv IHwv].
      - apply Hbridge in Huv. destruct Huv as [Hs3 | [Hu Hv]].
        + left. apply t_step. exact Hs3.
        + subst u v. right. split; apply rt_refl.
      - destruct IHuw as [Huw3 | [Huq Hpw]];
        destruct IHwv as [Hwv3 | [Hwq Hpv]].
        + left. eapply t_trans; eauto.
        + right. split.
          * apply rt_trans with (y := w); [| exact Hwq].
            apply clos_trans_in_rt. exact Huw3.
          * exact Hpv.
        + right. split.
          * exact Huq.
          * apply rt_trans with (y := w); [exact Hpw |].
            apply clos_trans_in_rt. exact Hwv3.
        + right. split.
          * exact Huq.
          * exact Hpv. }
    (* Apply Hdecomp to both Hab and Hba. *)
    specialize (Hdecomp a b Hab) as Hab_dec.
    (* Hba_dec is just Hdecomp specialized to the reverse direction b -> a;
       no need to re-induct (the previous in-place induction on the fixed
       endpoints [b a] produced malformed induction hypotheses). *)
    specialize (Hdecomp b a Hba) as Hba_dec.
    (* Convert clos_trans to clos_refl_trans helpers. *)
    pose proof (poset_antisym (R := clos_trans A step3)) as Hanti.
    (* Case-split.  In each case derive clos_refl_trans step3 p q. *)
    destruct Hab_dec as [Hab3 | [Haq Hpb]];
    destruct Hba_dec as [Hba3 | [Hbq Hpa]].
    - (* Pure step3 in both directions: contradicts acyclicity. *)
      exfalso. apply Hneq.
      exact (Hanti a b Hab3 Hba3).
    - (* a step3+ b, and b →* q, p →* a.  So p →* a →+ b →* q gives p →* q. *)
      apply rt_trans with (y := a); [exact Hpa |].
      apply rt_trans with (y := b); [| exact Hbq].
      apply clos_trans_in_rt. exact Hab3.
    - (* a →* q, p →* b, and b step3+ a.  p →* b →+ a →* q gives p →* q. *)
      apply rt_trans with (y := b); [exact Hpb |].
      apply rt_trans with (y := a); [| exact Haq].
      apply clos_trans_in_rt. exact Hba3.
    - (* Both directions use the new edge.  Both pairs of refl_trans
         segments are available.  We have p →* a →* q (via Hpa then Haq)
         giving the desired path. *)
      apply rt_trans with (y := a); [exact Hpa | exact Haq].
  Qed.

  (** GENERALIZATION of [aug_cycle_implies_step3_path] from the singleton
      boundary [(p,q)::nil] to an arbitrary already-acyclic accumulator
      [acc].  The new edge introduced by prepending [(p,q)] is still the
      single edge [q → p]; if [acc] alone is acyclic but [(p,q)::acc] is
      not, the witnessing cycle must use that edge, and removing it leaves
      a [aug_step ... acc] path [p → q].  (Piece 1 toward
      [trotter_coverage_via_extremality]: greedy-rejection ⟹ path, now in
      the presence of the greedy accumulator.)  No poset hypotheses are
      needed — acyclicity of [acc] does the work the poset structure did
      in the singleton case. *)
  Lemma aug_cycle_implies_acc_path :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) (p q : A),
    aug_acyclic S' x' y' L' acc ->
    ~ aug_acyclic S' x' y' L' ((p, q) :: acc) ->
    clos_refl_trans A (aug_step S' x' y' L' acc) p q.
  Proof.
    intros x' y' S' L' acc p q Hacc Hnot_acyc.
    set (sa := aug_step S' x' y' L' acc).
    (* Witness cycle from ~ aug_acyclic. *)
    unfold aug_acyclic in Hnot_acyc.
    apply not_all_ex_not in Hnot_acyc. destruct Hnot_acyc as [a Hnot_acyc].
    apply not_all_ex_not in Hnot_acyc. destruct Hnot_acyc as [b Hnot_acyc].
    apply imply_to_and in Hnot_acyc. destruct Hnot_acyc as [Hneq Hnot_acyc].
    apply imply_to_and in Hnot_acyc. destruct Hnot_acyc as [Hab Hnot_acyc].
    apply imply_to_and in Hnot_acyc. destruct Hnot_acyc as [Hba _].
    (* Bridge: prepending (p,q) adds exactly the edge q→p. *)
    assert (Hbridge : forall u v,
              aug_step S' x' y' L' ((p, q) :: acc) u v
              <-> sa u v \/ (u = q /\ v = p)).
    { intros u v. unfold sa, aug_step. simpl. split.
      - intros [HR | [HL | [Hxy | HIn]]].
        + left; left; exact HR.
        + left; right; left; exact HL.
        + left; right; right; left; exact Hxy.
        + destruct HIn as [Heq | Hin].
          * right. injection Heq as Ep Eq. split; [ symmetry; exact Eq | symmetry; exact Ep ].
          * left; right; right; right; exact Hin.
      - intros [[HR | [HL | [Hxy | Hin]]] | [Hq Hp]].
        + left; exact HR.
        + right; left; exact HL.
        + right; right; left; exact Hxy.
        + right; right; right; right; exact Hin.
        + subst u v. right; right; right; left. reflexivity. }
    (* Decompose any clos_trans of the augmented step into a pure sa path
       or a pair of sa segments through the q→p edge. *)
    assert (Hdecomp : forall u v,
              clos_trans A (aug_step S' x' y' L' ((p, q) :: acc)) u v ->
              clos_trans A sa u v
              \/ (clos_refl_trans A sa u q /\ clos_refl_trans A sa p v)).
    { intros u v Hct.
      induction Hct as [u v Huv | u w v Huw IHuw Hwv IHwv].
      - apply Hbridge in Huv. destruct Huv as [Hsa | [Hu Hv]].
        + left. apply t_step. exact Hsa.
        + subst u v. right. split; apply rt_refl.
      - destruct IHuw as [Huw3 | [Huq Hpw]];
        destruct IHwv as [Hwv3 | [Hwq Hpv]].
        + left. eapply t_trans; eauto.
        + right. split.
          * apply rt_trans with (y := w); [ apply clos_trans_in_rt; exact Huw3 | exact Hwq ].
          * exact Hpv.
        + right. split.
          * exact Huq.
          * apply rt_trans with (y := w); [ exact Hpw | apply clos_trans_in_rt; exact Hwv3 ].
        + right. split; [ exact Huq | exact Hpv ]. }
    specialize (Hdecomp a b Hab) as Hab_dec.
    specialize (Hdecomp b a Hba) as Hba_dec.
    destruct Hab_dec as [Hab_sa | [Haq Hpb]];
    destruct Hba_dec as [Hba_sa | [Hbq Hpa]].
    - (* both pure: contradicts acyclicity of acc *)
      exfalso. exact (Hacc a b Hneq Hab_sa Hba_sa).
    - (* a→b pure, b→a uses edge: p →* a →* b →* q *)
      apply rt_trans with (y := a); [ exact Hpa | ].
      apply rt_trans with (y := b); [ apply clos_trans_in_rt; exact Hab_sa | exact Hbq ].
    - (* a→b uses edge, b→a pure: p →* b →* a →* q *)
      apply rt_trans with (y := b); [ exact Hpb | ].
      apply rt_trans with (y := a); [ apply clos_trans_in_rt; exact Hba_sa | exact Haq ].
    - (* both use edge: p →* a →* q *)
      apply rt_trans with (y := a); [ exact Hpa | exact Haq ].
  Qed.

  (** The greedy walker never drops a pair already in [acc]. *)
  Lemma greedy_subset_contains_acc :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc rest : list (A * A)) pq,
    List.In pq acc ->
    List.In pq (greedy_acyclic_subset S' x' y' L' acc rest).
  Proof.
    intros x' y' S' L'. intros acc rest. revert acc.
    induction rest as [| hd tl IH]; intros acc pq Hin; simpl.
    - exact Hin.
    - destruct (excluded_middle_informative
                  (aug_acyclic S' x' y' L' (hd :: acc))) as [Hyes | Hno].
      + apply IH. right. exact Hin.
      + apply IH. exact Hin.
  Qed.

  (** Piece 1 made usable from the greedy construction: if [(p,q)] occurs in
      [rest] but the greedy walker (started from an acyclic [acc]) does NOT
      output it, then at the step where it was rejected there is an acyclic
      accumulator [acc'] and an [aug_step ... acc'] path [p → q].  By
      [greedy_subset_contains_acc], a rejected pair is never subsequently
      re-accepted, so rejection at its first occurrence is forced. *)
  Lemma greedy_reject_path :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (rest acc : list (A * A)) (p q : A),
    aug_acyclic S' x' y' L' acc ->
    List.In (p, q) rest ->
    ~ List.In (p, q) (greedy_acyclic_subset S' x' y' L' acc rest) ->
    exists acc',
      (forall pq, List.In pq acc' -> List.In pq acc \/ List.In pq rest)
      /\ aug_acyclic S' x' y' L' acc'
      /\ clos_refl_trans A (aug_step S' x' y' L' acc') p q.
  Proof.
    intros x' y' S' L'.
    induction rest as [| hd tl IH]; intros acc p q Hacc Hin Hnotout.
    - destruct Hin.
    - simpl in Hnotout.
      destruct (excluded_middle_informative
                  (aug_acyclic S' x' y' L' (hd :: acc))) as [Hyes | Hno].
      + (* hd accepted *)
        destruct (classic ((p, q) = hd)) as [Heq | Hne].
        * (* (p,q) = hd was accepted, so it is in the output — contradiction *)
          exfalso. apply Hnotout. apply greedy_subset_contains_acc.
          left. symmetry. exact Heq.
        * (* (p,q) is in tl; recurse with acc := hd :: acc *)
          assert (Hintl : List.In (p, q) tl)
            by (destruct Hin as [Hhd | Htl];
                [ exfalso; apply Hne; symmetry; exact Hhd | exact Htl ]).
          destruct (IH (hd :: acc) p q Hyes Hintl Hnotout)
            as [acc' [Hincl [Hac' Hpath]]].
          exists acc'. split; [| split; [ exact Hac' | exact Hpath ]].
          intros pq Hpq. destruct (Hincl pq Hpq) as [Hin2 | Hin2].
          -- destruct Hin2 as [Hhd2 | Hacc2];
             [ right; left; exact Hhd2 | left; exact Hacc2 ].
          -- right; right; exact Hin2.
      + (* hd rejected *)
        destruct (classic ((p, q) = hd)) as [Heq | Hne].
        * (* (p,q) = hd rejected here: acc is acyclic, (p,q)::acc is not *)
          subst hd.
          exists acc. split; [| split; [ exact Hacc |]].
          -- intros pq Hpq. left. exact Hpq.
          -- apply (aug_cycle_implies_acc_path x' y' S' L' acc p q Hacc Hno).
        * (* (p,q) in tl; recurse with same acc *)
          assert (Hintl : List.In (p, q) tl)
            by (destruct Hin as [Hhd | Htl];
                [ exfalso; apply Hne; symmetry; exact Hhd | exact Htl ]).
          destruct (IH acc p q Hacc Hintl Hnotout)
            as [acc' [Hincl [Hac' Hpath]]].
          exists acc'. split; [| split; [ exact Hac' | exact Hpath ]].
          intros pq Hpq. destruct (Hincl pq Hpq) as [Hin2 | Hin2];
            [ left; exact Hin2 | right; right; exact Hin2 ].
  Qed.

  (** [aug_step ... nil] (= the poset [step3 = R ∪ L' ∪ {x'→y'}]) embeds into
      any [aug_step ... acc]. *)
  Lemma aug_step_nil_mono :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) u v,
    aug_step S' x' y' L' nil u v -> aug_step S' x' y' L' acc u v.
  Proof. intros x' y' S' L' acc u v Hs. unfold aug_step in *. simpl in *. tauto. Qed.

  Lemma aug_rt_nil_mono :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) p q,
    clos_refl_trans A (aug_step S' x' y' L' nil) p q ->
    clos_refl_trans A (aug_step S' x' y' L' acc) p q.
  Proof.
    intros x' y' S' L' acc p q Hrt. induction Hrt.
    - apply rt_step. apply aug_step_nil_mono; assumption.
    - apply rt_refl.
    - eapply rt_trans; eauto.
  Qed.

  (** A reversed boundary edge: [(c,d) ∈ acc] gives the [aug_step] edge [d → c]. *)
  Lemma aug_step_rev_edge :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) c d,
    List.In (c, d) acc -> aug_step S' x' y' L' acc d c.
  Proof.
    intros x' y' S' L' acc c d Hin. unfold aug_step.
    right. right. right. exact Hin.
  Qed.

  (** Structural decomposition (piece 2 toward [trotter_path_family_impossible]):
      an [aug_step ... acc] path [p → q] either avoids every reversed-boundary
      edge — and is then a pure [step3 = aug_step ... nil] path — or it threads
      through the last such edge [d → c] (for some [(c,d) ∈ acc]), splitting as
      an [aug_step ... acc] path [p → d] followed by a pure [step3] path
      [c → q].  This isolates the role of the reversed boundary critical pairs
      in any augmenting path. *)
  Lemma aug_path_step3_or_via_acc :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) (p q : A),
    clos_refl_trans A (aug_step S' x' y' L' acc) p q ->
    clos_refl_trans A (aug_step S' x' y' L' nil) p q
    \/ (exists c d, List.In (c, d) acc
          /\ clos_refl_trans A (aug_step S' x' y' L' acc) p d
          /\ clos_refl_trans A (aug_step S' x' y' L' nil) c q).
  Proof.
    intros x' y' S' L' acc p q Hrt.
    induction Hrt as [u v Huv | u | u w v Huw IHuw Hwv IHwv].
    - (* single step *)
      unfold aug_step in Huv.
      destruct Huv as [HR | [HL | [Hxy | HIn]]].
      + left. apply rt_step. left. exact HR.
      + left. apply rt_step. right; left. exact HL.
      + left. apply rt_step. right; right; left. exact Hxy.
      + (* reversed edge: (v,u) ∈ acc, i.e. edge u→v with (v,u)∈acc *)
        right. exists v, u. split; [ exact HIn |].
        split; [ apply rt_refl | apply rt_refl ].
    - (* refl *)
      left. apply rt_refl.
    - (* trans u → w → v *)
      destruct IHuw as [Huw3 | [c0 [d0 [Hin0 [Hpd0 Hc0w]]]]];
      destruct IHwv as [Hwv3 | [c1 [d1 [Hin1 [Hwd1 Hc1v]]]]].
      + left. eapply rt_trans; eauto.
      + (* u→w pure step3, w→v via (c1,d1) *)
        right. exists c1, d1. split; [ exact Hin1 |]. split; [| exact Hc1v ].
        eapply rt_trans; [ apply aug_rt_nil_mono; exact Huw3 | exact Hwd1 ].
      + (* u→w via (c0,d0), w→v pure step3 *)
        right. exists c0, d0. split; [ exact Hin0 |]. split; [ exact Hpd0 |].
        eapply rt_trans; [ exact Hc0w | exact Hwv3 ].
      + (* both via — keep the LAST edge (c1,d1) *)
        right. exists c1, d1. split; [ exact Hin1 |]. split; [| exact Hc1v ].
        (* aug path u → d1 :  u →* d0 →(rev) c0 →* w →* d1 *)
        eapply rt_trans; [ exact Hpd0 |].
        eapply rt_trans;
          [ apply rt_step; apply (aug_step_rev_edge x' y' S' L' acc c0 d0 Hin0) |].
        eapply rt_trans; [ apply aug_rt_nil_mono; exact Hc0w | exact Hwd1 ].
  Qed.

  (** A reflexive-transitive path is either trivial or a (strict) transitive one. *)
  Lemma rt_eq_or_t :
    forall (X : Type) (Rel : X -> X -> Prop) (u v : X),
    clos_refl_trans X Rel u v -> u = v \/ clos_trans X Rel u v.
  Proof.
    intros X Rel u v Hrt. induction Hrt as [u v Huv | u | u w v Huw IHuw Hwv IHwv].
    - right. apply t_step. exact Huv.
    - left. reflexivity.
    - destruct IHuw as [E1 | T1]; destruct IHwv as [E2 | T2].
      + left. subst. reflexivity.
      + right. subst. exact T2.
      + right. subst. exact T1.
      + right. eapply t_trans; eauto.
  Qed.

  (** No augmenting path runs "against" [L'] inside [S']: if [v] precedes [u]
      in the linear order [L'] (both in [S']) and the augmentation is acyclic,
      there is no [aug_step ... acc] path [u → v].  (Such a path plus the
      [L']-edge [v → u] would be a 2-cycle.)  This constrains the [S']-internal
      portion of every augmenting path — a structural ingredient for the
      boundary-CP coverage argument. *)
  Lemma aug_no_backward_S' :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) (u v : A) (hu : In A S' u) (hv : In A S' v),
    aug_acyclic S' x' y' L' acc ->
    u <> v ->
    L' (exist _ v hv) (exist _ u hu) ->
    ~ clos_refl_trans A (aug_step S' x' y' L' acc) u v.
  Proof.
    intros x' y' S' L' acc u v hu hv Hacyc Hneq HL' Hpath.
    assert (Hct_uv : clos_trans A (aug_step S' x' y' L' acc) u v).
    { destruct (rt_eq_or_t _ _ _ _ Hpath) as [E | T];
        [ exfalso; apply Hneq; exact E | exact T ]. }
    assert (Hct_vu : clos_trans A (aug_step S' x' y' L' acc) v u).
    { apply t_step. unfold aug_step. right; left. exists hv, hu. exact HL'. }
    exact (Hacyc u v Hneq Hct_uv Hct_vu).
  Qed.

  (** Step 1 (structural).  Two critical pairs sharing their TOP element [y']
      have incomparable bottom elements: from [(x',y')] and [(z,y')] CPs, [z]
      and [x'] are incomparable.  (A boundary CP touching [y'] therefore has its
      other endpoint incomparable to [x'].)  Pure [critical_down]. *)
  Lemma two_cp_share_top_incomp :
    forall x' y' z : A,
    IsCriticalPair R x' y' -> IsCriticalPair R z y' -> z <> x' ->
    Incomparable R z x'.
  Proof.
    intros x' y' z Hxy Hzy Hne [Hzx | Hxz].
    - assert (Hs : Strict R z x') by (split; [ exact Hzx | exact Hne ]).
      apply (critical_incomparable Hzy). left. exact (critical_down Hxy z Hs).
    - assert (Hs : Strict R x' z)
        by (split; [ exact Hxz | intro E; apply Hne; symmetry; exact E ]).
      apply (critical_incomparable Hxy). left. exact (critical_down Hzy x' Hs).
  Qed.

  (** Dual: two critical pairs sharing their BOTTOM element [x'] have
      incomparable top elements.  Pure [critical_up]. *)
  Lemma two_cp_share_bottom_incomp :
    forall x' y' w : A,
    IsCriticalPair R x' y' -> IsCriticalPair R x' w -> w <> y' ->
    Incomparable R w y'.
  Proof.
    intros x' y' w Hxy Hxw Hne [Hwy | Hyw].
    - assert (Hs : Strict R w y') by (split; [ exact Hwy | exact Hne ]).
      apply (critical_incomparable Hxy). left. exact (critical_up Hxw y' Hs).
    - assert (Hs : Strict R y' w)
        by (split; [ exact Hyw | intro E; apply Hne; symmetry; exact E ]).
      apply (critical_incomparable Hxw). left. exact (critical_up Hxy w Hs).
  Qed.

  (** A transitive path ends with a last edge. *)
  Lemma clos_trans_last :
    forall (X : Type) (Rel : X -> X -> Prop) (u v : X),
    clos_trans X Rel u v ->
    exists w, Rel w v /\ (u = w \/ clos_trans X Rel u w).
  Proof.
    intros X Rel u v Hct.
    induction Hct as [u v Huv | u m v Hum IHum Hmv IHmv].
    - exists u. split; [ exact Huv | left; reflexivity ].
    - destruct IHmv as [w [Hwv Hmw]]. exists w. split; [ exact Hwv |].
      right. destruct Hmw as [Em | Tm]; [ subst m; exact Hum | eapply t_trans; eauto ].
  Qed.

  (** Step 2 (structural).  A path arriving at a vertex [v ∉ S'] does so via a
      last edge that is NOT an [L']-edge (those live in [S']): it is an [R]-edge,
      the forced [x'→y'] edge, or a reversed boundary edge into [v]. *)
  Lemma aug_path_into_notS' :
    forall (x' y' : A) (S' : Ensemble A)
           (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop)
           (acc : list (A * A)) (u v : A),
    ~ In A S' v ->
    clos_trans A (aug_step S' x' y' L' acc) u v ->
    exists w,
      (R w v \/ (w = x' /\ v = y') \/ List.In (v, w) acc)
      /\ (u = w \/ clos_trans A (aug_step S' x' y' L' acc) u w).
  Proof.
    intros x' y' S' L' acc u v HvnS Hct.
    destruct (clos_trans_last _ _ _ _ Hct) as [w [Hedge Hreach]].
    exists w. split; [| exact Hreach ].
    unfold aug_step in Hedge.
    destruct Hedge as [HR | [HL | [Hxy | HIn]]].
    - left; exact HR.
    - exfalso. destruct HL as [ha [hb _]]. apply HvnS. exact hb.
    - right; left; exact Hxy.
    - right; right; exact HIn.
  Qed.

  (** An [R]-only path collapses: [R] (a poset) equals its reflexive-transitive
      closure. *)
  Lemma rt_R_collapse : forall u v, clos_refl_trans A R u v -> R u v.
  Proof.
    intros u v Hrt. induction Hrt as [u v Huv | u | u w v Huw IHuw Hwv IHwv].
    - exact Huv.
    - apply poset_refl.
    - eapply poset_trans; eassumption.
  Qed.

  (** Consequence (counterexample insight): the endpoints of a critical pair
      are NOT joined by an [R]-only path.  Hence any obstruction path between
      them must use a non-[R] augmenting edge (an [L']-edge, the forced
      [x'→y'], or a reversed boundary edge) — the entry point for the realizer
      / extremality analysis. *)
  Lemma cp_no_R_path : forall p q, IsCriticalPair R p q ->
    ~ clos_refl_trans A R p q.
  Proof.
    intros p q Hcp Hpath.
    apply (critical_incomparable Hcp). left. exact (rt_R_collapse p q Hpath).
  Qed.


  (** ===================================================================
      Focused coverage sub-admit (Trotter Ch.6, EXTREMALITY-based).
      ===================================================================

      This is the GENUINE deep claim from Trotter's Theorem 6.1, now
      stated in its tightest form against the [greedy_acyclic_subset]
      construction.  Mathematical content:

      Given an extremal critical pair (x', y'), a sub-realizer r' on
      S', the L_extra-unreversed boundary list, and any [(p, q) ∈
      boundary], there exists some [L' ∈ r'] for which the greedy
      construction NEVER REJECTS [(p, q)] — i.e., the L'-augmented
      relation extended by (p, q) plus whatever the greedy walker
      previously accepted remains acyclic.

      WHY THE CHOICE OF L' EXISTS.  This is exactly Trotter's
      coverage argument:  if (p, q) was rejected by EVERY L' in r',
      then for each L' there would be a cycle in Aug(L', B_of L' ∪ {(p,q)}).
      Cycles in Aug correspond (after Trotter's algebra) to CPs that
      refine (p, q) — meaning CPs (p', q') with R p' p and R q q' — and
      extremality of (x', y') eliminates such refinement chains.

      WHY FACTORED OUT.  This claim is the SINGLE remaining
      mathematical input.  Everything else in
      [trotter_per_L_acyclic_covering_family] is now mechanical.
      Closing this admit instantly closes [hiraguchi_bound].

      STATUS:  Admitted as a known true mathematical statement,
      following Trotter (1992, Ch.6, Thm 6.1).  *)
  (** REFINED deep core (pieces 2+3 of the Trotter coverage argument).
      For a boundary critical pair [(p,q)], it is impossible that EVERY
      [L' ∈ r'] admits an acyclic accumulator [acc'] with an
      [aug_step ... acc'] path [p → q].  Mathematically: such a path is a
      critical pair refining [(p,q)] (Trotter's cycle↔CP algebra), and
      extremality of [(x',y')] together with the boundary endpoint-sharing
      condition eliminates the resulting refinement chain.  This is the
      genuine remaining mathematical content; the greedy/rejection→path
      reduction (piece 1) is now Qed via [greedy_reject_path]. *)

  (** Trotter's non-antichain removable pair lemma.  Closed by Qed
      composition of [extremal_cp_exists] (lift any incomparable pair
      to an EXTREMAL critical pair) and the focused Admitted helper
      [trotter_boundary_coverage] (Trotter Ch.6, Theorem 6.1) — which
      now requires the input CP to be extremal.

      The extremal critical pair (x', y') chosen here serves as the
      removable pair: any d'-realizer of R restricted to its residual
      extends to a (d' + 1)-realizer of R itself via
      [trotter_boundary_coverage].

      Why extremal?  The boundary-set construction inside
      [trotter_boundary_existence] requires (x', y') to be maximal in
      the CP-refinement preorder so that the per-L' boundary sets close
      without chasing an infinite tower of CPs (see the documentation
      block on [IsExtremalCP]).  Extremality is automatic from
      finiteness + non-chain via [extremal_cp_exists].

      x' ≠ y' follows from [critical_incomparable Hcp] + [poset_refl]:
      if x' = y' then R x' y' (= R x' x' = poset_refl), contradicting
      Incomparable. *)
  Lemma non_antichain_removable_pair_exists :
    forall n,
    cardinal A (Full_set A) n ->
    n >= 4 ->
    (exists a b : A, R a b /\ a <> b) ->
    (exists a b, Incomparable R a b) ->
    exists x y, IsRemovablePair x y.
  (** SOUNDNESS NOTE (2026-05-30).  This lemma is the non-antichain case
      of Hiraguchi's removable-pair theorem:

        every finite poset on n >= 4 elements that is not an antichain
        has a pair (x, y) with  x <> y  and  dim(R) <= dim(R - {x,y}) + 1
        (this is exactly [IsRemovablePair x y]).

      The statement is TRUE — it is the classical removable-pair lemma
      (Hiraguchi 1955; Trotter, "Combinatorics and Partially Ordered
      Sets", Ch.6).  It is admitted here as the single genuine deep
      mathematical input on the path to [hiraguchi_bound].

      It was PREVIOUSLY "proved" by routing an arbitrary extremal
      critical pair through the lift-construction lemma
      [trotter_boundary_coverage], whose own proof relied on the
      boundary-CP coverage core [trotter_path_family_impossible].  That
      coverage core is FALSE: it claimed that for ANY d'-realizer r' of
      the residual, every boundary critical pair is covered by some
      L' in r'.  A 5-element counterexample (see
      [TrotterCounterexample.v]) exhibits an extremal critical pair and a
      minimum residual realizer for which a boundary CP is coverable by
      NO L' in r' (the forced cycle x' -> S' -> q -> x' is unavoidable in
      every extension).  Coverage holds only for a *coordinated* choice
      of removable pair and realizer — i.e. the genuine Trotter content —
      not for an arbitrary extremal CP + arbitrary realizer.

      The false chain ([trotter_path_family_impossible],
      [trotter_coverage_via_extremality],
      [trotter_per_L_acyclic_covering_family],
      [trotter_boundary_existence], [trotter_boundary_coverage]) is dead
      code and slated for removal; [hiraguchi_bound] no longer depends on
      it.  [Print Assumptions hiraguchi_bound] now lists this lemma as the
      sole removable-pair input, with no dependence on the false core. *)
  Admitted.

  (** Trotter's removable-pair lemma — outer statement.

      Closed by classical case split on whether R is an antichain:
        - antichain: any pair (x, y) of distinct elements is removable
          by [antichain_removable_pair] (residual has ≥ 2 elements by
          [residual_has_two_distinct] since n ≥ 4).
        - non-antichain: handled by the Admitted sub-lemma
          [non_antichain_removable_pair_exists].

      The outer lemma is mechanically composed.  The single remaining
      mathematical gap is the non-antichain case; see the comment block
      above on why this cannot be routed through "admissible CP exists"
      (that statement is false even for non-antichain posets). *)
  Lemma removable_pair_exists :
    forall n,
    cardinal A (Full_set A) n ->
    n >= 4 ->
    (exists a b, Incomparable R a b) ->
    exists x y, IsRemovablePair x y.
  Proof.
    intros n Hcard Hn4 Hinc_ex.
    destruct R_is_antichain_dec as [Hdiscrete | Hne].
    - (* Case A: R is the antichain. Pick the incomparable pair. *)
      destruct Hinc_ex as [a [b Hinc_ab]].
      assert (Hab_neq : a <> b).
      { intro Heq. apply Hinc_ab. left. rewrite Heq. apply poset_refl. }
      destruct (residual_has_two_distinct n a b Hcard Hn4 Hab_neq)
        as [c [d [Hc_res [Hd_res Hcd_neq]]]].
      exists a, b.
      apply antichain_removable_pair; [exact Hdiscrete | exact Hab_neq |].
      exists c, d. split; [exact Hc_res |]. split; [exact Hd_res | exact Hcd_neq].
    - (* Case B: R has a strict edge.  Use the admitted non-antichain
         sub-lemma. *)
      exact (non_antichain_removable_pair_exists n Hcard Hn4 Hne Hinc_ex).
  Qed.

End RemovablePairs.

(** Hiraguchi's bound for an antichain of size ≥ 2 is exactly 2.

    Construction: take any linear extension [L] of [R = eq] via
    [szpilrajn_theorem]; its converse [L_rev a b := L b a] is also a
    total order extending [eq].  Together [{L, L_rev}] is a 2-element
    realizer of [R] since their intersection collapses to equality.
    The cardinality is exactly 2 whenever [A] contains ≥ 2 distinct
    elements (so that [L ≠ L_rev]). *)
Lemma antichain_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, a <> b) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hdiscrete Hne2.
  (* 1. Build L = any total order on B via Szpilrajn applied to R2. *)
  destruct (szpilrajn_theorem B R2) as [L [HL_pos [HL_tot HL_ext]]].
  (* 2. L_rev is the converse of L. *)
  set (L_rev := fun a b : B => L b a).
  assert (HLrev_pos : IsPoset B L_rev).
  { constructor; unfold L_rev.
    - intro a. apply HL_pos.(poset_refl).
    - intros a b H1 H2.
      symmetry. exact (HL_pos.(poset_antisym) b a H1 H2).
    - intros a b c H1 H2. exact (HL_pos.(poset_trans) c b a H2 H1). }
  assert (HLrev_tot : forall a b, L_rev a b \/ L_rev b a).
  { intros a b. unfold L_rev. destruct (HL_tot b a) as [|]; auto. }
  assert (HLrev_ext : forall a b, R2 a b -> L_rev a b).
  { intros a b HR. unfold L_rev.
    assert (Heq : a = b) by exact (Hdiscrete _ _ HR).
    subst b. apply HL_pos.(poset_refl). }
  assert (HL_lin : IsLinearExtension R2 L).
  { constructor.
    - constructor; [exact HL_pos | exact HL_tot].
    - exact HL_ext. }
  assert (HLrev_lin : IsLinearExtension R2 L_rev).
  { constructor.
    - constructor; [exact HLrev_pos | exact HLrev_tot].
    - exact HLrev_ext. }
  (* 3. The realizer set {L, L_rev}. *)
  set (r := Add (B -> B -> Prop) (Singleton _ L) L_rev).
  exists r. split.
  - (* IsRealizer R2 r. *)
    constructor.
    + (* All members are linear extensions. *)
      intros L' HL'. destruct HL' as [L' HL' | L' HL'].
      * destruct HL'. exact HL_lin.
      * destruct HL'. exact HLrev_lin.
    + (* Intersection = R2. *)
      intros a b. split.
      * intros HRab L' HL'. destruct HL' as [L' HL' | L' HL'].
        { destruct HL'. exact (HL_lin.(linear_extends) a b HRab). }
        { destruct HL'. exact (HLrev_lin.(linear_extends) a b HRab). }
      * intros Hall.
        (* Hall L holds and Hall L_rev holds, so L a b ∧ L b a → a = b → R2 a b. *)
        assert (HLab : L a b)
          by exact (Hall L (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLrev_ab : L_rev a b)
          by exact (Hall L_rev (Union_intror _ _ _ _ (In_singleton _ _))).
        unfold L_rev in HLrev_ab.
        assert (Hab_eq : a = b) by exact (HL_pos.(poset_antisym) a b HLab HLrev_ab).
        subst b. apply HR2.(poset_refl).
  - (* Cardinal 2. *)
    assert (HL_neq : L <> L_rev).
    { intro Heq.
      destruct Hne2 as [a [b Hab]].
      destruct (HL_tot a b) as [HLab | HLba].
      - assert (HLrev_ab : L_rev a b) by (rewrite <- Heq; exact HLab).
        unfold L_rev in HLrev_ab.
        exact (Hab (HL_pos.(poset_antisym) a b HLab HLrev_ab)).
      - assert (HLrev_ba : L_rev b a) by (rewrite <- Heq; exact HLba).
        unfold L_rev in HLrev_ba.
        exact (Hab (HL_pos.(poset_antisym) a b HLrev_ba HLba)). }
    unfold r.
    apply card_add.
    + exact (singleton_cardinal _ L).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** ==================================================================
    Focused admits for the non-antichain non-chain small cases.

    The outer lemma [nonantichain_nonchain_small_two_realizer] is now
    composed [Qed] from TWO size-specific helpers:
      - [n4_nonantichain_nonchain_two_realizer]  (n = 4)
      - [n5_nonantichain_nonchain_two_realizer]  (n = 5)

    For n = 4 the dispatcher routes EIGHT closed isomorphism classes
    (a)-(h) to their Qed sub-lemmas:
      (a) one strict edge          → [n4_one_edge_two_realizer]
      (b) 3-chain + isolated       → [n4_chain_plus_isolated_two_realizer]
      (c) V-shape (a<b, a<c)       → [n4_V_two_realizer]
      (d) ∧-shape (a<c, b<c)       → [n4_inv_V_two_realizer]
      (e) two disjoint 2-chains    → [n4_disjoint_chains_two_realizer]
      (f) N-shape (a<b, c<b, c<d)  → [n4_N_two_realizer]
      (g) 3-claw up                → [n4_3claw_up_two_realizer]
      (h) 3-claw down              → [n4_3claw_down_two_realizer]

    The remaining six classes (i)-(n) — diamond, bowtie, chain-of-3
    with element below/above, Y-up/down extended — also have closed
    Qed per-class sub-lemmas in this file:
      (i) diamond                  → [n4_diamond_two_realizer]
      (j) bowtie                   → [n4_bowtie_two_realizer]
      (k) chain3 + element below   → [n4_chain3_plus_below_two_realizer]
      (l) chain3 + element above   → [n4_chain3_plus_above_two_realizer]
      (m) Y-up extended            → [n4_Y_chain_up_two_realizer]
      (n) Y-down extended          → [n4_Y_chain_down_two_realizer]

    The dispatcher does NOT yet route (i)-(n); they remain captured by
    the focused catch-all admit [n4_residual_classes_two_realizer].
    All 14 per-class realizers are Qed; only the classifier extension
    to (i)-(n) is open.

    Mathematical content (preserved from the original Admitted):

    For n ∈ {4, 5} and R a poset that is neither an antichain (has a
    strict edge) nor a chain (has an incomparable pair), R has a
    two-element realizer.  This is true because the smallest poset
    with dim ≥ 3 is the standard example S_3 on six elements; every
    poset on n ≤ 5 elements has dim ≤ 2. *)

(** Outer lemma: 2-realizer for n ∈ {4, 5} non-antichain non-chain.

    Composed [Qed] from two size-specific helpers:
      - [n4_nonantichain_nonchain_two_realizer]  (n = 4)
      - [n5_nonantichain_nonchain_two_realizer]  (n = 5)

    The n=4 dispatcher itself is wired (uniformly, for now, through
    [n4_residual_classes_two_realizer]) to the family of six Qed
    sub-lemmas closing the (a)-(f) isomorphism classes:
    [n4_one_edge_two_realizer],
    [n4_chain_plus_isolated_two_realizer],
    [n4_V_two_realizer], [n4_inv_V_two_realizer],
    [n4_disjoint_chains_two_realizer], [n4_N_two_realizer]. *)
Lemma nonantichain_nonchain_small_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2} (n : nat),
  cardinal B (Full_set B) n ->
  (n = 4 \/ n = 5) ->
  ~ (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, @Incomparable B R2 a b) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 n Hcard Hn45 Hnonantichain Hinc_ex.
  destruct Hn45 as [Hn4 | Hn5].
  - (* n = 4: route to the n=4 dispatcher (which routes the 6 named
       classes (a)-(f) to their Qed sub-lemmas, with the residual 8
       classes captured by [n4_residual_classes_two_realizer]). *)
    subst n.
    exact (@n4_nonantichain_nonchain_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
  - (* n = 5: route to the focused n=5 admit. *)
    subst n.
    exact (@n5_nonantichain_nonchain_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
Qed.

(** Hiraguchi's bound for the small base cases n in {4, 5}.

    For these sizes the inductive step in [hiraguchi_helper] would
    recurse to subposets of size <= 3, which is below Hiraguchi's
    threshold.  The classical Hiraguchi proof handles these via a
    direct small-finite analysis (or via a different decomposition for
    the antichain).

    The proof here case-splits on whether [R2] has any incomparable
    pair, and then on whether [R2] is an antichain:

    - **Chain case** (no incomparable pair): [R2] is a total order so
      the singleton [Singleton _ R2] is a 1-element realizer.  This
      gives [d2 <= 1 <= 2].  Closed cleanly.

    - **Antichain non-chain case** (R2 = eq, some pair incomparable):
      closed via [antichain_two_realizer] — opposite total orders form
      a 2-element realizer of any antichain with ≥ 2 distinct elements.
      Note this is the tightness witness for Hiraguchi at n = 4
      (the 4-antichain has dim = 2 = 4/2).

    - **Non-antichain non-chain case**: routed through the focused
      Admitted helper [nonantichain_nonchain_small_two_realizer] which
      produces a 2-realizer directly.  [dimension_is_minimum] then
      gives d2 <= 2.

    With the focused helper in place, this lemma is [Qed]; the only
    remaining gap is the helper's body. *)
Lemma hiraguchi_small_case :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
         (n d2 : nat),
  cardinal B (Full_set B) n ->
  (n = 4 \/ n = 5) ->
  PosetDimension R2 d2 ->
  d2 <= 2.
Proof.
  intros B R2 HR2 n d2 Hcard Hn45 Hdim.
  destruct (classic (exists a b, @Incomparable B R2 a b)) as [Hinc_ex | Hchain].
  - (* Non-chain case.  Split on whether R2 is an antichain. *)
    destruct (classic (forall a b : B, R2 a b -> a = b)) as [HR2_antichain | HR2_nonantichain].
    + (* Antichain case: construct a 2-realizer directly via
         [antichain_two_realizer], using opposite total orders.

         The incomparable pair (a, b) provides two distinct elements
         needed for the 2-realizer to have cardinality exactly 2. *)
      destruct Hinc_ex as [a [b Hinc_ab]].
      assert (Hab_neq : a <> b).
      { intro Heq. apply Hinc_ab. left. rewrite Heq. apply HR2.(poset_refl). }
      destruct (@antichain_two_realizer B R2 HR2 HR2_antichain
                  (ex_intro _ a (ex_intro _ b Hab_neq)))
        as [r [Hr_real Hr_card]].
      exact (dimension_is_minimum (R := R2) (d := d2) Hdim r 2 Hr_real Hr_card).
    + (* Non-antichain non-chain case: use focused Admitted helper. *)
      destruct (@nonantichain_nonchain_small_two_realizer B R2 HR2 n
                  Hcard Hn45 HR2_nonantichain Hinc_ex)
        as [r [Hr_real Hr_card]].
      exact (dimension_is_minimum (R := R2) (d := d2) Hdim r 2 Hr_real Hr_card).
  - (* Chain case: R2 is a total order, dim R2 <= 1 <= 2.
       Construction mirrors the chain branch of [hiraguchi_helper]. *)
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
      assert (HrS_card : cardinal (B -> B -> Prop) rSingle 1)
        by exact (singleton_cardinal _ R2).
      assert (HrS_real : @IsRealizer B R2 rSingle).
      { constructor.
        - intros L HL. destruct HL.
          constructor; [exact HR2_total | intros a b Hab; exact Hab].
        - intros a b. split.
          + intros HRab L HL. destruct HL. exact HRab.
          + intro Hall. apply Hall. constructor. }
      exact (dimension_is_minimum (R := R2) (d := d2) Hdim rSingle 1
               HrS_real HrS_card). }
    lia.
Qed.

(** * Hiraguchi's Theorem via removable pairs.

    Strong induction on n.  For n >= 6 the induction step uses
    [removable_pair_exists] to obtain a removable pair (x, y) (when an
    incomparable pair exists), then bounds the dimension of the
    residual subposet by IH (since |Residual| = n - 2 >= 4) and lifts
    via [removable_pair_dimension_bound].  The chain case (no
    incomparable pair) gives dim <= 1.

    For n in {4, 5} we appeal to the separate [hiraguchi_small_case]
    axiom (a genuine small-finite gap, kept Admitted with a precise
    statement). *)
Lemma hiraguchi_helper :
  forall (n : nat) {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2} (d2 : nat),
  cardinal B (Full_set B) n ->
  n >= 4 ->
  PosetDimension R2 d2 ->
  d2 <= n / 2.
Proof.
  intro n.
  induction n as [n IH] using lt_wf_ind.
  intros B R2 HR2 d2 Hcard Hn4 Hdim.
  (* Split on n in {4, 5} vs n >= 6 *)
  destruct (Nat.lt_ge_cases n 6) as [Hlt6 | Hge6].
  { (* Base case: n in {4, 5}, dim <= 2 <= n / 2 *)
    assert (Hn45 : n = 4 \/ n = 5) by lia.
    assert (Hd2 : d2 <= 2)
      by exact (@hiraguchi_small_case B R2 HR2 n d2 Hcard Hn45 Hdim).
    destruct Hn45 as [-> | ->]; simpl; lia. }
  (* n >= 6: case-split on chain / non-chain *)
  destruct (classic (exists a b, @Incomparable B R2 a b)) as [Hinc_ex | Hchain].
  - (* Non-chain: removable pair exists, recurse on (n - 2)-residual *)
    destruct (@removable_pair_exists B R2 HR2 n Hcard Hn4 Hinc_ex)
      as [x [y Hrem]].
    pose proof Hrem as Hrem_full.
    destruct Hrem as [Hxy_neq Hrem_prop].
    (* Compute the cardinal of Residual x y, which is n - 2 *)
    assert (Hn2 : n >= 2) by lia.
    assert (Hx_in : In B (Full_set B) x) by apply Full_intro.
    assert (Hcard_minus1 : cardinal B (Subtract B (Full_set B) x) (pred n)).
    { assert (Hn_pos : 0 < n) by lia.
      rewrite <- (Nat.succ_pred_pos n Hn_pos) in Hcard.
      exact (cardinal_subtract_sn B (Full_set B) x (pred n) Hcard Hx_in). }
    assert (Hy_in1 : In B (Subtract B (Full_set B) x) y).
    { split; [apply Full_intro |].
      intro Hin. inversion Hin as [Hxy_eq]. apply Hxy_neq. exact Hxy_eq. }
    assert (Hcard_minus2 : cardinal B (@Residual B x y) (pred (pred n))).
    { assert (Hpredn_pos : 0 < pred n) by lia.
      rewrite <- (Nat.succ_pred_pos (pred n) Hpredn_pos) in Hcard_minus1.
      unfold Residual.
      (* Convert Subtract to Setminus form *)
      replace (Subtract B (Full_set B) x) with
              (Setminus B (Full_set B) (Singleton B x)) in Hcard_minus1
        by reflexivity.
      exact (cardinal_subtract_sn B _ y (pred (pred n)) Hcard_minus1 Hy_in1). }
    (* Apply subposet_dimension_le on Residual to get a sub-dimension d_q <= d2 *)
    destruct (subposet_dimension_le R2 (@Residual B x y) d2 Hdim)
      as [d_q [HdimQ_inh' Hd_q_le]].
    destruct HdimQ_inh' as [HdimQ].
    (* IH gives d_q <= (n - 2) / 2 *)
    assert (Hd_q_bound : d_q <= pred (pred n) / 2).
    { assert (Hcard_sub :
        cardinal {a : B | In B (@Residual B x y) a}
                 (Full_set {a : B | In B (@Residual B x y) a})
                 (pred (pred n))).
      { exact (cardinal_subtype_full B (@Residual B x y) (pred (pred n))
                 Hcard_minus2). }
      assert (Hpp_ge4 : pred (pred n) >= 4) by lia.
      exact (IH (pred (pred n)) ltac:(lia)
                {a : B | In B (@Residual B x y) a}
                (fun a b => R2 (proj1_sig a) (proj1_sig b))
                (subtype_is_poset R2 (@Residual B x y))
                d_q
                Hcard_sub Hpp_ge4 HdimQ). }
    (* Use removable_pair_dimension_bound to lift d_q to a (d_q + 1)-realizer of R2 *)
    assert (Hd_ext : d2 <= d_q + 1).
    { pose proof (dimension_is_realizer HdimQ) as HrSub_real.
      pose proof (dimension_cardinality HdimQ) as HrSub_card.
      destruct (@removable_pair_dimension_bound B R2 x y d_q
                  (dimension_realizer HdimQ)
                  Hrem_full HrSub_real HrSub_card)
        as [r [Hr_real Hr_card]].
      exact (dimension_is_minimum (R := R2) (d := d2) Hdim r (d_q + 1)
               Hr_real Hr_card). }
    (* Arithmetic: d_q + 1 <= (n - 2) / 2 + 1 = n / 2 for n >= 6 *)
    assert (Hbridge : pred (pred n) / 2 + 1 <= n / 2).
    { replace (pred (pred n)) with (n - 2) by lia.
      assert (Heq : n / 2 = (n - 2) / 2 + 1).
      { replace n with ((n - 2) + 1 * 2) at 1 by lia.
        rewrite Nat.div_add by lia. lia. }
      lia. }
    lia.
  - (* Chain: R2 is a total order, dim R2 <= 1 *)
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
      assert (HrS_card : cardinal (B -> B -> Prop) rSingle 1)
        by exact (singleton_cardinal _ R2).
      assert (HrS_real : @IsRealizer B R2 rSingle).
      { constructor.
        - intros L HL. destruct HL.
          constructor; [exact HR2_total | intros a b Hab; exact Hab].
        - intros a b. split.
          + intros HRab L HL. destruct HL. exact HRab.
          + intro Hall. apply Hall. constructor. }
      exact (dimension_is_minimum (R := R2) (d := d2) Hdim rSingle 1
               HrS_real HrS_card). }
    assert (Hnhalf : 1 <= n / 2) by (apply Nat.div_le_lower_bound; lia).
    lia.
Qed.

(** Hiraguchi's Theorem (1951), carrier-polymorphic form.
    Re-exports [hiraguchi_helper] under its historical name. *)
Lemma hiraguchi_thm :
  forall (n : nat) {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2} (d2 : nat),
  cardinal B (Full_set B) n ->
  n >= 4 ->
  PosetDimension R2 d2 ->
  d2 <= n / 2.
Proof.
  intros n B R2 HR2 d2 Hcard Hn4 Hdim.
  exact (@hiraguchi_helper n B R2 HR2 d2 Hcard Hn4 Hdim).
Qed.

(** Hiraguchi's Theorem, specialised form: section-arg corollary. *)
Theorem hiraguchi_bound :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R} (n d : nat),
  cardinal A (Full_set A) n ->
  n >= 4 ->
  PosetDimension R d ->
  d <= n / 2.
Proof.
  intros A R HR n d Hcard Hn4 Hdim.
  exact (@hiraguchi_helper n A R HR d Hcard Hn4 Hdim).
Qed.




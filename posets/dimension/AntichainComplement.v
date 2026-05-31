(** * Lemma 5.6 / Trotter Theorem 2:  dim(X) ≤ max{2, |X − A|}  (A antichain)

    The induction step of the direct Hiraguchi proof, built on
    [OnePointRemoval.one_point_removal].  Polymorphic over the carrier so the
    inductive call lands on the subtype X − p as a fresh poset. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia.
From Stdlib Require Import Classical ClassicalDescription ProofIrrelevance.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs Theorems OnePointRemoval.

(** Cardinality of a complement: |Full − Sub| = |Full| − |Sub|. *)
Lemma cardinal_setminus :
  forall (U : Type) (Sub : Ensemble U) (k : nat),
    cardinal U Sub k ->
    forall (Full : Ensemble U) (N : nat),
      cardinal U Full N -> Included U Sub Full ->
      cardinal U (Setminus U Full Sub) (N - k).
Proof.
  intros U Sub k Hcard. induction Hcard as [| A n Hsub IH x Hxni]; intros Full N HF Hincl.
  - (* Sub = ∅ *)
    replace (Setminus U Full (Empty_set U)) with Full.
    + rewrite Nat.sub_0_r. exact HF.
    + apply Extensionality_Ensembles. split.
      * intros y Hy. split; [ exact Hy | intro Hbot; destruct Hbot ].
      * intros y [Hy _]. exact Hy.
  - (* Sub = Add A x, x ∉ A *)
    assert (HinclA : Included U A Full).
    { intros y Hy. apply Hincl. left; exact Hy. }
    assert (Hx_full : In U Full x) by (apply Hincl; right; constructor).
    pose proof (IH Full N HF HinclA) as Hca.
    (* Setminus Full (Add A x) = Subtract (Setminus Full A) x *)
    replace (Setminus U Full (Add U A x))
       with (Subtract U (Setminus U Full A) x).
    + assert (Hx_in : In U (Setminus U Full A) x) by (split; [ exact Hx_full | exact Hxni ]).
      pose proof (card_soustr_1 U (Setminus U Full A) (N - n) Hca x Hx_in) as Hcs.
      replace (N - S n) with (Nat.pred (N - n)) by lia.
      exact Hcs.
    + apply Extensionality_Ensembles. split.
      * intros y [[Hyf Hyna] Hynx]. split; [ exact Hyf |].
        intro Hyadd. destruct Hyadd as [y Hy | y Hy].
        -- apply Hyna; exact Hy.
        -- apply Hynx; exact Hy.
      * intros y [Hyf Hyn]. split.
        -- split; [ exact Hyf | intro Hya; apply Hyn; left; exact Hya ].
        -- intro Hyx. apply Hyn. destruct Hyx. right; constructor.
Qed.

Section AntichainComplement.
  Context {B : Type}.
  Context (R : B -> B -> Prop) `{IsPoset B R}.

  (** A poset with two distinct elements has dimension ≥ 1
      (the empty realizer would force the relation to be universal). *)
  Lemma dim_ge_1_of_two :
    forall d, PosetDimension R d -> (exists a b : B, a <> b) -> 1 <= d.
  Proof.
    intros d Hdim [a [b Hab]].
    destruct d as [| d']; [| lia]. exfalso.
    pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    (* cardinal realizer 0 ⟹ realizer is empty *)
    assert (Hre : dimension_realizer Hdim = Empty_set _)
      by (apply cardinalO_empty; exact Hcard).
    assert (Hempty : forall L, ~ In _ (dimension_realizer Hdim) L).
    { intros L HL. rewrite Hre in HL. destruct HL. }
    assert (HRab : R a b).
    { apply (proj2 (realizer_intersection Hreal a b)).
      intros L HL. exfalso. exact (Hempty L HL). }
    assert (HRba : R b a).
    { apply (proj2 (realizer_intersection Hreal b a)).
      intros L HL. exfalso. exact (Hempty L HL). }
    exact (Hab (poset_antisym _ _ HRab HRba)).
  Qed.

End AntichainComplement.

(** Base case (Trotter 1975, Lemma 3 + antichain): if at most two points lie
    outside an antichain, the dimension is at most 2.  TRUE, classical; the
    [m = 2] case is Trotter's finite analysis (Figure 1).  Admitted pending its
    own formalization. *)
Lemma small_complement_le_2 :
  forall (B : Type) (R : B -> B -> Prop) `{IsPoset B R} (Ach : Ensemble B) (d m : nat),
    Finite B (Full_set B) ->
    IsAntichain R Ach ->
    PosetDimension R d ->
    cardinal B (Setminus B (Full_set B) Ach) m ->
    m <= 2 -> d <= 2.
Admitted.

(** Subtype data for one-point removal (TRUE; standard subtype/cardinal facts).
    Removing a point [p] outside the antichain [Ach] from [B] leaves the subtype
    [{a | a <> p}] with: the inherited poset, finiteness, [Ach] still an
    antichain, and complement of size [m - 1].  Admitted pending the (mechanical
    but fiddly) subtype-cardinal bookkeeping. *)
Lemma subtype_remove_data :
  forall (B : Type) (R : B -> B -> Prop) `{IsPoset B R} (Ach : Ensemble B) (p : B) (m : nat),
    Finite B (Full_set B) ->
    IsAntichain R Ach ->
    In B (Setminus B (Full_set B) Ach) p ->
    cardinal B (Setminus B (Full_set B) Ach) m ->
    exists (HR' : IsPoset {a : B | a <> p} (fun a b => R (proj1_sig a) (proj1_sig b))),
      Finite {a : B | a <> p} (Full_set _) /\
      @IsAntichain {a : B | a <> p} (fun a b => R (proj1_sig a) (proj1_sig b))
        (fun s => In B Ach (proj1_sig s)) /\
      cardinal {a : B | a <> p}
        (Setminus {a : B | a <> p} (Full_set _) (fun s => In B Ach (proj1_sig s)))
        (m - 1).
Proof.
  intros B R HR Ach p m Hfin Hanti Hp Hcompl.
  destruct Hp as [Hp_full Hp_nAch].
  destruct Hanti as [Hanti_inh Hanti_inc].
  set (Sub := {a : B | a <> p}).
  set (R' := fun a b : Sub => R (proj1_sig a) (proj1_sig b)).
  set (Ach' := fun s : Sub => In B Ach (proj1_sig s)).
  pose proof (@subtype_is_poset B R HR (fun x => x <> p)) as HR'.
  exists HR'.
  (* n := |Full B| *)
  destruct (finite_cardinal _ _ Hfin) as [n Hn].
  (* cardinal of {x | x <> p} as a B-ensemble = n - 1 *)
  assert (Hsetp : (fun x : B => x <> p) = Subtract B (Full_set B) p).
  { apply Extensionality_Ensembles. split.
    - intros x Hx. split; [ apply Full_intro | intro Hs; destruct Hs; exact (Hx eq_refl) ].
    - intros x [_ Hx] Heq. apply Hx. rewrite Heq. constructor. }
  assert (Hn1 : n = S (n - 1)).
  { destruct n as [| n']; [ exfalso | lia ].
    pose proof (cardinalO_empty _ _ Hn) as Hfe. rewrite Hfe in Hp_full. destruct Hp_full. }
  assert (HcardSp : cardinal B (fun x => x <> p) (n - 1)).
  { rewrite Hsetp.
    apply (cardinal_subtract_sn B (Full_set B) p (n - 1)); [ rewrite <- Hn1; exact Hn | exact Hp_full ]. }
  (* cardinal of subtype Full = n - 1 *)
  assert (HfullSub : cardinal Sub (Full_set Sub) (n - 1))
    by exact (cardinal_subtype_full B (fun x => x <> p) (n - 1) HcardSp).
  assert (HfinSub : Finite Sub (Full_set Sub)) by exact (cardinal_finite _ _ _ HfullSub).
  split; [ exact HfinSub | split ].
  - (* Ach' is an antichain *)
    constructor.
    + (* inhabited: Ach is inhabited and p ∉ Ach *)
      destruct Hanti_inh as [a Ha].
      assert (Ha_np : a <> p) by (intro Heq; apply Hp_nAch; rewrite <- Heq; exact Ha).
      exists (exist _ a Ha_np). unfold Ach'. simpl. exact Ha.
    + intros x y Hx Hy Hcmp. unfold Ach', R' in *.
      assert (Hpe : proj1_sig x = proj1_sig y)
        by exact (Hanti_inc _ _ Hx Hy Hcmp).
      destruct x as [x Hxp]; destruct y as [y Hyp]; simpl in Hpe; subst y.
      f_equal. apply proof_irrelevance.
  - (* cardinal of the complement subtype = m - 1 *)
    set (Comp := Setminus Sub (Full_set Sub) Ach').
    assert (HfinComp : Finite Sub Comp).
    { apply (Finite_downward_closed _ (Full_set Sub) HfinSub).
      intros s _; apply Full_intro. }
    destruct (finite_cardinal _ _ HfinComp) as [k Hk].
    (* image of Comp under proj1_sig = Subtract (Setminus Full Ach) p *)
    set (f := fun s : Sub => proj1_sig s).
    assert (Hinj : forall a b : Sub, In _ (Full_set Sub) a -> In _ (Full_set Sub) b ->
                     f a = f b -> a = b).
    { intros [a Ha] [b Hb] _ _ Heq. unfold f in Heq; simpl in Heq; subst b.
      f_equal. apply proof_irrelevance. }
    assert (HImCard : cardinal B (Im Sub B Comp f) k).
    { apply (cardinal_Im_injective _ _ Comp f k Hk).
      intros a b Ha Hb Heq. apply Hinj; [ apply Full_intro | apply Full_intro | exact Heq ]. }
    assert (HImEq : Im Sub B Comp f = Subtract B (Setminus B (Full_set B) Ach) p).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. destruct Hx as [s Hs x0 Hx0]. subst x0. unfold f.
        destruct Hs as [_ Hs_nAch]. unfold Ach' in Hs_nAch.
        destruct s as [a Hap]; simpl in *. split.
        + split; [ apply Full_intro | exact Hs_nAch ].
        + intro Hsing; destruct Hsing; exact (Hap eq_refl).
      - intros x [[_ Hx_nAch] Hx_np].
        assert (Hxp : x <> p) by (intro Heq; apply Hx_np; rewrite Heq; constructor).
        exists (exist _ x Hxp); [| reflexivity ].
        split; [ apply Full_intro | unfold Ach'; simpl; exact Hx_nAch ]. }
    rewrite HImEq in HImCard.
    (* cardinal (Subtract (Setminus Full Ach) p) = m - 1 *)
    assert (Hm1 : m = S (m - 1)).
    { destruct m as [| m']; [ exfalso | lia ].
      pose proof (cardinalO_empty _ _ Hcompl) as He.
      assert (Hpin : In B (Setminus B (Full_set B) Ach) p) by (split; assumption).
      rewrite He in Hpin. destruct Hpin. }
    assert (HsubCard : cardinal B (Subtract B (Setminus B (Full_set B) Ach) p) (m - 1)).
    { apply (cardinal_subtract_sn B (Setminus B (Full_set B) Ach) p (m - 1));
        [ rewrite <- Hm1; exact Hcompl | split; assumption ]. }
    assert (Hkeq : k = m - 1) by exact (cardinal_unicity _ _ _ HImCard _ HsubCard).
    subst k. exact Hk.
Qed.

(** A positive-cardinality set is inhabited. *)
Lemma card_inhabited :
  forall (U : Type) (X : Ensemble U) (n : nat), cardinal U X n -> 0 < n -> Inhabited U X.
Proof.
  intros U X n Hc Hpos. destruct n as [| n']; [ lia |].
  destruct (cardinal_invert _ _ _ Hc) as [A' [x [Heq _]]].
  exists x. rewrite Heq. apply Add_intro2.
Qed.

(** A set of cardinality ≥ 2 has two distinct elements. *)
Lemma card_ge_2_distinct :
  forall (U : Type) (X : Ensemble U) (n : nat),
    cardinal U X n -> 2 <= n -> exists x y, In U X x /\ In U X y /\ x <> y.
Proof.
  intros U X n Hc Hn. destruct n as [| [| n']]; try lia.
  destruct (cardinal_invert _ _ _ Hc) as [A1 [x1 [Heq1 [Hx1 Hc1]]]].
  destruct (cardinal_invert _ _ _ Hc1) as [A2 [x2 [Heq2 [Hx2 _]]]].
  exists x1, x2. repeat split.
  - rewrite Heq1. apply Add_intro2.
  - rewrite Heq1. left. rewrite Heq2. apply Add_intro2.
  - intro Heqx. apply Hx1. subst x2. rewrite Heq2. apply Add_intro2.
Qed.

(** Lemma 5.6 / Trotter Theorem 2:  dim(P) ≤ max{2, |P − A|} for an antichain A.
    Polymorphic over the carrier; strong induction on m = |P − A| using
    [one_point_removal] for the step and [small_complement_le_2] for m ≤ 2. *)
Theorem antichain_complement_dim_bound :
  forall (m : nat) (B : Type) (R : B -> B -> Prop) `{IsPoset B R}
         (Ach : Ensemble B) (d : nat),
    Finite B (Full_set B) ->
    IsAntichain R Ach ->
    PosetDimension R d ->
    cardinal B (Setminus B (Full_set B) Ach) m ->
    d <= Nat.max 2 m.
Proof.
  intro m. induction m as [m IH] using (well_founded_induction lt_wf).
  intros B R HR Ach d Hfin Hanti Hdim Hcompl.
  destruct (Nat.le_gt_cases m 2) as [Hle2 | Hgt2].
  - (* base: m <= 2 ⟹ dim <= 2 = max 2 m *)
    rewrite (Nat.max_l 2 m Hle2).
    exact (small_complement_le_2 B R Ach d m Hfin Hanti Hdim Hcompl Hle2).
  - (* step: m >= 3 *)
    rewrite (Nat.max_r 2 m (Nat.le_trans 2 3 m (le_S _ _ (le_n 2)) Hgt2)).
    (* pick p in the complement (nonempty since m >= 3) *)
    destruct (card_inhabited B (Setminus B (Full_set B) Ach) m Hcompl ltac:(lia))
      as [p Hp].
    (* subtype data *)
    destruct (subtype_remove_data B R Ach p m Hfin Hanti Hp Hcompl)
      as [HR' [Hfin' [Hanti' Hcompl']]].
    set (R' := fun a b : {a : B | a <> p} => R (proj1_sig a) (proj1_sig b)) in *.
    (* dimension of the subtype exists (Dushnik–Miller) *)
    destruct (finite_cardinal _ _ Hfin') as [nB' HcardB'].
    destruct (@dushnik_miller_exists {a : B | a <> p} R' HR' nB' HcardB') as [d' [Hdim']].
    (* IH: d' <= max 2 (m-1) *)
    assert (Hd'le : d' <= Nat.max 2 (m - 1)).
    { exact (@IH (m - 1) ltac:(lia) {a : B | a <> p} R' HR'
                (fun s => In B Ach (proj1_sig s)) d' Hfin' Hanti' Hdim' Hcompl'). }
    (* the subtype has >= 2 elements (complement size m-1 >= 2) ⟹ d' >= 1 *)
    assert (Hd'1 : 1 <= d').
    { apply (@dim_ge_1_of_two {a : B | a <> p} R' HR' d' Hdim').
      destruct (card_ge_2_distinct _ _ _ Hcompl' ltac:(lia)) as [x [y [_ [_ Hxy]]]].
      exists x, y. exact Hxy. }
    (* one-point removal: d <= d' + 1 *)
    pose proof (@one_point_removal B R HR p d d' Hd'1 Hdim Hdim') as Hstep.
    (* arithmetic: d' <= max 2 (m-1) = m-1 (m>=3), so d <= m *)
    assert (Hm1 : Nat.max 2 (m - 1) = m - 1) by (apply Nat.max_r; lia).
    lia.
Qed.


(** n = 4 per-class 2-realizer lemmas, helpers, and dispatcher.

    Split out from RemovablePairs.v.  See the doc-comment block at the
    top of [n4_one_edge_two_realizer] for the (a)-(n) isomorphism
    classes that this file closes for posets on a carrier of
    cardinality 4. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Helper for [n4_one_edge_two_realizer]: when [Full_set B] has
    cardinal 4, extract 4 pairwise distinct elements [p, q, r, s] and
    confirm that every element of [B] equals one of them.

    The "covers" conjunct relies on stripping the four elements off
    [Full_set B] and observing the remaining ensemble has cardinal 0,
    hence is [Empty_set]; consequently any [a : B] outside [{p,q,r,s}]
    would still lie in the residual and contradict emptiness. *)
Lemma carrier_4_destructure :
  forall {B : Type} (p q : B),
  cardinal B (Full_set B) 4 ->
  p <> q ->
  exists r s : B,
    p <> r /\ p <> s /\ q <> r /\ q <> s /\ r <> s /\
    (forall a : B, a = p \/ a = q \/ a = r \/ a = s).
Proof.
  intros B p q Hcard Hpq.
  (* Strip p from Full_set: cardinal 3. *)
  assert (Hp_in : In B (Full_set B) p) by apply Full_intro.
  assert (Hcard1 : cardinal B (Subtract B (Full_set B) p) 3)
    by exact (cardinal_subtract_sn B (Full_set B) p 3 Hcard Hp_in).
  (* Strip q from the remainder. *)
  assert (Hq_in1 : In B (Subtract B (Full_set B) p) q).
  { apply Subtract_intro; [apply Full_intro |]. exact Hpq. }
  assert (Hcard2 : cardinal B (Subtract B (Subtract B (Full_set B) p) q) 2)
    by exact (cardinal_subtract_sn B (Subtract B (Full_set B) p) q 2 Hcard1 Hq_in1).
  (* Inhabited: pick r. *)
  assert (Hinh2 : Inhabited B (Subtract B (Subtract B (Full_set B) p) q))
    by exact (cardinal_elim B _ 2 Hcard2).
  destruct Hinh2 as [r Hr_in2].
  destruct (Subtract_inv _ _ _ _ Hr_in2) as [Hr_in1 Hqr_neq].
  destruct (Subtract_inv _ _ _ _ Hr_in1) as [_ Hpr_neq].
  (* Strip r. *)
  assert (Hcard3 : cardinal B (Subtract B (Subtract B (Subtract B (Full_set B) p) q) r) 1)
    by exact (cardinal_subtract_sn B _ r 1 Hcard2 Hr_in2).
  assert (Hinh3 : Inhabited B (Subtract B (Subtract B (Subtract B (Full_set B) p) q) r))
    by exact (cardinal_elim B _ 1 Hcard3).
  destruct Hinh3 as [s Hs_in3].
  destruct (Subtract_inv _ _ _ _ Hs_in3) as [Hs_in2 Hrs_neq].
  destruct (Subtract_inv _ _ _ _ Hs_in2) as [Hs_in1 Hqs_neq].
  destruct (Subtract_inv _ _ _ _ Hs_in1) as [_ Hps_neq].
  (* Strip s: cardinal 0, so Empty_set. *)
  assert (Hcard4 : cardinal B (Subtract B (Subtract B (Subtract B (Subtract B (Full_set B) p) q) r) s) 0)
    by exact (cardinal_subtract_sn B _ s 0 Hcard3 Hs_in3).
  assert (Hempty : Subtract B (Subtract B (Subtract B (Subtract B (Full_set B) p) q) r) s = Empty_set B)
    by exact (cardinal_elim B _ 0 Hcard4).
  exists r, s.
  split; [exact Hpr_neq |].
  split; [exact Hps_neq |].
  split; [exact Hqr_neq |].
  split; [exact Hqs_neq |].
  split; [exact Hrs_neq |].
  intro a.
  destruct (excluded_middle_informative (a = p)) as [Hap | Hnap]; [auto |].
  destruct (excluded_middle_informative (a = q)) as [Haq | Hnaq]; [auto |].
  destruct (excluded_middle_informative (a = r)) as [Har | Hnar]; [auto |].
  destruct (excluded_middle_informative (a = s)) as [Has | Hnas]; [auto |].
  (* Otherwise, a is in the four-fold residual = Empty_set. *)
  exfalso.
  assert (Hin_full : In B (Full_set B) a) by apply Full_intro.
  assert (Hin1 : In B (Subtract B (Full_set B) p) a)
    by exact (Subtract_intro _ _ _ _ Hin_full (fun He => Hnap (eq_sym He))).
  assert (Hin2 : In B (Subtract B (Subtract B (Full_set B) p) q) a)
    by exact (Subtract_intro _ _ _ _ Hin1 (fun He => Hnaq (eq_sym He))).
  assert (Hin3 : In B (Subtract B (Subtract B (Subtract B (Full_set B) p) q) r) a)
    by exact (Subtract_intro _ _ _ _ Hin2 (fun He => Hnar (eq_sym He))).
  assert (Hin4 : In B (Subtract B (Subtract B (Subtract B (Subtract B (Full_set B) p) q) r) s) a)
    by exact (Subtract_intro _ _ _ _ Hin3 (fun He => Hnas (eq_sym He))).
  rewrite Hempty in Hin4.
  destruct Hin4.
Qed.

(** Sub-case: n=4 poset with EXACTLY ONE strict edge.

    The carrier has 4 distinct elements; [R2] is identity plus one
    strict relation [R2 p q] with [p <> q]; no other strict relations.

    Explicit 2-realizer: [L1] orders [p < q < r < s] and [L2] orders
    [s < r < p < q].  Both extend [R2] (the only required pair is
    [R2 p q], which both [L1] and [L2] satisfy), and their intersection
    on the carrier is exactly [R2] because the only off-diagonal pair
    on which they agree is [(p, q)].  Cardinality is 2 because, for
    instance, [L1 r s] but [~ L2 r s]. *)
Lemma n4_one_edge_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists p q : B,
     p <> q /\ R2 p q /\
     (forall a b : B, R2 a b -> a = b \/ (a = p /\ b = q))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard [p [q [Hpq_neq [HRpq HR_only]]]].
  destruct (@carrier_4_destructure B p q Hcard Hpq_neq)
    as [r [s [Hpr [Hps [Hqr [Hqs [Hrs Hcovers]]]]]]].
  (* L1 rank: p=0, q=1, r=2, s=3.  L2 rank: s=0, r=1, p=2, q=3. *)
  set (rk1 := fun a : B =>
                if excluded_middle_informative (a = p) then 0%nat
                else if excluded_middle_informative (a = q) then 1%nat
                else if excluded_middle_informative (a = r) then 2%nat
                else 3%nat).
  set (rk2 := fun a : B =>
                if excluded_middle_informative (a = s) then 0%nat
                else if excluded_middle_informative (a = r) then 1%nat
                else if excluded_middle_informative (a = p) then 2%nat
                else 3%nat).
  (* Rank computations on the four elements. *)
  assert (Hrk1_p : rk1 p = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (p = p)); [reflexivity | contradiction]. }
  assert (Hrk1_q : rk1 q = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (q = p)); [contradiction Hpq_neq; auto |].
    destruct (excluded_middle_informative (q = q)); [reflexivity | contradiction]. }
  assert (Hrk1_r : rk1 r = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (r = p)) as [He|_]; [contradiction Hpr; auto |].
    destruct (excluded_middle_informative (r = q)) as [He|_]; [contradiction Hqr; auto |].
    destruct (excluded_middle_informative (r = r)); [reflexivity | contradiction]. }
  assert (Hrk1_s : rk1 s = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (s = p)) as [He|_]; [contradiction Hps; auto |].
    destruct (excluded_middle_informative (s = q)) as [He|_]; [contradiction Hqs; auto |].
    destruct (excluded_middle_informative (s = r)) as [He|_]; [contradiction Hrs; auto |].
    reflexivity. }
  assert (Hrk2_p : rk2 p = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (p = s)) as [He|_]; [contradiction Hps; auto |].
    destruct (excluded_middle_informative (p = r)) as [He|_]; [contradiction Hpr; auto |].
    destruct (excluded_middle_informative (p = p)); [reflexivity | contradiction]. }
  assert (Hrk2_q : rk2 q = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (q = s)) as [He|_]; [contradiction Hqs; auto |].
    destruct (excluded_middle_informative (q = r)) as [He|_]; [contradiction Hqr; auto |].
    destruct (excluded_middle_informative (q = p)) as [He|_];
      [contradiction Hpq_neq; symmetry; exact He |].
    reflexivity. }
  assert (Hrk2_r : rk2 r = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (r = s)) as [He|_]; [contradiction Hrs; auto |].
    destruct (excluded_middle_informative (r = r)); [reflexivity | contradiction]. }
  assert (Hrk2_s : rk2 s = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (s = s)); [reflexivity | contradiction]. }
  (* Rank ≤ 3 always. *)
  assert (Hrk1_le3 : forall a, rk1 a <= 3).
  { intro a. destruct (Hcovers a) as [He|[He|[He|He]]]; subst a;
      [rewrite Hrk1_p | rewrite Hrk1_q | rewrite Hrk1_r | rewrite Hrk1_s]; lia. }
  assert (Hrk2_le3 : forall a, rk2 a <= 3).
  { intro a. destruct (Hcovers a) as [He|[He|[He|He]]]; subst a;
      [rewrite Hrk2_p | rewrite Hrk2_q | rewrite Hrk2_r | rewrite Hrk2_s]; lia. }
  (* Injectivity of rk1 (and rk2) on B: if ranks agree, elements agree. *)
  assert (Hrk1_inj : forall a b, rk1 a = rk1 b -> a = b).
  { intros a b Hab.
    destruct (Hcovers a) as [Ha|[Ha|[Ha|Ha]]]; subst a;
    destruct (Hcovers b) as [Hb|[Hb|[Hb|Hb]]]; subst b;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_p, ?Hrk1_q, ?Hrk1_r, ?Hrk1_s in Hab;
              discriminate ]. }
  assert (Hrk2_inj : forall a b, rk2 a = rk2 b -> a = b).
  { intros a b Hab.
    destruct (Hcovers a) as [Ha|[Ha|[Ha|Ha]]]; subst a;
    destruct (Hcovers b) as [Hb|[Hb|[Hb|Hb]]]; subst b;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_p, ?Hrk2_q, ?Hrk2_r, ?Hrk2_s in Hab;
              discriminate ]. }
  (* Define L1, L2 as rank-le. *)
  set (L1 := fun a b : B => rk1 a <= rk1 b).
  set (L2 := fun a b : B => rk2 a <= rk2 b).
  (* L1 is a total order. *)
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro a. lia.
    - intros a b Hab Hba. apply Hrk1_inj. lia.
    - intros a b c Hab Hbc. lia. }
  assert (HL1_total : forall a b, L1 a b \/ L1 b a).
  { intros a b. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall a b, R2 a b -> L1 a b).
  { intros a b HR. destruct (HR_only a b HR) as [Heq | [Hae Hbe]].
    - subst b. unfold L1. lia.
    - subst a b. unfold L1. rewrite Hrk1_p, Hrk1_q. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  (* L2 is a total order. *)
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro a. lia.
    - intros a b Hab Hba. apply Hrk2_inj. lia.
    - intros a b c Hab Hbc. lia. }
  assert (HL2_total : forall a b, L2 a b \/ L2 b a).
  { intros a b. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall a b, R2 a b -> L2 a b).
  { intros a b HR. destruct (HR_only a b HR) as [Heq | [Hae Hbe]].
    - subst b. unfold L2. lia.
    - subst a b. unfold L2. rewrite Hrk2_p, Hrk2_q. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  (* Intersection: L1 a b ∧ L2 a b → R2 a b.
     Case-split on (a, b) ∈ {p,q,r,s}^2 (16 cases). *)
  assert (Hinter : forall a b, L1 a b -> L2 a b -> R2 a b).
  { intros a b HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers a) as [Ha|[Ha|[Ha|Ha]]]; subst a;
    destruct (Hcovers b) as [Hb|[Hb|[Hb|Hb]]]; subst b;
      first [ apply HR2.(poset_refl)
            | exact HRpq
            | exfalso;
              rewrite ?Hrk1_p, ?Hrk1_q, ?Hrk1_r, ?Hrk1_s in HLa;
              rewrite ?Hrk2_p, ?Hrk2_q, ?Hrk2_r, ?Hrk2_s in HLb;
              lia ]. }
  (* Build realizer set {L1, L2}. *)
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - (* IsRealizer R2 rls. *)
    constructor.
    + (* All members are linear extensions. *)
      intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + (* Intersection equals R2. *)
      intros a b. split.
      * intros HRab L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) a b HRab). }
        { destruct HL. exact (HL2_lin.(linear_extends) a b HRab). }
      * intro Hall.
        assert (HLa : L1 a b)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 a b)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter a b HLa HLb).
  - (* Cardinal 2. *)
    assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 r s holds (rk1 r = 2 ≤ 3 = rk1 s), but L2 r s would imply rk2 r ≤ rk2 s,
         i.e., 1 ≤ 0, contradiction. *)
      assert (HL1rs : L1 r s) by (unfold L1; rewrite Hrk1_r, Hrk1_s; lia).
      assert (HL2rs : L2 r s) by (rewrite <- Heq; exact HL1rs).
      unfold L2 in HL2rs. rewrite Hrk2_r, Hrk2_s in HL2rs. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 poset with a 3-element chain plus one isolated point.

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b], [R2 b c], [R2 a c] (the chain
    [a < b < c]) and nothing else.  In particular, [d] is incomparable
    to each of [a, b, c].

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [d < a < b < c].  Both extend the chain (ranks of [a, b, c] are
    monotone in both), and their intersection on the carrier is exactly
    [R2] because the only off-diagonal pairs on which they agree are
    [(a, b), (a, c), (b, c)] — exactly the strict edges of [R2].
    Cardinality is 2 because, for instance, [L1 a d] but [~ L2 a d]. *)
Lemma n4_chain_plus_isolated_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 b c /\ R2 a c /\
     (forall x y : B,
        R2 x y -> x = y \/
        ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRbc [HRac HR_only]]]]]]]]]]]]].
  (* Derive the 4-element cover from [carrier_4_destructure] applied to (a, b).
     The resulting two elements [r, s] satisfy {r, s} = {c, d}, so every
     [x : B] is one of [a, b, c, d]. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  (* {c, d} ⊆ {r, s} : c must be r or s. *)
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  (* Conversely, r ∈ {c, d} and s ∈ {c, d} by exhausting cases on Hc_in/Hd_in. *)
  assert (Hr_in : r = c \/ r = d).
  { destruct Hc_in as [Hc | Hc].
    - left; symmetry; exact Hc.
    - destruct Hd_in as [Hd | Hd].
      + right; symmetry; exact Hd.
      + (* c = s and d = s gives c = d, contradiction *)
        exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  assert (Hs_in : s = c \/ s = d).
  { destruct Hc_in as [Hc | Hc].
    - destruct Hd_in as [Hd | Hd].
      + (* c = r and d = r gives c = d *)
        exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; symmetry; exact Hd.
    - left; symmetry; exact Hc. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hr_in as [Hr | Hr]; [right; right; left | right; right; right]; exact Hr.
    - subst x. destruct Hs_in as [Hs | Hs]; [right; right; left | right; right; right]; exact Hs. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: d=0, a=1, b=2, c=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = d) then 0%nat
                else if excluded_middle_informative (x = a) then 1%nat
                else if excluded_middle_informative (x = b) then 2%nat
                else 3%nat).
  (* Rank computations on the four elements. *)
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = d)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    reflexivity. }
  assert (Hrk2_d : rk2 d = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  (* Injectivity of rk1 (and rk2) on B. *)
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  (* Define L1, L2 as rank-le. *)
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  (* L1 is a total order. *)
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [Hxb Hyc]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  (* L2 is a total order. *)
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [Hxb Hyc]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  (* Intersection: L1 x y ∧ L2 x y → R2 x y.
     16-case split.  R2-yielding cases are diag and (a,b),(a,c),(b,c). *)
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exact HRbc
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  (* Build realizer set {L1, L2}. *)
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - (* IsRealizer R2 rls. *)
    constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - (* Cardinal 2. *)
    assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 a d: 0 ≤ 3.  L2 a d would require 1 ≤ 0, contradiction. *)
      assert (HL1ad : L1 a d) by (unfold L1; rewrite Hrk1_a, Hrk1_d; lia).
      assert (HL2ad : L2 a d) by (rewrite <- Heq; exact HL1ad).
      unfold L2 in HL2ad. rewrite Hrk2_a, Hrk2_d in HL2ad. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 poset that is two disjoint 2-element chains.

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b] and [R2 c d], and nothing else.

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [c < d < a < b].  Both extend the two strict edges, and their
    intersection on the carrier is exactly [R2] because the only
    off-diagonal pairs on which they agree are [(a, b)] and [(c, d)].
    Cardinality is 2 because, for instance, [L1 a c] but [~ L2 a c]. *)
Lemma n4_disjoint_chains_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 c d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRcd HR_only]]]]]]]]]]]].
  (* Cover argument: {r, s} = {c, d}. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hr_in : r = c \/ r = d).
  { destruct Hc_in as [Hc | Hc].
    - left; symmetry; exact Hc.
    - destruct Hd_in as [Hd | Hd].
      + right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  assert (Hs_in : s = c \/ s = d).
  { destruct Hc_in as [Hc | Hc].
    - destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; symmetry; exact Hd.
    - left; symmetry; exact Hc. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hr_in as [Hr | Hr]; [right; right; left | right; right; right]; exact Hr.
    - subst x. destruct Hs_in as [Hs | Hs]; [right; right; left | right; right; right]; exact Hs. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: c=0, d=1, a=2, b=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = c) then 0%nat
                else if excluded_middle_informative (x = d) then 1%nat
                else if excluded_middle_informative (x = a) then 2%nat
                else 3%nat).
  (* Rank computations. *)
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = c)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (a = d)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    reflexivity. }
  assert (Hrk2_c : rk2 c = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  (* Injectivity. *)
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  (* L1, L2 as rank-le. *)
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [Hxc Hyd]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_c, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [Hxc Hyd]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_c, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  (* Intersection. *)
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRcd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  (* Build realizer set {L1, L2}. *)
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 a c: 0 ≤ 2.  L2 a c would require 2 ≤ 0, contradiction. *)
      assert (HL1ac : L1 a c) by (unfold L1; rewrite Hrk1_a, Hrk1_c; lia).
      assert (HL2ac : L2 a c) by (rewrite <- Heq; exact HL1ac).
      unfold L2 in HL2ac. rewrite Hrk2_a, Hrk2_c in HL2ac. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 V-shape.

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b] and [R2 a c], and nothing else
    (so [b], [c] are incomparable and [d] is isolated).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [d < a < c < b].  Both extend the two strict edges from [a], and
    their intersection on the carrier agrees only on [(a, b)] and
    [(a, c)] off the diagonal.  Cardinality is 2 because, for
    instance, [L1 a d] but [~ L2 a d]. *)
Lemma n4_V_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 a c /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRac HR_only]]]]]]]]]]]].
  (* Cover argument: {r, s} = {c, d}. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hr_in : r = c \/ r = d).
  { destruct Hc_in as [Hc | Hc].
    - left; symmetry; exact Hc.
    - destruct Hd_in as [Hd | Hd].
      + right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  assert (Hs_in : s = c \/ s = d).
  { destruct Hc_in as [Hc | Hc].
    - destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; symmetry; exact Hd.
    - left; symmetry; exact Hc. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hr_in as [Hr | Hr]; [right; right; left | right; right; right]; exact Hr.
    - subst x. destruct Hs_in as [Hs | Hs]; [right; right; left | right; right; right]; exact Hs. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: d=0, a=1, c=2, b=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = d) then 0%nat
                else if excluded_middle_informative (x = a) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  (* Rank computations. *)
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = d)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    reflexivity. }
  assert (Hrk2_c : rk2 c = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  (* Injectivity. *)
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  (* L1, L2 as rank-le. *)
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [Hxa Hyc]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [Hxa Hyc]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  (* Intersection. *)
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  (* Build realizer set {L1, L2}. *)
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 a d: 0 ≤ 3.  L2 a d would require 1 ≤ 0, contradiction. *)
      assert (HL1ad : L1 a d) by (unfold L1; rewrite Hrk1_a, Hrk1_d; lia).
      assert (HL2ad : L2 a d) by (rewrite <- Heq; exact HL1ad).
      unfold L2 in HL2ad. rewrite Hrk2_a, Hrk2_d in HL2ad. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 inverted-V shape (dual of [n4_V_two_realizer]).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a c] and [R2 b c], and nothing else
    (so [a], [b] are incomparable and [d] is isolated).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [d < b < a < c].  Both extend the two strict edges into [c], and
    their intersection on the carrier agrees only on [(a, c)] and
    [(b, c)] off the diagonal.  Cardinality is 2 because, for
    instance, [L1 a b] but [~ L2 a b]. *)
Lemma n4_inv_V_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a c /\ R2 b c /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRac [HRbc HR_only]]]]]]]]]]]].
  (* Cover argument: {r, s} = {c, d}. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hr_in : r = c \/ r = d).
  { destruct Hc_in as [Hc | Hc].
    - left; symmetry; exact Hc.
    - destruct Hd_in as [Hd | Hd].
      + right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  assert (Hs_in : s = c \/ s = d).
  { destruct Hc_in as [Hc | Hc].
    - destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; symmetry; exact Hd.
    - left; symmetry; exact Hc. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hr_in as [Hr | Hr]; [right; right; left | right; right; right]; exact Hr.
    - subst x. destruct Hs_in as [Hs | Hs]; [right; right; left | right; right; right]; exact Hs. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: d=0, b=1, a=2, c=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = d) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = a) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = d)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (a = b)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    reflexivity. }
  assert (Hrk2_d : rk2 d = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyc] | [Hxb Hyc]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR) as [Heq | [[Hxa Hyc] | [Hxb Hyc]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRac
            | exact HRbc
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 a b: 0 ≤ 1.  L2 a b would require 2 ≤ 1, contradiction. *)
      assert (HL1ab : L1 a b) by (unfold L1; rewrite Hrk1_a, Hrk1_b; lia).
      assert (HL2ab : L2 a b) by (rewrite <- Heq; exact HL1ab).
      unfold L2 in HL2ab. rewrite Hrk2_a, Hrk2_b in HL2ab. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 N-shape.

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b], [R2 c b], and [R2 c d], and
    nothing else (so [a], [c] are incomparable, [b], [d] are
    incomparable, and [a, d] are incomparable).

    Explicit 2-realizer: [L1] orders [a < c < b < d] and [L2] orders
    [c < d < a < b].  Both extend the three strict edges, and their
    intersection on the carrier agrees only on [(a, b)], [(c, b)] and
    [(c, d)] off the diagonal.  Cardinality is 2 because, for
    instance, [L1 a c] but [~ L2 a c]. *)
Lemma n4_N_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 c b /\ R2 c d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRcb [HRcd HR_only]]]]]]]]]]]]].
  (* Cover argument: {r, s} = {c, d}. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hr_in : r = c \/ r = d).
  { destruct Hc_in as [Hc | Hc].
    - left; symmetry; exact Hc.
    - destruct Hd_in as [Hd | Hd].
      + right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  assert (Hs_in : s = c \/ s = d).
  { destruct Hc_in as [Hc | Hc].
    - destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; symmetry; exact Hd.
    - left; symmetry; exact Hc. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hr_in as [Hr | Hr]; [right; right; left | right; right; right]; exact Hr.
    - subst x. destruct Hs_in as [Hs | Hs]; [right; right; left | right; right; right]; exact Hs. }
  (* L1 rank: a=0, c=1, b=2, d=3.  L2 rank: c=0, d=1, a=2, b=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = c) then 1%nat
                else if excluded_middle_informative (x = b) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = c) then 0%nat
                else if excluded_middle_informative (x = d) then 1%nat
                else if excluded_middle_informative (x = a) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = c)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (a = d)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    reflexivity. }
  assert (Hrk2_c : rk2 c = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR.
    destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [[Hxc Hyb] | [Hxc Hyd]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_c, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_c, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR.
    destruct (HR_only x y HR) as [Heq | [[Hxa Hyb] | [[Hxc Hyb] | [Hxc Hyd]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_c, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_c, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRcb
            | exact HRcd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 a c: 0 ≤ 1.  L2 a c would require 2 ≤ 0, contradiction. *)
      assert (HL1ac : L1 a c) by (unfold L1; rewrite Hrk1_a, Hrk1_c; lia).
      assert (HL2ac : L2 a c) by (rewrite <- Heq; exact HL1ac).
      unfold L2 in HL2ac. rewrite Hrk2_a, Hrk2_c in HL2ac. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.







(** ** N=4 dispatcher: route non-antichain non-chain posets on 4
    elements to one of the six Qed sub-cases.

    Given the 6 closed sub-lemmas:
      - [n4_one_edge_two_realizer]            (class a: one strict edge)
      - [n4_chain_plus_isolated_two_realizer] (class b: 3-chain + isolated)
      - [n4_V_two_realizer]                   (class c: V-shape)
      - [n4_inv_V_two_realizer]               (class d: ∧-shape)
      - [n4_disjoint_chains_two_realizer]     (class e: 2 disjoint edges)
      - [n4_N_two_realizer]                   (class f: N-shape)

    There are 14 non-antichain non-chain unlabeled posets on 4
    elements (16 total minus chain and antichain), so the six
    sub-lemmas cover 6 of those 14 classes; the residual 8 classes
    (Y-up "claw", Y-down "claw", diamond, chain-of-3 + extra above/below,
    and three further configurations) are captured by the focused admit
    [n4_residual_classes_two_realizer] below.  This dispatcher Qed-routes
    the six covered classes to their respective sub-lemmas.

    NOTE: the [n4_residual_classes_two_realizer] admit is mathematically
    sound (each residual class has dim ≤ 2 by Hiraguchi's bound for n =
    4) but its proof is left for a follow-up extending the catalogue of
    sub-lemmas. *)

(** Sub-case: n=4 3-claw up (class g).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b], [R2 a c], [R2 a d], and nothing else
    (so [a] is a common bottom and [b], [c], [d] are pairwise incomparable).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [a < d < c < b].  Both extend the three strict edges from [a].
    Cardinality is 2 because, for instance, [L1 b c] but [~ L2 b c]. *)
Lemma n4_3claw_up_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 a c /\ R2 a d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/
                 (x = a /\ y = c) \/ (x = a /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRac [HRad HR_only]]]]]]]]]]]]].
  (* Cover argument: {r, s} = {c, d}. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: a=0, d=1, c=2, b=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = d) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  (* Rank computations. *)
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    reflexivity. }
  assert (Hrk2_c : rk2 c = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  (* Injectivity. *)
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  (* L1, L2 as rank-le. *)
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [Hxa Hyd]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [Hxa Hyd]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  (* Intersection. *)
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exact HRad
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  (* Build realizer set {L1, L2}. *)
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 b c: 1 ≤ 2.  L2 b c would require 3 ≤ 2, contradiction. *)
      assert (HL1bc : L1 b c) by (unfold L1; rewrite Hrk1_b, Hrk1_c; lia).
      assert (HL2bc : L2 b c) by (rewrite <- Heq; exact HL1bc).
      unfold L2 in HL2bc. rewrite Hrk2_b, Hrk2_c in HL2bc. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 3-claw down (class h).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a d], [R2 b d], [R2 c d], and nothing else
    (so [d] is a common top and [a], [b], [c] are pairwise incomparable).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [c < b < a < d].  Both extend the three strict edges into [d].
    Cardinality is 2 because, for instance, [L1 a b] but [~ L2 a b]. *)
Lemma n4_3claw_down_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a d /\ R2 b d /\ R2 c d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = d) \/
                 (x = b /\ y = d) \/ (x = c /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRad [HRbd [HRcd HR_only]]]]]]]]]]]]].
  (* Cover argument. *)
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: c=0, b=1, a=2, d=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = c) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = a) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = c)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (a = b)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    reflexivity. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyd] | [[Hxb Hyd] | [Hxc Hyd]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_c, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyd] | [[Hxb Hyd] | [Hxc Hyd]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_c, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRad
            | exact HRbd
            | exact HRcd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      (* L1 a b: 0 ≤ 1.  L2 a b would require 2 ≤ 1, contradiction. *)
      assert (HL1ab : L1 a b) by (unfold L1; rewrite Hrk1_a, Hrk1_b; lia).
      assert (HL2ab : L2 a b) by (rewrite <- Heq; exact HL1ab).
      unfold L2 in HL2ab. rewrite Hrk2_a, Hrk2_b in HL2ab. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 diamond (class i).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b], [R2 a c], [R2 a d], [R2 b d], [R2 c d],
    and nothing else. So [a] is bottom, [d] is top, and [b], [c] are
    incomparable (the diamond).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [a < c < b < d].  Both extend the diamond relations.
    Cardinality is 2 because, for instance, [L1 b c] but [~ L2 b c]. *)
Lemma n4_diamond_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 a c /\ R2 a d /\ R2 b d /\ R2 c d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c) \/
                 (x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRac [HRad [HRbd [HRcd HR_only]]]]]]]]]]]]]]].
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: a=0, c=1, b=2, d=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = c) then 1%nat
                else if excluded_middle_informative (x = b) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = c)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    reflexivity. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxa Hyd] | [[Hxb Hyd] | [Hxc Hyd]]]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_c, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxa Hyd] | [[Hxb Hyd] | [Hxc Hyd]]]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_c, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exact HRad
            | exact HRbd
            | exact HRcd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      assert (HL1bc : L1 b c) by (unfold L1; rewrite Hrk1_b, Hrk1_c; lia).
      assert (HL2bc : L2 b c) by (rewrite <- Heq; exact HL1bc).
      unfold L2 in HL2bc. rewrite Hrk2_b, Hrk2_c in HL2bc. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 bowtie (class j).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a c], [R2 a d], [R2 b c], [R2 b d], and
    nothing else (so [a, b] are incomparable bottoms and [c, d] are
    incomparable tops — the 2x2 product).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [b < a < d < c].
    Cardinality is 2 because, for instance, [L1 a b] but [~ L2 a b]. *)
Lemma n4_bowtie_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
                 (x = b /\ y = c) \/ (x = b /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRac [HRad [HRbc [HRbd HR_only]]]]]]]]]]]]]].
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: b=0, a=1, d=2, c=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = b) then 0%nat
                else if excluded_middle_informative (x = a) then 1%nat
                else if excluded_middle_informative (x = d) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = b)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_d : rk2 d = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyc] | [[Hxa Hyd] | [[Hxb Hyc] | [Hxb Hyd]]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyc] | [[Hxa Hyd] | [[Hxb Hyc] | [Hxb Hyd]]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRac
            | exact HRad
            | exact HRbc
            | exact HRbd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      assert (HL1ab : L1 a b) by (unfold L1; rewrite Hrk1_a, Hrk1_b; lia).
      assert (HL2ab : L2 a b) by (rewrite <- Heq; exact HL1ab).
      unfold L2 in HL2ab. rewrite Hrk2_a, Hrk2_b in HL2ab. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 chain-of-3 plus element below (class k).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b], [R2 a c], [R2 b c], [R2 a d], and
    nothing else (so [a] is the common bottom, [a < b < c] is a chain
    with [a < c] explicit by transitivity, and [d] is comparable only
    with [a]).

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [a < d < b < c].
    Cardinality is 2 because, for instance, [L1 b d] but [~ L2 b d]. *)
Lemma n4_chain3_plus_below_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 a c /\ R2 b c /\ R2 a d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c) \/
                 (x = b /\ y = c) \/ (x = a /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRac [HRbc [HRad HR_only]]]]]]]]]]]]]].
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: a=0, d=1, b=2, c=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = d) then 1%nat
                else if excluded_middle_informative (x = b) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    reflexivity. }
  assert (Hrk2_d : rk2 d = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxb Hyc] | [Hxa Hyd]]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxb Hyc] | [Hxa Hyd]]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exact HRbc
            | exact HRad
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      assert (HL1bd : L1 b d) by (unfold L1; rewrite Hrk1_b, Hrk1_d; lia).
      assert (HL2bd : L2 b d) by (rewrite <- Heq; exact HL1bd).
      unfold L2 in HL2bd. rewrite Hrk2_b, Hrk2_d in HL2bd. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 chain-of-3 plus element above (class l), dual of (k).

    The carrier has 4 distinct elements [a, b, c, d]; [R2] is identity
    plus strict relations [R2 a b], [R2 a c], [R2 b c], [R2 d c], and
    nothing else (so [c] is the common top, [a < b < c] is a chain with
    [a < c] explicit by transitivity, and [d] is comparable only with
    [c]).

    Explicit 2-realizer: [L1] orders [a < b < d < c] and [L2] orders
    [d < a < b < c].
    Cardinality is 2 because, for instance, [L1 a d] but [~ L2 a d]. *)
Lemma n4_chain3_plus_above_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 a c /\ R2 b c /\ R2 d c /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c) \/
                 (x = b /\ y = c) \/ (x = d /\ y = c))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRac [HRbc [HRdc HR_only]]]]]]]]]]]]]].
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, d=2, c=3.  L2 rank: d=0, a=1, b=2, c=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = d) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = d) then 0%nat
                else if excluded_middle_informative (x = a) then 1%nat
                else if excluded_middle_informative (x = b) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk1_d : rk1 d = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk2_a : rk2 a = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = d)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = d)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    reflexivity. }
  assert (Hrk2_d : rk2 d = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxb Hyc] | [Hxd Hyc]]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_d, Hrk1_c. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxb Hyc] | [Hxd Hyc]]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_d, Hrk2_c. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exact HRbc
            | exact HRdc
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      assert (HL1ad : L1 a d) by (unfold L1; rewrite Hrk1_a, Hrk1_d; lia).
      assert (HL2ad : L2 a d) by (rewrite <- Heq; exact HL1ad).
      unfold L2 in HL2ad. rewrite Hrk2_a, Hrk2_d in HL2ad. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 Y-up extended (class m).

    The carrier has 4 distinct elements [a, b, c, d]; the Hasse diagram
    is [a -> b], [b -> c], [b -> d] (so [c], [d] are incomparable atop
    a chain [a < b]). [R2] is identity plus [R2 a b], [R2 a c], [R2 a d],
    [R2 b c], [R2 b d].

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [a < b < d < c].
    Cardinality is 2 because, for instance, [L1 c d] but [~ L2 c d]. *)
Lemma n4_Y_chain_up_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a b /\ R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c) \/
                 (x = a /\ y = d) \/ (x = b /\ y = c) \/ (x = b /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRab [HRac [HRad [HRbc [HRbd HR_only]]]]]]]]]]]]]]].
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: a=0, b=1, d=2, c=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = d) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = d)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_d : rk2 d = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = d)); [reflexivity | contradiction]. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxa Hyd] | [[Hxb Hyc] | [Hxb Hyd]]]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_b. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyb] | [[Hxa Hyc] | [[Hxa Hyd] | [[Hxb Hyc] | [Hxb Hyd]]]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_b. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRab
            | exact HRac
            | exact HRad
            | exact HRbc
            | exact HRbd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      assert (HL1cd : L1 c d) by (unfold L1; rewrite Hrk1_c, Hrk1_d; lia).
      assert (HL2cd : L2 c d) by (rewrite <- Heq; exact HL1cd).
      unfold L2 in HL2cd. rewrite Hrk2_c, Hrk2_d in HL2cd. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Sub-case: n=4 Y-down extended (class n), dual of (m).

    The carrier has 4 distinct elements [a, b, c, d]; the Hasse diagram
    is [a -> c], [b -> c], [c -> d] (so [a], [b] are incomparable below
    a chain [c < d]). [R2] is identity plus [R2 a c], [R2 b c], [R2 c d],
    [R2 a d], [R2 b d].

    Explicit 2-realizer: [L1] orders [a < b < c < d] and [L2] orders
    [b < a < c < d].
    Cardinality is 2 because, for instance, [L1 a b] but [~ L2 a b]. *)
Lemma n4_Y_chain_down_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  (exists a b c d : B,
     a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
     R2 a c /\ R2 b c /\ R2 c d /\ R2 a d /\ R2 b d /\
     (forall x y : B,
        R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                 (x = c /\ y = d) \/ (x = a /\ y = d) \/ (x = b /\ y = d))) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard
    [a [b [c [d [Hab_neq [Hac_neq [Had_neq [Hbc_neq [Hbd_neq [Hcd_neq
       [HRac [HRbc [HRcd [HRad [HRbd HR_only]]]]]]]]]]]]]]].
  destruct (@carrier_4_destructure B a b Hcard Hab_neq)
    as [r [s [Har_neq [Has_neq [Hbr_neq [Hbs_neq [Hrs_neq Hcov4]]]]]]].
  assert (Hc_in : c = r \/ c = s).
  { destruct (Hcov4 c) as [Hc | [Hc | [Hc | Hc]]].
    - contradiction Hac_neq; symmetry; exact Hc.
    - contradiction Hbc_neq; symmetry; exact Hc.
    - left; exact Hc.
    - right; exact Hc. }
  assert (Hd_in : d = r \/ d = s).
  { destruct (Hcov4 d) as [Hd | [Hd | [Hd | Hd]]].
    - contradiction Had_neq; symmetry; exact Hd.
    - contradiction Hbd_neq; symmetry; exact Hd.
    - left; exact Hd.
    - right; exact Hd. }
  assert (Hcovers : forall x : B, x = a \/ x = b \/ x = c \/ x = d).
  { intro x.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]].
    - auto.
    - auto.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; left; symmetry; exact Hc.
      + right; right; right; symmetry; exact Hd.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
    - subst x. destruct Hc_in as [Hc | Hc];
      destruct Hd_in as [Hd | Hd].
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity.
      + right; right; right; symmetry; exact Hd.
      + right; right; left; symmetry; exact Hc.
      + exfalso. apply Hcd_neq. rewrite Hc, Hd. reflexivity. }
  (* L1 rank: a=0, b=1, c=2, d=3.  L2 rank: b=0, a=1, c=2, d=3. *)
  set (rk1 := fun x : B =>
                if excluded_middle_informative (x = a) then 0%nat
                else if excluded_middle_informative (x = b) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  set (rk2 := fun x : B =>
                if excluded_middle_informative (x = b) then 0%nat
                else if excluded_middle_informative (x = a) then 1%nat
                else if excluded_middle_informative (x = c) then 2%nat
                else 3%nat).
  assert (Hrk1_a : rk1 a = 0%nat).
  { unfold rk1. destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk1_b : rk1 b = 1%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (b = a)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk1_c : rk1 c = 2%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk1_d : rk1 d = 3%nat).
  { unfold rk1.
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk2_a : rk2 a = 1%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (a = b)) as [He|_]; [contradiction Hab_neq; auto |].
    destruct (excluded_middle_informative (a = a)); [reflexivity | contradiction]. }
  assert (Hrk2_b : rk2 b = 0%nat).
  { unfold rk2. destruct (excluded_middle_informative (b = b)); [reflexivity | contradiction]. }
  assert (Hrk2_c : rk2 c = 2%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (c = b)) as [He|_]; [contradiction Hbc_neq; auto |].
    destruct (excluded_middle_informative (c = a)) as [He|_]; [contradiction Hac_neq; auto |].
    destruct (excluded_middle_informative (c = c)); [reflexivity | contradiction]. }
  assert (Hrk2_d : rk2 d = 3%nat).
  { unfold rk2.
    destruct (excluded_middle_informative (d = b)) as [He|_]; [contradiction Hbd_neq; auto |].
    destruct (excluded_middle_informative (d = a)) as [He|_]; [contradiction Had_neq; auto |].
    destruct (excluded_middle_informative (d = c)) as [He|_]; [contradiction Hcd_neq; auto |].
    reflexivity. }
  assert (Hrk1_inj : forall x y, rk1 x = rk1 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in Hxy;
              discriminate ]. }
  assert (Hrk2_inj : forall x y, rk2 x = rk2 y -> x = y).
  { intros x y Hxy.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ reflexivity
            | exfalso;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in Hxy;
              discriminate ]. }
  set (L1 := fun x y : B => rk1 x <= rk1 y).
  set (L2 := fun x y : B => rk2 x <= rk2 y).
  assert (HL1_pos : IsPoset B L1).
  { constructor; unfold L1.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk1_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL1_total : forall x y, L1 x y \/ L1 y x).
  { intros x y. unfold L1. lia. }
  assert (HL1_tot : IsTotalOrder L1).
  { constructor; [exact HL1_pos | exact HL1_total]. }
  assert (HL1_ext : forall x y, R2 x y -> L1 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyc] | [[Hxb Hyc] | [[Hxc Hyd] | [[Hxa Hyd] | [Hxb Hyd]]]]]].
    - subst y. unfold L1. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_c. lia.
    - subst x y. unfold L1. rewrite Hrk1_c, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_a, Hrk1_d. lia.
    - subst x y. unfold L1. rewrite Hrk1_b, Hrk1_d. lia. }
  assert (HL1_lin : IsLinearExtension R2 L1).
  { constructor; [exact HL1_tot | exact HL1_ext]. }
  assert (HL2_pos : IsPoset B L2).
  { constructor; unfold L2.
    - intro x. lia.
    - intros x y Hxy Hyx. apply Hrk2_inj. lia.
    - intros x y z Hxy Hyz. lia. }
  assert (HL2_total : forall x y, L2 x y \/ L2 y x).
  { intros x y. unfold L2. lia. }
  assert (HL2_tot : IsTotalOrder L2).
  { constructor; [exact HL2_pos | exact HL2_total]. }
  assert (HL2_ext : forall x y, R2 x y -> L2 x y).
  { intros x y HR. destruct (HR_only x y HR)
      as [Heq | [[Hxa Hyc] | [[Hxb Hyc] | [[Hxc Hyd] | [[Hxa Hyd] | [Hxb Hyd]]]]]].
    - subst y. unfold L2. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_c. lia.
    - subst x y. unfold L2. rewrite Hrk2_c, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_a, Hrk2_d. lia.
    - subst x y. unfold L2. rewrite Hrk2_b, Hrk2_d. lia. }
  assert (HL2_lin : IsLinearExtension R2 L2).
  { constructor; [exact HL2_tot | exact HL2_ext]. }
  assert (Hinter : forall x y, L1 x y -> L2 x y -> R2 x y).
  { intros x y HLa HLb.
    unfold L1 in HLa; unfold L2 in HLb.
    destruct (Hcovers x) as [Hx|[Hx|[Hx|Hx]]]; subst x;
    destruct (Hcovers y) as [Hy|[Hy|[Hy|Hy]]]; subst y;
      first [ apply HR2.(poset_refl)
            | exact HRac
            | exact HRbc
            | exact HRcd
            | exact HRad
            | exact HRbd
            | exfalso;
              rewrite ?Hrk1_a, ?Hrk1_b, ?Hrk1_c, ?Hrk1_d in HLa;
              rewrite ?Hrk2_a, ?Hrk2_b, ?Hrk2_c, ?Hrk2_d in HLb;
              lia ]. }
  set (rls := Add (B -> B -> Prop) (Singleton _ L1) L2).
  exists rls. split.
  - constructor.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL. exact HL1_lin.
      * destruct HL. exact HL2_lin.
    + intros x y. split.
      * intros HRxy L HL. destruct HL as [L HL | L HL].
        { destruct HL. exact (HL1_lin.(linear_extends) x y HRxy). }
        { destruct HL. exact (HL2_lin.(linear_extends) x y HRxy). }
      * intro Hall.
        assert (HLa : L1 x y)
          by exact (Hall L1 (Union_introl _ _ _ _ (In_singleton _ _))).
        assert (HLb : L2 x y)
          by exact (Hall L2 (Union_intror _ _ _ _ (In_singleton _ _))).
        exact (Hinter x y HLa HLb).
  - assert (HL_neq : L1 <> L2).
    { intro Heq.
      assert (HL1ab : L1 a b) by (unfold L1; rewrite Hrk1_a, Hrk1_b; lia).
      assert (HL2ab : L2 a b) by (rewrite <- Heq; exact HL1ab).
      unfold L2 in HL2ab. rewrite Hrk2_a, Hrk2_b in HL2ab. lia. }
    unfold rls.
    apply card_add.
    + exact (singleton_cardinal _ L1).
    + intro Hin. destruct Hin. apply HL_neq. reflexivity.
Qed.

(** Edge-count = 1 residual: every off-diagonal pair other than
    [(p, q)] is incomparable.

    This is the simplest edge-count bucket of the residual classifier
    (the dispatcher's fall-through after the (a)-(n) labeling tests
    fail).  Given the 10 directed-edge negation hypotheses (all 5
    unordered non-[{p,q}] pairs incomparable in both directions), the
    relation must be [{(x, x) | x in B} ∪ {(p, q)}], which is exactly
    the class (a) shape covered by [n4_one_edge_two_realizer].

    Discharge strategy: existentially introduce [p, q] into
    [n4_one_edge_two_realizer] and case-split on [Hcov4 a] / [Hcov4 b]
    (16 sub-cases) to certify
    [forall a b, R2 a b -> a = b \/ (a = p /\ b = q)].  Each
    off-diagonal case other than [(p, q)] contradicts one of the 10
    edge negations (with the [(q, p)] sub-case using [HRpq] +
    antisymmetry to derive [p = q], contradicting [Hpq_neq]). *)
Lemma n4_residual_edge_count_1 :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 4)
    (p q r s : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hqr_neq : q <> r) (Hqs_neq : q <> s) (Hrs_neq : r <> s)
    (Hcov4 : forall a : B, a = p \/ a = q \/ a = r \/ a = s)
    (HRpq : R2 p q),
  ~ R2 p r -> ~ R2 r p ->
  ~ R2 p s -> ~ R2 s p ->
  ~ R2 q r -> ~ R2 r q ->
  ~ R2 q s -> ~ R2 s q ->
  ~ R2 r s -> ~ R2 s r ->
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard p q r s
    Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4 HRpq
    Hnpr Hnrp Hnps Hnsp Hnqr Hnrq Hnqs Hnsq Hnrs Hnsr.
  apply (@n4_one_edge_two_realizer B R2 HR2 Hcard).
  exists p, q.
  split; [exact Hpq_neq |].
  split; [exact HRpq |].
  intros a b HRab.
  destruct (Hcov4 a) as [Ha | [Ha | [Ha | Ha]]];
  destruct (Hcov4 b) as [Hb | [Hb | [Hb | Hb]]];
    subst a; subst b.
  (* (p, p) *) - left; reflexivity.
  (* (p, q) *) - right; split; reflexivity.
  (* (p, r) *) - contradiction.
  (* (p, s) *) - contradiction.
  (* (q, p) *) - left. apply poset_antisym; [exact HRab | exact HRpq].
  (* (q, q) *) - left; reflexivity.
  (* (q, r) *) - contradiction.
  (* (q, s) *) - contradiction.
  (* (r, p) *) - contradiction.
  (* (r, q) *) - contradiction.
  (* (r, r) *) - left; reflexivity.
  (* (r, s) *) - contradiction.
  (* (s, p) *) - contradiction.
  (* (s, q) *) - contradiction.
  (* (s, r) *) - contradiction.
  (* (s, s) *) - left; reflexivity.
Qed.

(** Edge-count = 2 residual, sub-case "extra edge is [R2 r s]":
    relation is exactly [{(p, q), (r, s)} ∪ diagonal], i.e. class (e)
    DISJOINT CHAINS with witness edges [(p, q)] and [(r, s)].

    Routes to [n4_disjoint_chains_two_realizer]. *)
Lemma n4_residual_edge_count_2_rs :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 4)
    (p q r s : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hqr_neq : q <> r) (Hqs_neq : q <> s) (Hrs_neq : r <> s)
    (Hcov4 : forall a : B, a = p \/ a = q \/ a = r \/ a = s)
    (HRpq : R2 p q) (HRrs : R2 r s),
  ~ R2 p r -> ~ R2 r p ->
  ~ R2 p s -> ~ R2 s p ->
  ~ R2 q r -> ~ R2 r q ->
  ~ R2 q s -> ~ R2 s q ->
  ~ R2 s r ->
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard p q r s
    Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4 HRpq HRrs
    Hnpr Hnrp Hnps Hnsp Hnqr Hnrq Hnqs Hnsq Hnsr.
  apply (@n4_disjoint_chains_two_realizer B R2 HR2 Hcard).
  exists p, q, r, s.
  split; [exact Hpq_neq |].
  split; [exact Hpr_neq |].
  split; [exact Hps_neq |].
  split; [exact Hqr_neq |].
  split; [exact Hqs_neq |].
  split; [exact Hrs_neq |].
  split; [exact HRpq |].
  split; [exact HRrs |].
  intros a b HRab.
  destruct (Hcov4 a) as [Ha | [Ha | [Ha | Ha]]];
  destruct (Hcov4 b) as [Hb | [Hb | [Hb | Hb]]];
    subst a; subst b.
  (* (p, p) *) - left; reflexivity.
  (* (p, q) *) - right; left; split; reflexivity.
  (* (p, r) *) - contradiction.
  (* (p, s) *) - contradiction.
  (* (q, p) *) - left. apply poset_antisym; [exact HRab | exact HRpq].
  (* (q, q) *) - left; reflexivity.
  (* (q, r) *) - contradiction.
  (* (q, s) *) - contradiction.
  (* (r, p) *) - contradiction.
  (* (r, q) *) - contradiction.
  (* (r, r) *) - left; reflexivity.
  (* (r, s) *) - right; right; split; reflexivity.
  (* (s, p) *) - contradiction.
  (* (s, q) *) - contradiction.
  (* (s, r) *) - left. apply poset_antisym; [exact HRab | exact HRrs].
  (* (s, s) *) - left; reflexivity.
Qed.

(** Edge-count = 2 residual, sub-case "extra edge is [R2 s r]":
    relation is exactly [{(p, q), (s, r)} ∪ diagonal], i.e. class (e)
    DISJOINT CHAINS with witness edges [(p, q)] and [(s, r)].

    Routes to [n4_disjoint_chains_two_realizer] with the alternate
    [{r, s}] labeling. *)
Lemma n4_residual_edge_count_2_sr :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 4)
    (p q r s : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hqr_neq : q <> r) (Hqs_neq : q <> s) (Hrs_neq : r <> s)
    (Hcov4 : forall a : B, a = p \/ a = q \/ a = r \/ a = s)
    (HRpq : R2 p q) (HRsr : R2 s r),
  ~ R2 p r -> ~ R2 r p ->
  ~ R2 p s -> ~ R2 s p ->
  ~ R2 q r -> ~ R2 r q ->
  ~ R2 q s -> ~ R2 s q ->
  ~ R2 r s ->
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard p q r s
    Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4 HRpq HRsr
    Hnpr Hnrp Hnps Hnsp Hnqr Hnrq Hnqs Hnsq Hnrs.
  apply (@n4_disjoint_chains_two_realizer B R2 HR2 Hcard).
  exists p, q, s, r.
  split; [exact Hpq_neq |].
  split; [exact Hps_neq |].
  split; [exact Hpr_neq |].
  split; [exact Hqs_neq |].
  split; [exact Hqr_neq |].
  split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
  split; [exact HRpq |].
  split; [exact HRsr |].
  intros a b HRab.
  destruct (Hcov4 a) as [Ha | [Ha | [Ha | Ha]]];
  destruct (Hcov4 b) as [Hb | [Hb | [Hb | Hb]]];
    subst a; subst b.
  (* (p, p) *) - left; reflexivity.
  (* (p, q) *) - right; left; split; reflexivity.
  (* (p, r) *) - contradiction.
  (* (p, s) *) - contradiction.
  (* (q, p) *) - left. apply poset_antisym; [exact HRab | exact HRpq].
  (* (q, q) *) - left; reflexivity.
  (* (q, r) *) - contradiction.
  (* (q, s) *) - contradiction.
  (* (r, p) *) - contradiction.
  (* (r, q) *) - contradiction.
  (* (r, r) *) - left; reflexivity.
  (* (r, s) *) - contradiction.
  (* (s, p) *) - contradiction.
  (* (s, q) *) - contradiction.
  (* (s, r) *) - right; right; split; reflexivity.
  (* (s, s) *) - left; reflexivity.
Qed.

(** Contradictory single-extra-edge residuals (4 lemmas).

    These cover the 4 directed extra-edge choices that, combined with
    the witness [HRpq : R2 p q] and one missing edge negation,
    transitively force an additional edge whose absence is in the
    hypotheses.  Hence the hypothesis set is inconsistent and we close
    the goal by [exfalso].

    Naming: [n4_residual_one_extra_X] where [X] is the directed-edge
    name.  Each takes ONE positive edge and TWO negation hypotheses
    (the transitive consequence + the symmetric direction is not
    needed). *)
Lemma n4_residual_one_extra_rp_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q r : B) (HRpq : R2 p q) (HRrp : R2 r p),
  ~ R2 r q ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q r HRpq HRrp Hnrq P.
  exfalso. apply Hnrq. exact (poset_trans r p q HRrp HRpq).
Qed.

Lemma n4_residual_one_extra_sp_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q s : B) (HRpq : R2 p q) (HRsp : R2 s p),
  ~ R2 s q ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q s HRpq HRsp Hnsq P.
  exfalso. apply Hnsq. exact (poset_trans s p q HRsp HRpq).
Qed.

Lemma n4_residual_one_extra_qr_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q r : B) (HRpq : R2 p q) (HRqr : R2 q r),
  ~ R2 p r ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q r HRpq HRqr Hnpr P.
  exfalso. apply Hnpr. exact (poset_trans p q r HRpq HRqr).
Qed.

Lemma n4_residual_one_extra_qs_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q s : B) (HRpq : R2 p q) (HRqs : R2 q s),
  ~ R2 p s ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q s HRpq HRqs Hnps P.
  exfalso. apply Hnps. exact (poset_trans p q s HRpq HRqs).
Qed.

(** Two-extra-edge contradictions: a witness edge [(p, q)] combined
    with a "below" edge [(r, p)] (resp. [(s, p)]) and an "above" edge
    [(q, r)] (resp. [(q, s)]) creates an antisymmetry contradiction.

    Specifically: [r → p → q] gives [r → q] by transitivity; combined
    with [q → r], antisymmetry forces [r = q], contradicting
    [Hqr_neq].  The [sp+qs] variant is symmetric in [r] vs [s].  These
    discharge the residual-cascade leaves where the dispatcher has
    selected [HRrp ∩ HRqr] (resp. [HRsp ∩ HRqs]) as additional edges
    beyond the witness. *)
Lemma n4_residual_one_extra_rp_qr_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q r : B) (Hqr_neq : q <> r)
    (HRpq : R2 p q) (HRrp : R2 r p) (HRqr : R2 q r),
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q r Hqr_neq HRpq HRrp HRqr P.
  exfalso. apply Hqr_neq.
  apply poset_antisym; [exact HRqr | exact (poset_trans r p q HRrp HRpq)].
Qed.

Lemma n4_residual_one_extra_sp_qs_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q s : B) (Hqs_neq : q <> s)
    (HRpq : R2 p q) (HRsp : R2 s p) (HRqs : R2 q s),
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q s Hqs_neq HRpq HRsp HRqs P.
  exfalso. apply Hqs_neq.
  apply poset_antisym; [exact HRqs | exact (poset_trans s p q HRsp HRpq)].
Qed.

(** Edge composition contradictions that fold a "below" edge into a
    standalone negation hypothesis:

    [s→r + r→p ⇒ s→p] via transitivity; if [~ R2 s p] is in context,
    discharge by exfalso.  The [rs_qp]-variant is symmetric. *)
Lemma n4_residual_one_extra_sr_rp_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p r s : B) (HRsr : R2 s r) (HRrp : R2 r p),
  ~ R2 s p ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p r s HRsr HRrp Hnsp P.
  exfalso. apply Hnsp. exact (poset_trans s r p HRsr HRrp).
Qed.

Lemma n4_residual_one_extra_rs_qp_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p r s : B) (HRrs : R2 r s) (HRsp : R2 s p),
  ~ R2 r p ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p r s HRrs HRsp Hnrp P.
  exfalso. apply Hnrp. exact (poset_trans r s p HRrs HRsp).
Qed.

(** Generic direct-antisymmetry contradiction: [R2 a b] and [R2 b a]
    with [a <> b] is False by antisymmetry. *)
Lemma n4_residual_antisym_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (a b : B) (Hab_neq : a <> b) (HRab : R2 a b) (HRba : R2 b a),
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 a b Hab_neq HRab HRba P.
  exfalso. apply Hab_neq. apply poset_antisym; [exact HRab | exact HRba].
Qed.

(** Generic transitivity contradiction: [R2 a b] and [R2 b c] with
    [~ R2 a c] is False by transitivity.  Subsumes the named
    [n4_residual_one_extra_*_contra] helpers above but is left as a
    convenience for inline rewiring. *)
Lemma n4_residual_trans_contra :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (a b c : B) (HRab : R2 a b) (HRbc : R2 b c),
  ~ R2 a c ->
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 a b c HRab HRbc Hnac P.
  exfalso. apply Hnac. exact (poset_trans a b c HRab HRbc).
Qed.

(** 4-chain incomparability contradiction.  If every pair of elements
    in the 4-element carrier is related (in one direction), then no
    pair is incomparable; this contradicts [Hinc_ex].

    Inputs: a 4-cover [Hcov4] and ordered-pair facts [HR_xy] for each
    of the 6 (unordered) pairs (i.e., one direction holds for each
    pair).  We need 12 ordered facts to discharge the 12 off-diagonal
    cases of the Hcov4 enumeration, plus the 4 diagonal cases via
    reflexivity (which makes [Incomparable a a] False). *)
Lemma n4_chain_contra_inc :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q r s : B)
    (Hcov4 : forall a : B, a = p \/ a = q \/ a = r \/ a = s)
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (Hpq : R2 p q \/ R2 q p)
    (Hpr : R2 p r \/ R2 r p)
    (Hps : R2 p s \/ R2 s p)
    (Hqr : R2 q r \/ R2 r q)
    (Hqs : R2 q s \/ R2 s q)
    (Hrs : R2 r s \/ R2 s r),
  forall (P : Prop), P.
Proof.
  intros B R2 HR2 p q r s Hcov4 Hinc_ex Hpq Hpr Hps Hqr Hqs Hrs P.
  exfalso.
  destruct Hinc_ex as [a [b Hinc]].
  apply Hinc.
  destruct (Hcov4 a) as [Ha | [Ha | [Ha | Ha]]];
  destruct (Hcov4 b) as [Hb | [Hb | [Hb | Hb]]];
    subst a; subst b;
    first
      [ left; apply HR2.(poset_refl)
      | (destruct Hpq as [HRpq | HRqp];
         [left; exact HRpq | right; exact HRqp])
      | (destruct Hpq as [HRpq | HRqp];
         [right; exact HRpq | left; exact HRqp])
      | (destruct Hpr as [HRpr | HRrp];
         [left; exact HRpr | right; exact HRrp])
      | (destruct Hpr as [HRpr | HRrp];
         [right; exact HRpr | left; exact HRrp])
      | (destruct Hps as [HRps | HRsp];
         [left; exact HRps | right; exact HRsp])
      | (destruct Hps as [HRps | HRsp];
         [right; exact HRps | left; exact HRsp])
      | (destruct Hqr as [HRqr | HRrq];
         [left; exact HRqr | right; exact HRrq])
      | (destruct Hqr as [HRqr | HRrq];
         [right; exact HRqr | left; exact HRrq])
      | (destruct Hqs as [HRqs | HRsq];
         [left; exact HRqs | right; exact HRsq])
      | (destruct Hqs as [HRqs | HRsq];
         [right; exact HRqs | left; exact HRsq])
      | (destruct Hrs as [HRrs | HRsr];
         [left; exact HRrs | right; exact HRsr])
      | (destruct Hrs as [HRrs | HRsr];
         [right; exact HRrs | left; exact HRsr]) ].
Qed.

(** Helper: dispatches the remaining six isomorphism classes (i)-(n)
    — diamond, bowtie, chain-of-3 + below/above, Y-up, Y-down — PLUS
    the alternate labelings of classes (b) chain+isolated and (f) N
    where the dispatcher's witness edge [(p, q)] is NOT the canonical
    "first" edge of the class.  Given the witness edge and the
    4-element destructuring [(p, q, r, s)] (distinct, covering
    [Full_set]).

    For each class, the witness edge [(p, q)] can play one of several
    structural roles; this helper enumerates the role × {r, s}-labeling
    cases via [classic] and applies the corresponding per-class Qed
    sub-lemma when the relation matches.

    Test coverage in this helper:
      (i) DIAMOND: D1-D5 (5 labelings)
      (j) BOWTIE: J1, J2 (2 labelings)
      (k) CHAIN3+BELOW: K1a/b, K2a/b, K3a/b, K4a/b (8 labelings)
      (l) CHAIN3+ABOVE: L1a/b, L2a/b, L3a/b, L4a/b (8 labelings)
      (m) Y-UP: M1, M2a/b, M3a/b (5 labelings)
      (n) Y-DOWN: N1a/b, N2a, N3a/b (5 labelings)
      (b) CHAIN+ISOLATED alt: B2a/b (witness=chain step 2), B3a/b
          (witness=transitive edge) — 4 labelings
      (f) N alt: F2a/b (witness=c→b), F3a/b (witness=c→d) — 4 labelings

    Status: every (a)-(n) labeling is now covered by an explicit
    Qed-routed branch via per-class lemmas plus inline edge enumeration
    in the tail cascades (covering the residual configurations the
    pattern tests miss).  No admit-routed fall-through remains. *)
Lemma n4_dispatch_residual_after_h :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 4)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hqr_neq : q <> r) (Hqs_neq : q <> s) (Hrs_neq : r <> s)
    (Hcov4 : forall a : B, a = p \/ a = q \/ a = r \/ a = s)
    (HRpq : R2 p q),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s
    Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4 HRpq.
  (* For repeated re-use throughout the cascade, factor a few neq
     facts in the "flipped" direction. *)
  assert (Hqp_neq : q <> p) by (intro Heq; apply Hpq_neq; symmetry; exact Heq).
  assert (Hrp_neq : r <> p) by (intro Heq; apply Hpr_neq; symmetry; exact Heq).
  assert (Hsp_neq : s <> p) by (intro Heq; apply Hps_neq; symmetry; exact Heq).
  assert (Hrq_neq : r <> q) by (intro Heq; apply Hqr_neq; symmetry; exact Heq).
  assert (Hsq_neq : s <> q) by (intro Heq; apply Hqs_neq; symmetry; exact Heq).
  assert (Hsr_neq : s <> r) by (intro Heq; apply Hrs_neq; symmetry; exact Heq).
  (* === Class (i) DIAMOMD : edges a→b, a→c, a→d, b→d, c→d ===*)
  (* D1: a=p, b=q, c=r, d=s.  Edges p→q, p→r, p→s, q→s, r→s. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 q s /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = r) \/
                       (x = p /\ y = s) \/ (x = q /\ y = s) \/
                       (x = r /\ y = s))) as [HD1 | HnD1].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD1 as [HRpr [HRps [HRqs [HRrs HR_only]]]].
    exists p, q, r, s.
    repeat (split; [first [exact Hpq_neq | exact Hpr_neq | exact Hps_neq
                          | exact Hqr_neq | exact Hqs_neq | exact Hrs_neq
                          | exact HRpq | exact HRpr | exact HRps
                          | exact HRqs | exact HRrs] |]).
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D2: a=p, b=q, c=s, d=r.  Edges p→q, p→s, p→r, q→r, s→r. *)
  destruct (classic (R2 p s /\ R2 p r /\ R2 q r /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = s) \/
                       (x = p /\ y = r) \/ (x = q /\ y = r) \/
                       (x = s /\ y = r))) as [HD2 | HnD2].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD2 as [HRps [HRpr [HRqr [HRsr HR_only]]]].
    exists p, q, s, r.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hsr_neq |].
    split; [exact HRpq |].
    split; [exact HRps |].
    split; [exact HRpr |].
    split; [exact HRqr |].
    split; [exact HRsr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D3: a=p, b=r, c=s, d=q.  Edges p→r, p→s, p→q, r→q, s→q. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = s) \/
                       (x = p /\ y = q) \/ (x = r /\ y = q) \/
                       (x = s /\ y = q))) as [HD3 | HnD3].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD3 as [HRpr [HRps [HRrq [HRsq HR_only]]]].
    exists p, r, s, q.
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsq_neq |].
    split; [exact HRpr |].
    split; [exact HRps |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D4: a=r, b=p, c=s, d=q.  Edges r→p, r→s, r→q, p→q, s→q. *)
  destruct (classic (R2 r p /\ R2 r s /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = p) \/ (x = r /\ y = s) \/
                       (x = r /\ y = q) \/ (x = p /\ y = q) \/
                       (x = s /\ y = q))) as [HD4 | HnD4].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD4 as [HRrp [HRrs [HRrq [HRsq HR_only]]]].
    exists r, p, s, q.
    split; [exact Hrp_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hsq_neq |].
    split; [exact HRrp |].
    split; [exact HRrs |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D5: a=s, b=p, c=r, d=q.  Edges s→p, s→r, s→q, p→q, r→q. *)
  destruct (classic (R2 s p /\ R2 s r /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = p) \/ (x = s /\ y = r) \/
                       (x = s /\ y = q) \/ (x = p /\ y = q) \/
                       (x = r /\ y = q))) as [HD5 | HnD5].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD5 as [HRsp [HRsr [HRsq [HRrq HR_only]]]].
    exists s, p, r, q.
    split; [exact Hsp_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hrq_neq |].
    split; [exact HRsp |].
    split; [exact HRsr |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D3b: a=p, b=s, c=r, d=q.  Edges p→r, p→s, p→q, s→q, r→q.
     Witness=(a,d)=(p,q), with residue r=c, s=b. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = r) \/
                       (x = p /\ y = q) \/ (x = s /\ y = q) \/
                       (x = r /\ y = q))) as [HD3b | HnD3b].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD3b as [HRpr [HRps [HRsq [HRrq HR_only]]]].
    exists p, s, r, q.
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hrq_neq |].
    split; [exact HRps |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D6a: a=p, b=r, c=q, d=s.  Edges p→r, p→q, p→s, r→s, q→s.
     Witness=(a,c)=(p,q), with residue r=b, s=d. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 r s /\ R2 q s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = q) \/
                       (x = p /\ y = s) \/ (x = r /\ y = s) \/
                       (x = q /\ y = s))) as [HD6a | HnD6a].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD6a as [HRpr [HRps [HRrs [HRqs HR_only]]]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    split; [exact HRps |].
    split; [exact HRrs |].
    split; [exact HRqs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D6b: a=p, b=s, c=q, d=r.  Edges p→s, p→q, p→r, s→r, q→r.
     Witness=(a,c)=(p,q), with residue r=d, s=b. *)
  destruct (classic (R2 p s /\ R2 p r /\ R2 s r /\ R2 q r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = q) \/
                       (x = p /\ y = r) \/ (x = s /\ y = r) \/
                       (x = q /\ y = r))) as [HD6b | HnD6b].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD6b as [HRps [HRpr [HRsr [HRqr HR_only]]]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRps |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    split; [exact HRsr |].
    split; [exact HRqr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D7a: a=r, b=s, c=p, d=q.  Edges r→s, r→p, r→q, s→q, p→q.
     Witness=(c,d)=(p,q), with a=r, b=s. *)
  destruct (classic (R2 r s /\ R2 r p /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = s) \/ (x = r /\ y = p) \/
                       (x = r /\ y = q) \/ (x = s /\ y = q) \/
                       (x = p /\ y = q))) as [HD7a | HnD7a].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD7a as [HRrs [HRrp [HRrq [HRsq HR_only]]]].
    exists r, s, p, q.
    split; [exact Hrs_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hpq_neq |].
    split; [exact HRrs |].
    split; [exact HRrp |].
    split; [exact HRrq |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* D7b: a=s, b=r, c=p, d=q.  Edges s→r, s→p, s→q, r→q, p→q.
     Witness=(c,d)=(p,q), with a=s, b=r. *)
  destruct (classic (R2 s r /\ R2 s p /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = r) \/ (x = s /\ y = p) \/
                       (x = s /\ y = q) \/ (x = r /\ y = q) \/
                       (x = p /\ y = q))) as [HD7b | HnD7b].
  { apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
    destruct HD7b as [HRsr [HRsp [HRsq [HRrq HR_only]]]].
    exists s, r, p, q.
    split; [exact Hsr_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hpq_neq |].
    split; [exact HRsr |].
    split; [exact HRsp |].
    split; [exact HRsq |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* === Class (j) BOWTIE : edges a→c, a→d, b→c, b→d === *)
  (* J1: a=p, b=r, c=q, d=s.  Edges p→q, p→s, r→q, r→s. *)
  destruct (classic (R2 p s /\ R2 r q /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = s) \/
                       (x = r /\ y = q) \/ (x = r /\ y = s)))
    as [HJ1 | HnJ1].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ1 as [HRps [HRrq [HRrs HR_only]]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpq |].
    split; [exact HRps |].
    split; [exact HRrq |].
    split; [exact HRrs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J2: a=p, b=s, c=q, d=r.  Edges p→q, p→r, s→q, s→r. *)
  destruct (classic (R2 p r /\ R2 s q /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = r) \/
                       (x = s /\ y = q) \/ (x = s /\ y = r)))
    as [HJ2 | HnJ2].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ2 as [HRpr [HRsq [HRsr HR_only]]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    split; [exact HRsq |].
    split; [exact HRsr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J3a: a=p, b=r, c=s, d=q.  Edges p→s, p→q, r→s, r→q.
     Witness=(a,d)=(p,q), residue r=b, s=c. *)
  destruct (classic (R2 p s /\ R2 r s /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = q) \/
                       (x = r /\ y = s) \/ (x = r /\ y = q)))
    as [HJ3a | HnJ3a].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ3a as [HRps [HRrs [HRrq HR_only]]].
    exists p, r, s, q.
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsq_neq |].
    split; [exact HRps |].
    split; [exact HRpq |].
    split; [exact HRrs |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J3b: a=p, b=s, c=r, d=q.  Edges p→r, p→q, s→r, s→q.
     Witness=(a,d)=(p,q), residue r=c, s=b. *)
  destruct (classic (R2 p r /\ R2 s r /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = q) \/
                       (x = s /\ y = r) \/ (x = s /\ y = q)))
    as [HJ3b | HnJ3b].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ3b as [HRpr [HRsr [HRsq HR_only]]].
    exists p, s, r, q.
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hrq_neq |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    split; [exact HRsr |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J4a: a=r, b=p, c=q, d=s.  Edges r→q, r→s, p→q, p→s.
     Witness=(b,c)=(p,q), residue r=a, s=d. *)
  destruct (classic (R2 r q /\ R2 r s /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = q) \/ (x = r /\ y = s) \/
                       (x = p /\ y = q) \/ (x = p /\ y = s)))
    as [HJ4a | HnJ4a].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ4a as [HRrq [HRrs [HRps HR_only]]].
    exists r, p, q, s.
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRrq |].
    split; [exact HRrs |].
    split; [exact HRpq |].
    split; [exact HRps |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J4b: a=s, b=p, c=q, d=r.  Edges s→q, s→r, p→q, p→r.
     Witness=(b,c)=(p,q), residue r=d, s=a. *)
  destruct (classic (R2 s q /\ R2 s r /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = q) \/ (x = s /\ y = r) \/
                       (x = p /\ y = q) \/ (x = p /\ y = r)))
    as [HJ4b | HnJ4b].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ4b as [HRsq [HRsr [HRpr HR_only]]].
    exists s, p, q, r.
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRsq |].
    split; [exact HRsr |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J5a: a=r, b=p, c=s, d=q.  Edges r→s, r→q, p→s, p→q.
     Witness=(b,d)=(p,q), residue r=a, s=c. *)
  destruct (classic (R2 r s /\ R2 r q /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = s) \/ (x = r /\ y = q) \/
                       (x = p /\ y = s) \/ (x = p /\ y = q)))
    as [HJ5a | HnJ5a].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ5a as [HRrs [HRrq [HRps HR_only]]].
    exists r, p, s, q.
    split; [exact Hrp_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hsq_neq |].
    split; [exact HRrs |].
    split; [exact HRrq |].
    split; [exact HRps |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* J5b: a=s, b=p, c=r, d=q.  Edges s→r, s→q, p→r, p→q.
     Witness=(b,d)=(p,q), residue r=c, s=a. *)
  destruct (classic (R2 s r /\ R2 s q /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = r) \/ (x = s /\ y = q) \/
                       (x = p /\ y = r) \/ (x = p /\ y = q)))
    as [HJ5b | HnJ5b].
  { apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
    destruct HJ5b as [HRsr [HRsq [HRpr HR_only]]].
    exists s, p, r, q.
    split; [exact Hsp_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hrq_neq |].
    split; [exact HRsr |].
    split; [exact HRsq |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* === Class (k) CHAIN3 + BELOW : edges a→b, a→c, b→c, a→d === *)
  (* K1a: a=p, b=q, c=r, d=s.  Edges p→q, p→r, q→r, p→s. *)
  destruct (classic (R2 p r /\ R2 q r /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = r) \/
                       (x = q /\ y = r) \/ (x = p /\ y = s)))
    as [HK1a | HnK1a].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK1a as [HRpr [HRqr [HRps HR_only]]].
    exists p, q, r, s.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    split; [exact HRqr |].
    split; [exact HRps |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K1b: a=p, b=q, c=s, d=r.  Edges p→q, p→s, q→s, p→r. *)
  destruct (classic (R2 p s /\ R2 q s /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = s) \/
                       (x = q /\ y = s) \/ (x = p /\ y = r)))
    as [HK1b | HnK1b].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK1b as [HRps [HRqs [HRpr HR_only]]].
    exists p, q, s, r.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hsr_neq |].
    split; [exact HRpq |].
    split; [exact HRps |].
    split; [exact HRqs |].
    split; [exact HRpr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K2a: a=p, b=r, c=q, d=s.  Edges p→q, p→r, r→q, p→s. *)
  destruct (classic (R2 p r /\ R2 r q /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = q) \/
                       (x = r /\ y = q) \/ (x = p /\ y = s)))
    as [HK2a | HnK2a].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK2a as [HRpr [HRrq [HRps HR_only]]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    split; [exact HRps |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K2b: a=p, b=s, c=q, d=r.  Edges p→q, p→s, s→q, p→r. *)
  destruct (classic (R2 p s /\ R2 s q /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = q) \/
                       (x = s /\ y = q) \/ (x = p /\ y = r)))
    as [HK2b | HnK2b].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK2b as [HRps [HRsq [HRpr HR_only]]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRps |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    split; [exact HRpr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K3a: a=r, b=p, c=q, d=s.  Edges r→p, r→q, p→q, r→s. *)
  destruct (classic (R2 r p /\ R2 r q /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = p) \/ (x = r /\ y = q) \/
                       (x = p /\ y = q) \/ (x = r /\ y = s)))
    as [HK3a | HnK3a].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK3a as [HRrp [HRrq [HRrs HR_only]]].
    exists r, p, q, s.
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRrp |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    split; [exact HRrs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K3b: a=s, b=p, c=q, d=r.  Edges s→p, s→q, p→q, s→r. *)
  destruct (classic (R2 s p /\ R2 s q /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = p) \/ (x = s /\ y = q) \/
                       (x = p /\ y = q) \/ (x = s /\ y = r)))
    as [HK3b | HnK3b].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK3b as [HRsp [HRsq [HRsr HR_only]]].
    exists s, p, q, r.
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRsp |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    split; [exact HRsr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K4a: a=p, b=r, c=s, d=q.  Edges p→r, p→s, r→s, p→q. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = s) \/
                       (x = r /\ y = s) \/ (x = p /\ y = q)))
    as [HK4a | HnK4a].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK4a as [HRpr [HRps [HRrs HR_only]]].
    exists p, r, s, q.
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsq_neq |].
    split; [exact HRpr |].
    split; [exact HRps |].
    split; [exact HRrs |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* K4b: a=p, b=s, c=r, d=q.  Edges p→s, p→r, s→r, p→q. *)
  destruct (classic (R2 p s /\ R2 p r /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = r) \/
                       (x = s /\ y = r) \/ (x = p /\ y = q)))
    as [HK4b | HnK4b].
  { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
    destruct HK4b as [HRps [HRpr [HRsr HR_only]]].
    exists p, s, r, q.
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hrq_neq |].
    split; [exact HRps |].
    split; [exact HRpr |].
    split; [exact HRsr |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* === Class (l) CHAIN3 + ABOVE : edges a→b, a→c, b→c, d→c === *)
  (* L1a: a=p, b=q, c=r, d=s.  Edges p→q, p→r, q→r, s→r. *)
  destruct (classic (R2 p r /\ R2 q r /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = r) \/
                       (x = q /\ y = r) \/ (x = s /\ y = r)))
    as [HL1a | HnL1a].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL1a as [HRpr [HRqr [HRsr HR_only]]].
    exists p, q, r, s.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    split; [exact HRqr |].
    split; [exact HRsr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L1b: a=p, b=q, c=s, d=r.  Edges p→q, p→s, q→s, r→s. *)
  destruct (classic (R2 p s /\ R2 q s /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = s) \/
                       (x = q /\ y = s) \/ (x = r /\ y = s)))
    as [HL1b | HnL1b].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL1b as [HRps [HRqs [HRrs HR_only]]].
    exists p, q, s, r.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hsr_neq |].
    split; [exact HRpq |].
    split; [exact HRps |].
    split; [exact HRqs |].
    split; [exact HRrs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L2a: a=p, b=r, c=q, d=s.  Edges p→r, p→q, r→q, s→q. *)
  destruct (classic (R2 p r /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = q) \/
                       (x = r /\ y = q) \/ (x = s /\ y = q)))
    as [HL2a | HnL2a].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL2a as [HRpr [HRrq [HRsq HR_only]]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L2b: a=p, b=s, c=q, d=r.  Edges p→s, p→q, s→q, r→q. *)
  destruct (classic (R2 p s /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = q) \/
                       (x = s /\ y = q) \/ (x = r /\ y = q)))
    as [HL2b | HnL2b].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL2b as [HRps [HRsq [HRrq HR_only]]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRps |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L3a: a=r, b=p, c=q, d=s.  Edges r→p, r→q, p→q, s→q. *)
  destruct (classic (R2 r p /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = p) \/ (x = r /\ y = q) \/
                       (x = p /\ y = q) \/ (x = s /\ y = q)))
    as [HL3a | HnL3a].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL3a as [HRrp [HRrq [HRsq HR_only]]].
    exists r, p, q, s.
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRrp |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L3b: a=s, b=p, c=q, d=r.  Edges s→p, s→q, p→q, r→q. *)
  destruct (classic (R2 s p /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = p) \/ (x = s /\ y = q) \/
                       (x = p /\ y = q) \/ (x = r /\ y = q)))
    as [HL3b | HnL3b].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL3b as [HRsp [HRsq [HRrq HR_only]]].
    exists s, p, q, r.
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRsp |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L4a: a=r, b=s, c=q, d=p.  Edges r→s, r→q, s→q, p→q. *)
  destruct (classic (R2 r s /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = s) \/ (x = r /\ y = q) \/
                       (x = s /\ y = q) \/ (x = p /\ y = q)))
    as [HL4a | HnL4a].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL4a as [HRrs [HRrq [HRsq HR_only]]].
    exists r, s, q, p.
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hqp_neq |].
    split; [exact HRrs |].
    split; [exact HRrq |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* L4b: a=s, b=r, c=q, d=p.  Edges s→r, s→q, r→q, p→q. *)
  destruct (classic (R2 s r /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = r) \/ (x = s /\ y = q) \/
                       (x = r /\ y = q) \/ (x = p /\ y = q)))
    as [HL4b | HnL4b].
  { apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
    destruct HL4b as [HRsr [HRsq [HRrq HR_only]]].
    exists s, r, q, p.
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hqp_neq |].
    split; [exact HRsr |].
    split; [exact HRsq |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | HM]]];
      [ left | right; left | right; right; left | right; right; right ];
      exact HM. }
  (* === Class (m) Y-UP : edges a→b, a→c, a→d, b→c, b→d === *)
  (* M1: a=p, b=q, c=r, d=s.  Edges p→q, p→r, p→s, q→r, q→s. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 q r /\ R2 q s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = p /\ y = r) \/
                       (x = p /\ y = s) \/ (x = q /\ y = r) \/
                       (x = q /\ y = s)))
    as [HM1 | HnM1].
  { apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
    destruct HM1 as [HRpr [HRps [HRqr [HRqs HR_only]]]].
    exists p, q, r, s.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    split; [exact HRps |].
    split; [exact HRqr |].
    split; [exact HRqs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* M2a: a=p, b=r, c=q, d=s.  Edges p→r, p→q, p→s, r→q, r→s. *)
  destruct (classic (R2 p r /\ R2 p s /\ R2 r q /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = p /\ y = q) \/
                       (x = p /\ y = s) \/ (x = r /\ y = q) \/
                       (x = r /\ y = s)))
    as [HM2a | HnM2a].
  { apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
    destruct HM2a as [HRpr [HRps [HRrq [HRrs HR_only]]]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    split; [exact HRps |].
    split; [exact HRrq |].
    split; [exact HRrs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* M2b: a=p, b=s, c=q, d=r.  Edges p→s, p→q, p→r, s→q, s→r. *)
  destruct (classic (R2 p s /\ R2 p r /\ R2 s q /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = p /\ y = q) \/
                       (x = p /\ y = r) \/ (x = s /\ y = q) \/
                       (x = s /\ y = r)))
    as [HM2b | HnM2b].
  { apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
    destruct HM2b as [HRps [HRpr [HRsq [HRsr HR_only]]]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRps |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    split; [exact HRsq |].
    split; [exact HRsr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* M3a: a=r, b=p, c=q, d=s.  Edges r→p, r→q, r→s, p→q, p→s. *)
  destruct (classic (R2 r p /\ R2 r q /\ R2 r s /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = p) \/ (x = r /\ y = q) \/
                       (x = r /\ y = s) \/ (x = p /\ y = q) \/
                       (x = p /\ y = s)))
    as [HM3a | HnM3a].
  { apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
    destruct HM3a as [HRrp [HRrq [HRrs [HRps HR_only]]]].
    exists r, p, q, s.
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRrp |].
    split; [exact HRrq |].
    split; [exact HRrs |].
    split; [exact HRpq |].
    split; [exact HRps |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* M3b: a=s, b=p, c=q, d=r.  Edges s→p, s→q, s→r, p→q, p→r. *)
  destruct (classic (R2 s p /\ R2 s q /\ R2 s r /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = p) \/ (x = s /\ y = q) \/
                       (x = s /\ y = r) \/ (x = p /\ y = q) \/
                       (x = p /\ y = r)))
    as [HM3b | HnM3b].
  { apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
    destruct HM3b as [HRsp [HRsq [HRsr [HRpr HR_only]]]].
    exists s, p, q, r.
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRsp |].
    split; [exact HRsq |].
    split; [exact HRsr |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* === Class (n) Y-DOWN : edges a→c, b→c, c→d, a→d, b→d === *)
  (* N1a: a=p, b=r, c=q, d=s.  Edges p→q, r→q, q→s, p→s, r→s. *)
  destruct (classic (R2 r q /\ R2 q s /\ R2 p s /\ R2 r s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = r /\ y = q) \/
                       (x = q /\ y = s) \/ (x = p /\ y = s) \/
                       (x = r /\ y = s)))
    as [HN1a | HnN1a].
  { apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
    destruct HN1a as [HRrq [HRqs [HRps [HRrs HR_only]]]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    split; [exact HRqs |].
    split; [exact HRps |].
    split; [exact HRrs |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* N1b: a=p, b=s, c=q, d=r.  Edges p→q, s→q, q→r, p→r, s→r. *)
  destruct (classic (R2 s q /\ R2 q r /\ R2 p r /\ R2 s r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = q) \/ (x = s /\ y = q) \/
                       (x = q /\ y = r) \/ (x = p /\ y = r) \/
                       (x = s /\ y = r)))
    as [HN1b | HnN1b].
  { apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
    destruct HN1b as [HRsq [HRqr [HRpr [HRsr HR_only]]]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    split; [exact HRqr |].
    split; [exact HRpr |].
    split; [exact HRsr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* N2a: a=r, b=s, c=p, d=q.  Edges r→p, s→p, p→q, r→q, s→q. *)
  destruct (classic (R2 r p /\ R2 s p /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = p) \/ (x = s /\ y = p) \/
                       (x = p /\ y = q) \/ (x = r /\ y = q) \/
                       (x = s /\ y = q)))
    as [HN2a | HnN2a].
  { apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
    destruct HN2a as [HRrp [HRsp [HRrq [HRsq HR_only]]]].
    exists r, s, p, q.
    split; [exact Hrs_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hpq_neq |].
    split; [exact HRrp |].
    split; [exact HRsp |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* N3a: a=p, b=r, c=s, d=q.  Edges p→s, r→s, s→q, p→q, r→q. *)
  destruct (classic (R2 p s /\ R2 r s /\ R2 s q /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = r /\ y = s) \/
                       (x = s /\ y = q) \/ (x = p /\ y = q) \/
                       (x = r /\ y = q)))
    as [HN3a | HnN3a].
  { apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
    destruct HN3a as [HRps [HRrs [HRsq [HRrq HR_only]]]].
    exists p, r, s, q.
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsq_neq |].
    split; [exact HRps |].
    split; [exact HRrs |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* N3b: a=p, b=s, c=r, d=q.  Edges p→r, s→r, r→q, p→q, s→q. *)
  destruct (classic (R2 p r /\ R2 s r /\ R2 r q /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = s /\ y = r) \/
                       (x = r /\ y = q) \/ (x = p /\ y = q) \/
                       (x = s /\ y = q)))
    as [HN3b | HnN3b].
  { apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
    destruct HN3b as [HRpr [HRsr [HRrq [HRsq HR_only]]]].
    exists p, s, r, q.
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hrq_neq |].
    split; [exact HRpr |].
    split; [exact HRsr |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | [HM | [HM | HM]]]];
      [ left | right; left | right; right; left
      | right; right; right; left | right; right; right; right ];
      exact HM. }
  (* === Class (b) CHAIN+ISOLATED, alternate labelings where the
         witness edge (p, q) is NOT the first chain step ===
     The outer dispatcher's (b) test only handles witness=a→b; here we
     cover witness=b→c and witness=a→c. *)
  (* B2a: a=r, b=p, c=q, d=s.  Edges r→p, p→q, r→q. *)
  destruct (classic (R2 r p /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = p) \/ (x = p /\ y = q) \/
                       (x = r /\ y = q)))
    as [HB2a | HnB2a].
  { apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
    destruct HB2a as [HRrp [HRrq HR_only]].
    exists r, p, q, s.
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRrp |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; right | right; left ];
      exact HM. }
  (* B2b: a=s, b=p, c=q, d=r.  Edges s→p, p→q, s→q. *)
  destruct (classic (R2 s p /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = p) \/ (x = p /\ y = q) \/
                       (x = s /\ y = q)))
    as [HB2b | HnB2b].
  { apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
    destruct HB2b as [HRsp [HRsq HR_only]].
    exists s, p, q, r.
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRsp |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; right | right; left ];
      exact HM. }
  (* B3a: a=p, b=r, c=q, d=s.  Edges p→r, r→q, p→q. *)
  destruct (classic (R2 p r /\ R2 r q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = r) \/ (x = r /\ y = q) \/
                       (x = p /\ y = q)))
    as [HB3a | HnB3a].
  { apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
    destruct HB3a as [HRpr [HRrq HR_only]].
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpr |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; right | right; left ];
      exact HM. }
  (* B3b: a=p, b=s, c=q, d=r.  Edges p→s, s→q, p→q. *)
  destruct (classic (R2 p s /\ R2 s q /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = p /\ y = s) \/ (x = s /\ y = q) \/
                       (x = p /\ y = q)))
    as [HB3b | HnB3b].
  { apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
    destruct HB3b as [HRps [HRsq HR_only]].
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqr_neq |].
    split; [exact HRps |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; right | right; left ];
      exact HM. }
  (* === Class (f) N, alternate labelings where the witness edge (p, q)
         is NOT the (a→b) edge.  Lemma signature: R2 a b /\ R2 c b /\ R2 c d.
         Outer dispatcher covers witness=(a,b); here we cover
         witness=(c,b) and witness=(c,d). *)
  (* F2a: a=r, b=q, c=p, d=s.  Edges r→q, p→q, p→s. *)
  destruct (classic (R2 r q /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = q) \/ (x = p /\ y = q) \/
                       (x = p /\ y = s)))
    as [HF2a | HnF2a].
  { apply (@n4_N_two_realizer B R2 HR2 Hcard).
    destruct HF2a as [HRrq [HRps HR_only]].
    exists r, q, p, s.
    split; [exact Hrq_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqp_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hps_neq |].
    split; [exact HRrq |].
    split; [exact HRpq |].
    split; [exact HRps |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; left | right; right ];
      exact HM. }
  (* F2b: a=s, b=q, c=p, d=r.  Edges s→q, p→q, p→r. *)
  destruct (classic (R2 s q /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = q) \/ (x = p /\ y = q) \/
                       (x = p /\ y = r)))
    as [HF2b | HnF2b].
  { apply (@n4_N_two_realizer B R2 HR2 Hcard).
    destruct HF2b as [HRsq [HRpr HR_only]].
    exists s, q, p, r.
    split; [exact Hsq_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hsr_neq |].
    split; [exact Hqp_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hpr_neq |].
    split; [exact HRsq |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; left | right; right ];
      exact HM. }
  (* F3a: a=r, b=s, c=p, d=q.  Edges r→s, p→s, p→q. *)
  destruct (classic (R2 r s /\ R2 p s /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = r /\ y = s) \/ (x = p /\ y = s) \/
                       (x = p /\ y = q)))
    as [HF3a | HnF3a].
  { apply (@n4_N_two_realizer B R2 HR2 Hcard).
    destruct HF3a as [HRrs [HRps HR_only]].
    exists r, s, p, q.
    split; [exact Hrs_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hpq_neq |].
    split; [exact HRrs |].
    split; [exact HRps |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; left | right; right ];
      exact HM. }
  (* F3b: a=s, b=r, c=p, d=q.  Edges s→r, p→r, p→q. *)
  destruct (classic (R2 s r /\ R2 p r /\
                     forall x y : B, x <> y -> R2 x y ->
                       (x = s /\ y = r) \/ (x = p /\ y = r) \/
                       (x = p /\ y = q)))
    as [HF3b | HnF3b].
  { apply (@n4_N_two_realizer B R2 HR2 Hcard).
    destruct HF3b as [HRsr [HRpr HR_only]].
    exists s, r, p, q.
    split; [exact Hsr_neq |].
    split; [exact Hsp_neq |].
    split; [exact Hsq_neq |].
    split; [exact Hrp_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hpq_neq |].
    split; [exact HRsr |].
    split; [exact HRpr |].
    split; [exact HRpq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (HR_only x y Hneq HRxy)
      as [HM | [HM | HM]];
      [ left | right; left | right; right ];
      exact HM. }
  (* If we reach here, the relation matches no class-(b)..(n) labeling
     above.  Before falling through to the focused admit
     [n4_residual_classes_two_realizer], we discharge several
     edge-count buckets directly via classical decisions on the 10
     directed edges of the 5 non-[{p,q}] pairs:

     - all 10 absent → class (a) via [n4_residual_edge_count_1].
     - exactly [R2 r s] present, others absent → class (e) via
       [n4_residual_edge_count_2_rs].
     - exactly [R2 s r] present, others absent → class (e) via
       [n4_residual_edge_count_2_sr].
     - 4 contradictory single-extra-edge configs (r→p, s→p, q→r, q→s
       with all others absent) discharge by transitivity + edge
       negation via the [n4_residual_one_extra_*_contra] lemmas.

     All OTHER patterns (multi-edge configs) fall through to
     [n4_residual_classes_two_realizer]. *)
  destruct (classic (R2 p r)) as [HRpr | Hnpr].
  { (* Inside HRpr: case-split on r→p (antisym contradiction) and on
       extras that match residual classifier patterns. *)
    destruct (classic (R2 r p)) as [HRrp | Hnrp].
    { (* p→r and r→p ⇒ p = r by antisymmetry, contradicting Hpr_neq. *)
      apply (@n4_residual_antisym_contra B R2 HR2 p r Hpr_neq HRpr HRrp). }
    destruct (classic (R2 s q)) as [HRsq | Hnsq].
    { (* HRsq + HRpq + HRpr always present.  Hnrp from outer.  Enumerate
         remaining undecided edges:
         R2 q s (antisym contra),
         R2 s p (forces HRsr; sub-cascade with chain or Y_chain_up),
         R2 r s (forces HRrq + HRps; 4-chain contra),
         R2 s r (sub-cascade: bowtie, Y_chain_down, Y_chain_up, chain contra),
         else (R2 q r forces HRsr but Hnsr; R2 r q + R2 p s ⇒ diamond;
               R2 r q alone ⇒ chain3+above; R2 p s alone ⇒ chain3+below;
               no extras ⇒ HnF2b N-pattern). *)
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { apply (@n4_residual_antisym_contra B R2 HR2 q s Hqs_neq HRqs HRsq). }
      destruct (classic (R2 s p)) as [HRsp | Hnsp].
      { (* HRsp + HRpr ⇒ HRsr forced. *)
        assert (HRsr : R2 s r) by exact (poset_trans s p r HRsp HRpr).
        destruct (classic (R2 p s)) as [HRps | Hnps].
        { apply (@n4_residual_antisym_contra B R2 HR2 p s Hps_neq HRps HRsp). }
        destruct (classic (R2 r s)) as [HRrs | Hnrs].
        { apply (@n4_residual_antisym_contra B R2 HR2 r s Hrs_neq HRrs HRsr). }
        destruct (classic (R2 q r)) as [HRqr | Hnqr].
        { (* Edges {s→p, s→q, s→r, p→q, p→r, q→r} all present ⇒ 4-chain s<p<q<r. *)
          assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
          assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
          assert (Hps_cmp : R2 p s \/ R2 s p) by (right; exact HRsp).
          assert (Hqr_cmp : R2 q r \/ R2 r q) by (left; exact HRqr).
          assert (Hqs_cmp : R2 q s \/ R2 s q) by (right; exact HRsq).
          assert (Hrs_cmp : R2 r s \/ R2 s r) by (right; exact HRsr).
          exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                   Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
        destruct (classic (R2 r q)) as [HRrq | Hnrq].
        { (* Edges {sp, sq, sr, pq, pr, rq} all present ⇒ 4-chain s<p<r<q. *)
          assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
          assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
          assert (Hps_cmp : R2 p s \/ R2 s p) by (right; exact HRsp).
          assert (Hqr_cmp : R2 q r \/ R2 r q) by (right; exact HRrq).
          assert (Hqs_cmp : R2 q s \/ R2 s q) by (right; exact HRsq).
          assert (Hrs_cmp : R2 r s \/ R2 s r) by (right; exact HRsr).
          exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                   Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
        (* Edges {sp, sq, sr, pq, pr}.  Y_chain_up with a=s, b=p, c=q, d=r. *)
        apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
        exists s, p, q, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRsp |].
        split; [exact HRsq |].
        split; [exact HRsr |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                                (* (s,p) *)
            | (right; left; split; reflexivity)                         (* (s,q) *)
            | (right; right; left; split; reflexivity)                  (* (s,r) *)
            | (right; right; right; left; split; reflexivity)           (* (p,q) *)
            | (right; right; right; right; split; reflexivity)          (* (p,r) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* HRrs + HRsq ⇒ HRrq.  HRpr + HRrs ⇒ HRps.  4-chain p<r<s<q. *)
        assert (HRrq : R2 r q) by exact (poset_trans r s q HRrs HRsq).
        assert (HRps : R2 p s) by exact (poset_trans p r s HRpr HRrs).
        assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
        assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
        assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
        assert (Hqr_cmp : R2 q r \/ R2 r q) by (right; exact HRrq).
        assert (Hqs_cmp : R2 q s \/ R2 s q) by (right; exact HRsq).
        assert (Hrs_cmp : R2 r s \/ R2 s r) by (left; exact HRrs).
        exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                 Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { (* HRpq, HRpr, HRsq, HRsr.  Sub-cascade. *)
        destruct (classic (R2 q r)) as [HRqr | Hnqr].
        { destruct (classic (R2 r q)) as [HRrq | Hnrq].
          { apply (@n4_residual_antisym_contra B R2 HR2 q r Hqr_neq HRqr HRrq). }
          destruct (classic (R2 p s)) as [HRps | Hnps].
          { (* Edges {pq, pr, sq, sr, qr, ps}.  All 6 pairs comparable.
               Chain p<r<{q,s}... actually check: p→q ✓, p→r ✓, p→s ✓, q→r ✓, q→s? Hnqs.
               So q↔s comparison is HRsq (s→q): consistent.  All 6 pairs OK. *)
            assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
            assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
            assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
            assert (Hqr_cmp : R2 q r \/ R2 r q) by (left; exact HRqr).
            assert (Hqs_cmp : R2 q s \/ R2 s q) by (right; exact HRsq).
            assert (Hrs_cmp : R2 r s \/ R2 s r) by (right; exact HRsr).
            exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                     Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
          (* Edges {pq, pr, sq, sr, qr}.  Y_chain_down a=p, b=s, c=q, d=r. *)
          apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
          exists p, s, q, r.
          split; [exact Hps_neq |].
          split; [exact Hpq_neq |].
          split; [exact Hpr_neq |].
          split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
          split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
          split; [exact Hqr_neq |].
          split; [exact HRpq |].
          split; [exact HRsq |].
          split; [exact HRqr |].
          split; [exact HRpr |].
          split; [exact HRsr |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,q) *)
              | (right; left; split; reflexivity)                         (* (s,q) *)
              | (right; right; left; split; reflexivity)                  (* (q,r) *)
              | (right; right; right; left; split; reflexivity)           (* (p,r) *)
              | (right; right; right; right; split; reflexivity)          (* (s,r) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        destruct (classic (R2 r q)) as [HRrq | Hnrq].
        { destruct (classic (R2 p s)) as [HRps | Hnps].
          { (* Edges {pq, pr, sq, sr, rq, ps}.  All 6 pairs comparable.  Chain contra. *)
            assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
            assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
            assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
            assert (Hqr_cmp : R2 q r \/ R2 r q) by (right; exact HRrq).
            assert (Hqs_cmp : R2 q s \/ R2 s q) by (right; exact HRsq).
            assert (Hrs_cmp : R2 r s \/ R2 s r) by (right; exact HRsr).
            exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                     Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
          (* Edges {pq, pr, sq, sr, rq}.  Y_chain_down a=p, b=s, c=r, d=q. *)
          apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
          exists p, s, r, q.
          split; [exact Hps_neq |].
          split; [exact Hpr_neq |].
          split; [exact Hpq_neq |].
          split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
          split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
          split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
          split; [exact HRpr |].
          split; [exact HRsr |].
          split; [exact HRrq |].
          split; [exact HRpq |].
          split; [exact HRsq |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,r) *)
              | (right; left; split; reflexivity)                         (* (s,r) *)
              | (right; right; left; split; reflexivity)                  (* (r,q) *)
              | (right; right; right; left; split; reflexivity)           (* (p,q) *)
              | (right; right; right; right; split; reflexivity)          (* (s,q) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        destruct (classic (R2 p s)) as [HRps | Hnps].
        { (* Edges {pq, pr, sq, sr, ps}.  Y_chain_up a=p, b=s, c=q, d=r. *)
          apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
          exists p, s, q, r.
          split; [exact Hps_neq |].
          split; [exact Hpq_neq |].
          split; [exact Hpr_neq |].
          split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
          split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
          split; [exact Hqr_neq |].
          split; [exact HRps |].
          split; [exact HRpq |].
          split; [exact HRpr |].
          split; [exact HRsq |].
          split; [exact HRsr |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,s) *)
              | (right; left; split; reflexivity)                         (* (p,q) *)
              | (right; right; left; split; reflexivity)                  (* (p,r) *)
              | (right; right; right; left; split; reflexivity)           (* (s,q) *)
              | (right; right; right; right; split; reflexivity)          (* (s,r) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        (* Edges {pq, pr, sq, sr}.  Bowtie a=p, b=s, c=q, d=r. *)
        apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
        exists p, s, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRsq |].
        split; [exact HRsr |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,q) *)
            | (right; left; split; reflexivity)                   (* (p,r) *)
            | (right; right; left; split; reflexivity)            (* (s,q) *)
            | (right; right; right; split; reflexivity)           (* (s,r) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Hnsr branch.  Hnsp, Hnqs, Hnrs, Hnsr in scope. *)
      destruct (classic (R2 q r)) as [HRqr | Hnqr].
      { (* HRsq + HRqr ⇒ HRsr by trans, contradicting Hnsr. *)
        apply (@n4_residual_trans_contra B R2 HR2 s q r HRsq HRqr Hnsr). }
      destruct (classic (R2 r q)) as [HRrq | Hnrq].
      { destruct (classic (R2 p s)) as [HRps | Hnps].
        { (* Edges {pq, pr, sq, rq, ps}.  Diamond a=p, b=r, c=s, d=q. *)
          apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
          exists p, r, s, q.
          split; [exact Hpr_neq |].
          split; [exact Hps_neq |].
          split; [exact Hpq_neq |].
          split; [exact Hrs_neq |].
          split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
          split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
          split; [exact HRpr |].
          split; [exact HRps |].
          split; [exact HRpq |].
          split; [exact HRrq |].
          split; [exact HRsq |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,r) *)
              | (right; left; split; reflexivity)                         (* (p,s) *)
              | (right; right; left; split; reflexivity)                  (* (p,q) *)
              | (right; right; right; left; split; reflexivity)           (* (r,q) *)
              | (right; right; right; right; split; reflexivity)          (* (s,q) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        (* Edges {pq, pr, sq, rq}.  chain3+above a=p, b=r, c=q, d=s. *)
        apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
        exists p, r, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRpr |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRsq |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,r) *)
            | (right; left; split; reflexivity)                   (* (p,q) *)
            | (right; right; left; split; reflexivity)            (* (r,q) *)
            | (right; right; right; split; reflexivity)           (* (s,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 p s)) as [HRps | Hnps].
      { (* Edges {pq, pr, sq, ps}.  chain3+below a=p, b=s, c=q, d=r. *)
        apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
        exists p, s, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRps |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRpr |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,s) *)
            | (right; left; split; reflexivity)                   (* (p,q) *)
            | (right; right; left; split; reflexivity)            (* (s,q) *)
            | (right; right; right; split; reflexivity)           (* (p,r) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* All extras absent.  Edges exactly {pq, pr, sq} = F2b N-pattern. *)
      exfalso. apply HnF2b.
      split; [exact HRsq |].
      split; [exact HRpr |].
      intros x y Hxy_neq HRxy.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hxy_neq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (s,q) *)
          | (right; left; split; reflexivity)                   (* (p,q) *)
          | (right; right; split; reflexivity)                  (* (p,r) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnsq branch: HRpq, HRpr in scope, Hnrp, Hnsq.
       Undecided: R2 p s, R2 s p, R2 q r, R2 r q, R2 q s, R2 r s, R2 s r.
       Key forced fact: HRsp + HRpq ⇒ HRsq, but Hnsq, so HRsp forbidden. *)
    destruct (classic (R2 s p)) as [HRsp | Hnsp].
    { apply (@n4_residual_trans_contra B R2 HR2 s p q HRsp HRpq Hnsq). }
    destruct (classic (R2 r s)) as [HRrs | Hnrs].
    { (* HRrs branch: HRpr + HRrs ⇒ HRps (forced). *)
      assert (HRps : R2 p s) by exact (poset_trans p r s HRpr HRrs).
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { apply (@n4_residual_antisym_contra B R2 HR2 r s Hrs_neq HRrs HRsr). }
      destruct (classic (R2 q r)) as [HRqr | Hnqr].
      { (* HRqr + HRrs ⇒ HRqs forced.  All 6 pairs comparable.  Chain contra. *)
        assert (HRqs : R2 q s) by exact (poset_trans q r s HRqr HRrs).
        assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
        assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
        assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
        assert (Hqr_cmp : R2 q r \/ R2 r q) by (left; exact HRqr).
        assert (Hqs_cmp : R2 q s \/ R2 s q) by (left; exact HRqs).
        assert (Hrs_cmp : R2 r s \/ R2 s r) by (left; exact HRrs).
        exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                 Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
      destruct (classic (R2 r q)) as [HRrq | Hnrq].
      { destruct (classic (R2 q s)) as [HRqs | Hnqs].
        { (* All 6 pairs comparable.  Chain contra. *)
          assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
          assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
          assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
          assert (Hqr_cmp : R2 q r \/ R2 r q) by (right; exact HRrq).
          assert (Hqs_cmp : R2 q s \/ R2 s q) by (left; exact HRqs).
          assert (Hrs_cmp : R2 r s \/ R2 s r) by (left; exact HRrs).
          exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                   Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
        (* Edges {pq, pr, ps, rq, rs}.  Y_chain_up a=p, b=r, c=q, d=s. *)
        apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
        exists p, r, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRpr |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRrq |].
        split; [exact HRrs |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                                (* (p,r) *)
            | (right; left; split; reflexivity)                         (* (p,q) *)
            | (right; right; left; split; reflexivity)                  (* (p,s) *)
            | (right; right; right; left; split; reflexivity)           (* (r,q) *)
            | (right; right; right; right; split; reflexivity)          (* (r,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { (* Edges {pq, pr, ps, rs, qs}.  Diamond a=p, b=q, c=r, d=s. *)
        apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRps |].
        split; [exact HRqs |].
        split; [exact HRrs |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                                (* (p,q) *)
            | (right; left; split; reflexivity)                         (* (p,r) *)
            | (right; right; left; split; reflexivity)                  (* (p,s) *)
            | (right; right; right; left; split; reflexivity)           (* (q,s) *)
            | (right; right; right; right; split; reflexivity)          (* (r,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Edges {pq, pr, ps, rs}.  chain3+below a=p, b=r, c=s, d=q. *)
      apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
      exists p, r, s, q.
      split; [exact Hpr_neq |].
      split; [exact Hps_neq |].
      split; [exact Hpq_neq |].
      split; [exact Hrs_neq |].
      split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
      split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
      split; [exact HRpr |].
      split; [exact HRps |].
      split; [exact HRrs |].
      split; [exact HRpq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,r) *)
          | (right; left; split; reflexivity)                   (* (p,s) *)
          | (right; right; left; split; reflexivity)            (* (r,s) *)
          | (right; right; right; split; reflexivity)           (* (p,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnrs branch *)
    destruct (classic (R2 s r)) as [HRsr | Hnsr].
    { destruct (classic (R2 r q)) as [HRrq | Hnrq].
      { apply (@n4_residual_trans_contra B R2 HR2 s r q HRsr HRrq Hnsq). }
      destruct (classic (R2 q r)) as [HRqr | Hnqr].
      { destruct (classic (R2 p s)) as [HRps | Hnps].
        { destruct (classic (R2 q s)) as [HRqs | Hnqs].
          { (* All 6 pairs comparable.  Chain contra. *)
            assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
            assert (Hpr_cmp : R2 p r \/ R2 r p) by (left; exact HRpr).
            assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
            assert (Hqr_cmp : R2 q r \/ R2 r q) by (left; exact HRqr).
            assert (Hqs_cmp : R2 q s \/ R2 s q) by (left; exact HRqs).
            assert (Hrs_cmp : R2 r s \/ R2 s r) by (right; exact HRsr).
            exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                     Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
          (* Edges {pq, pr, sr, qr, ps}.  Diamond a=p, b=q, c=s, d=r. *)
          apply (@n4_diamond_two_realizer B R2 HR2 Hcard).
          exists p, q, s, r.
          split; [exact Hpq_neq |].
          split; [exact Hps_neq |].
          split; [exact Hpr_neq |].
          split; [exact Hqs_neq |].
          split; [exact Hqr_neq |].
          split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
          split; [exact HRpq |].
          split; [exact HRps |].
          split; [exact HRpr |].
          split; [exact HRqr |].
          split; [exact HRsr |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,q) *)
              | (right; left; split; reflexivity)                         (* (p,s) *)
              | (right; right; left; split; reflexivity)                  (* (p,r) *)
              | (right; right; right; left; split; reflexivity)           (* (q,r) *)
              | (right; right; right; right; split; reflexivity)          (* (s,r) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        destruct (classic (R2 q s)) as [HRqs | Hnqs].
        { apply (@n4_residual_trans_contra B R2 HR2 p q s HRpq HRqs Hnps). }
        (* Edges {pq, pr, sr, qr}.  chain3+above a=p, b=q, c=r, d=s. *)
        apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRqr |].
        split; [exact HRsr |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,q) *)
            | (right; left; split; reflexivity)                   (* (p,r) *)
            | (right; right; left; split; reflexivity)            (* (q,r) *)
            | (right; right; right; split; reflexivity)           (* (s,r) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Hnqr.  Edges {pq, pr, sr}. *)
      destruct (classic (R2 p s)) as [HRps | Hnps].
      { destruct (classic (R2 q s)) as [HRqs | Hnqs].
        { apply (@n4_residual_trans_contra B R2 HR2 q s r HRqs HRsr Hnqr). }
        (* Edges {pq, pr, sr, ps}.  chain3+below a=p, b=s, c=r, d=q. *)
        apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
        exists p, s, r, q.
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRps |].
        split; [exact HRpr |].
        split; [exact HRsr |].
        split; [exact HRpq |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,s) *)
            | (right; left; split; reflexivity)                   (* (p,r) *)
            | (right; right; left; split; reflexivity)            (* (s,r) *)
            | (right; right; right; split; reflexivity)           (* (p,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { apply (@n4_residual_trans_contra B R2 HR2 p q s HRpq HRqs Hnps). }
      (* Edges {pq, pr, sr}.  N-pattern a=s, b=r, c=p, d=q. *)
      apply (@n4_N_two_realizer B R2 HR2 Hcard).
      exists s, r, p, q.
      split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
      split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
      split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
      split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
      split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
      split; [exact Hpq_neq |].
      split; [exact HRsr |].
      split; [exact HRpr |].
      split; [exact HRpq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (s,r) *)
          | (right; left; split; reflexivity)                   (* (p,r) *)
          | (right; right; split; reflexivity)                  (* (p,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnsr branch.  Hnrs, Hnsr in scope. *)
    destruct (classic (R2 q r)) as [HRqr | Hnqr].
    { destruct (classic (R2 r q)) as [HRrq | Hnrq].
      { apply (@n4_residual_antisym_contra B R2 HR2 q r Hqr_neq HRqr HRrq). }
      destruct (classic (R2 p s)) as [HRps | Hnps].
      { destruct (classic (R2 q s)) as [HRqs | Hnqs].
        { (* Edges {pq, pr, qr, ps, qs}.  Y_chain_up a=p, b=q, c=r, d=s. *)
          apply (@n4_Y_chain_up_two_realizer B R2 HR2 Hcard).
          exists p, q, r, s.
          split; [exact Hpq_neq |].
          split; [exact Hpr_neq |].
          split; [exact Hps_neq |].
          split; [exact Hqr_neq |].
          split; [exact Hqs_neq |].
          split; [exact Hrs_neq |].
          split; [exact HRpq |].
          split; [exact HRpr |].
          split; [exact HRps |].
          split; [exact HRqr |].
          split; [exact HRqs |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,q) *)
              | (right; left; split; reflexivity)                         (* (p,r) *)
              | (right; right; left; split; reflexivity)                  (* (p,s) *)
              | (right; right; right; left; split; reflexivity)           (* (q,r) *)
              | (right; right; right; right; split; reflexivity)          (* (q,s) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        (* Edges {pq, pr, qr, ps}.  chain3+below a=p, b=q, c=r, d=s. *)
        apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRqr |].
        split; [exact HRps |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,q) *)
            | (right; left; split; reflexivity)                   (* (p,r) *)
            | (right; right; left; split; reflexivity)            (* (q,r) *)
            | (right; right; right; split; reflexivity)           (* (p,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { apply (@n4_residual_trans_contra B R2 HR2 p q s HRpq HRqs Hnps). }
      (* Edges {pq, pr, qr}.  chain_plus_isolated a=p, b=q, c=r, d=s. *)
      apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
      exists p, q, r, s.
      split; [exact Hpq_neq |].
      split; [exact Hpr_neq |].
      split; [exact Hps_neq |].
      split; [exact Hqr_neq |].
      split; [exact Hqs_neq |].
      split; [exact Hrs_neq |].
      split; [exact HRpq |].
      split; [exact HRqr |].
      split; [exact HRpr |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,q) *)
          | (right; left; split; reflexivity)                   (* (q,r) *)
          | (right; right; split; reflexivity)                  (* (p,r) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 r q)) as [HRrq | Hnrq].
    { destruct (classic (R2 p s)) as [HRps | Hnps].
      { destruct (classic (R2 q s)) as [HRqs | Hnqs].
        { apply (@n4_residual_trans_contra B R2 HR2 r q s HRrq HRqs Hnrs). }
        (* Edges {pq, pr, rq, ps}.  chain3+below a=p, b=r, c=q, d=s. *)
        apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
        exists p, r, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRpr |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRps |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,r) *)
            | (right; left; split; reflexivity)                   (* (p,q) *)
            | (right; right; left; split; reflexivity)            (* (r,q) *)
            | (right; right; right; split; reflexivity)           (* (p,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { apply (@n4_residual_trans_contra B R2 HR2 p q s HRpq HRqs Hnps). }
      (* Edges {pq, pr, rq}.  chain_plus_isolated a=p, b=r, c=q, d=s. *)
      apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
      exists p, r, q, s.
      split; [exact Hpr_neq |].
      split; [exact Hpq_neq |].
      split; [exact Hps_neq |].
      split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
      split; [exact Hrs_neq |].
      split; [exact Hqs_neq |].
      split; [exact HRpr |].
      split; [exact HRrq |].
      split; [exact HRpq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,r) *)
          | (right; left; split; reflexivity)                   (* (r,q) *)
          | (right; right; split; reflexivity)                  (* (p,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 p s)) as [HRps | Hnps].
    { destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { (* Edges {pq, pr, ps, qs}.  chain3+below a=p, b=q, c=s, d=r. *)
        apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRqs |].
        split; [exact HRpr |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,q) *)
            | (right; left; split; reflexivity)                   (* (p,s) *)
            | (right; right; left; split; reflexivity)            (* (q,s) *)
            | (right; right; right; split; reflexivity)           (* (p,r) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Edges {pq, pr, ps}.  3-claw-up a=p, b=q, c=r, d=s. *)
      apply (@n4_3claw_up_two_realizer B R2 HR2 Hcard).
      exists p, q, r, s.
      split; [exact Hpq_neq |].
      split; [exact Hpr_neq |].
      split; [exact Hps_neq |].
      split; [exact Hqr_neq |].
      split; [exact Hqs_neq |].
      split; [exact Hrs_neq |].
      split; [exact HRpq |].
      split; [exact HRpr |].
      split; [exact HRps |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,q) *)
          | (right; left; split; reflexivity)                   (* (p,r) *)
          | (right; right; split; reflexivity)                  (* (p,s) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 q s)) as [HRqs | Hnqs].
    { apply (@n4_residual_trans_contra B R2 HR2 p q s HRpq HRqs Hnps). }
    (* Edges {pq, pr}.  V at p with a=p, b=q, c=r, d=s. *)
    apply (@n4_V_two_realizer B R2 HR2 Hcard).
    exists p, q, r, s.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRpr |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
    destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
      subst x; subst y;
      try (exfalso; apply Hneq; reflexivity);
      first
        [ (left; split; reflexivity)                          (* (p,q) *)
        | (right; split; reflexivity)                         (* (p,r) *)
        | (exfalso;
           match goal with
           | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
           end)
        | (exfalso; apply Hpq_neq; apply poset_antisym;
           [exact HRpq | exact HRxy]) ]. }
  destruct (classic (R2 r p)) as [HRrp | Hnrp].
  { (* Sub-cascade: if r→p with all others absent, derive contradiction
       via [r → p → q] forcing R2 r q. *)
    destruct (classic (R2 p s)) as [HRps | Hnps].
    { (* Inside HRrp + HRps: case-split on q→r or s→r extras for
         transitivity contradictions against Hnpr. *)
      destruct (classic (R2 q r)) as [HRqr | Hnqr].
      { (* p→q + q→r ⇒ p→r, contradicting Hnpr. *)
        apply (@n4_residual_one_extra_qr_contra B R2 HR2 p q r HRpq HRqr Hnpr). }
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { (* p→s + s→r ⇒ p→r, contradicting Hnpr. *)
        apply (@n4_residual_trans_contra B R2 HR2 p s r HRps HRsr Hnpr). }
      destruct (classic (R2 s p)) as [HRsp | Hnsp].
      { (* p→s and s→p ⇒ p = s by antisymmetry, contradicting Hps_neq. *)
        apply (@n4_residual_antisym_contra B R2 HR2 p s Hps_neq HRps HRsp). }
      (* Forced via trans: HRrq (rp+pq), HRrs (rp+ps).  Total 5 edges
         {r→p, p→q, p→s, r→q, r→s} = M3a pattern.  Split on HRqs/HRsq
         extras; the "neither" case derives False from HnM3a. *)
      assert (HRrq : R2 r q) by exact (poset_trans r p q HRrp HRpq).
      assert (HRrs : R2 r s) by exact (poset_trans r p s HRrp HRps).
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { (* HRqs: 4-chain r<p<q<s. Hinc_ex contradiction. *)
        assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
        assert (Hpr_cmp : R2 p r \/ R2 r p) by (right; exact HRrp).
        assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
        assert (Hqr_cmp : R2 q r \/ R2 r q) by (right; exact HRrq).
        assert (Hqs_cmp : R2 q s \/ R2 s q) by (left; exact HRqs).
        assert (Hrs_cmp : R2 r s \/ R2 s r) by (left; exact HRrs).
        exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                 Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
      destruct (classic (R2 s q)) as [HRsq | Hnsq].
      { (* HRsq: 4-chain r<p<s<q. Hinc_ex contradiction. *)
        assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
        assert (Hpr_cmp : R2 p r \/ R2 r p) by (right; exact HRrp).
        assert (Hps_cmp : R2 p s \/ R2 s p) by (left; exact HRps).
        assert (Hqr_cmp : R2 q r \/ R2 r q) by (right; exact HRrq).
        assert (Hqs_cmp : R2 q s \/ R2 s q) by (right; exact HRsq).
        assert (Hrs_cmp : R2 r s \/ R2 s r) by (left; exact HRrs).
        exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                 Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
      (* Both Hnqs and Hnsq.  Edges exactly the 5 M3a edges.  Derive
         False from HnM3a via Hcov4 enumeration. *)
      exfalso. apply HnM3a.
      split; [exact HRrp |].
      split; [exact HRrq |].
      split; [exact HRrs |].
      split; [exact HRps |].
      intros x y Hxy_neq HRxy.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hxy_neq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (r,p) *)
          | (right; left; split; reflexivity)                   (* (r,q) *)
          | (right; right; left; split; reflexivity)            (* (r,s) *)
          | (right; right; right; left; split; reflexivity)     (* (p,q) *)
          | (right; right; right; right; split; reflexivity)    (* (p,s) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 s p)) as [HRsp | Hnsp].
    { (* Inside HRrp + HRsp: case-split on q→r or q→s extras. *)
      destruct (classic (R2 q r)) as [HRqr | Hnqr].
      { (* p→q + q→r ⇒ p→r, contradicting Hnpr. *)
        apply (@n4_residual_one_extra_qr_contra B R2 HR2 p q r HRpq HRqr Hnpr). }
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { (* p→q + q→s ⇒ p→s, but s→p ⇒ p=s by antisym, contradicting Hps_neq. *)
        apply (@n4_residual_antisym_contra B R2 HR2 p s Hps_neq
                 (poset_trans p q s HRpq HRqs) HRsp). }
      (* All edges with q,p,r,p,s,p covered.  Forced: HRrq (rp+pq) and
         HRsq (sp+pq).  Now split on remaining HRrs and HRsr.  Both
         positive cases extend the relation to a 4-chain, contradicting
         Hinc_ex. *)
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* 4-chain r<s<p<q via HRrs + HRsp + HRpq.  Plus HRrp, HRrq,
           HRsq forced.  All 6 pairs comparable; contradicts Hinc_ex. *)
        assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
        assert (Hpr_cmp : R2 p r \/ R2 r p) by (right; exact HRrp).
        assert (Hps_cmp : R2 p s \/ R2 s p) by (right; exact HRsp).
        assert (Hqr_cmp : R2 q r \/ R2 r q)
          by (right; exact (poset_trans r p q HRrp HRpq)).
        assert (Hqs_cmp : R2 q s \/ R2 s q)
          by (right; exact (poset_trans s p q HRsp HRpq)).
        assert (Hrs_cmp : R2 r s \/ R2 s r) by (left; exact HRrs).
        exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                 Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { (* 4-chain s<r<p<q via HRsr + HRrp + HRpq. *)
        assert (Hpq_cmp : R2 p q \/ R2 q p) by (left; exact HRpq).
        assert (Hpr_cmp : R2 p r \/ R2 r p) by (right; exact HRrp).
        assert (Hps_cmp : R2 p s \/ R2 s p) by (right; exact HRsp).
        assert (Hqr_cmp : R2 q r \/ R2 r q)
          by (right; exact (poset_trans r p q HRrp HRpq)).
        assert (Hqs_cmp : R2 q s \/ R2 s q)
          by (right; exact (poset_trans s p q HRsp HRpq)).
        assert (Hrs_cmp : R2 r s \/ R2 s r) by (right; exact HRsr).
        exact (@n4_chain_contra_inc B R2 HR2 p q r s Hcov4 Hinc_ex
                 Hpq_cmp Hpr_cmp Hps_cmp Hqr_cmp Hqs_cmp Hrs_cmp _). }
      (* Hnrs and Hnsr both hold.  Edges are exactly the 5 N2a
         edges: {r→p, s→p, p→q, r→q, s→q}.  Derive False from HnN2a
         (in scope from line ~6284) via Hcov4 enumeration. *)
      assert (HRrq : R2 r q) by exact (poset_trans r p q HRrp HRpq).
      assert (HRsq : R2 s q) by exact (poset_trans s p q HRsp HRpq).
      exfalso. apply HnN2a.
      split; [exact HRrp |].
      split; [exact HRsp |].
      split; [exact HRrq |].
      split; [exact HRsq |].
      intros x y Hxy_neq HRxy.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hxy_neq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (r,p) *)
          | (right; left; split; reflexivity)                   (* (s,p) *)
          | (right; right; left; split; reflexivity)            (* (p,q) *)
          | (right; right; right; left; split; reflexivity)     (* (r,q) *)
          | (right; right; right; right; split; reflexivity)    (* (s,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 q r)) as [HRqr | Hnqr].
    { (* HRrp + HRpq ⇒ HRrq (trans); combined with HRqr, antisymmetry
         forces q = r, contradicting Hqr_neq. *)
      apply (@n4_residual_one_extra_rp_qr_contra B R2 HR2 p q r
               Hqr_neq HRpq HRrp HRqr). }
    destruct (classic (R2 r q)) as [HRrq | Hnrq].
    { (* Inside HRrp + HRrq: case-split on s-related extras to
         discharge contradictions. *)
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { (* p→q + q→s ⇒ p→s, contradicting Hnps. *)
        apply (@n4_residual_one_extra_qs_contra B R2 HR2 p q s HRpq HRqs Hnps). }
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { (* s→r + r→p ⇒ s→p, contradicting Hnsp. *)
        apply (@n4_residual_one_extra_sr_rp_contra B R2 HR2 p r s
                 HRsr HRrp Hnsp). }
      (* Inside HRrp + HRrq + Hnqs + Hnsr: split on remaining extras
         R2 r s and R2 s q.  Both sub-cases (with the other negated)
         match K3a or L3a; the combined HRrs + HRsq matches D4. *)
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { destruct (classic (R2 s q)) as [HRsq | Hnsq].
        { (* HRrs + HRsq: edges {r→p, p→q, r→q, r→s, s→q} = D4 diamond
             pattern.  Derive False from HnD4. *)
          exfalso. apply HnD4.
          split; [exact HRrp |].
          split; [exact HRrs |].
          split; [exact HRrq |].
          split; [exact HRsq |].
          intros x y Hxy_neq HRxy.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hxy_neq; reflexivity);
            first
              [ (left; split; reflexivity)                          (* (r,p) *)
              | (right; left; split; reflexivity)                   (* (r,s) *)
              | (right; right; left; split; reflexivity)            (* (r,q) *)
              | (right; right; right; left; split; reflexivity)     (* (p,q) *)
              | (right; right; right; right; split; reflexivity)    (* (s,q) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        (* Hnsq: edges exactly {r→p, p→q, r→q, r→s} = K3a pattern. *)
        exfalso. apply HnK3a.
        split; [exact HRrp |].
        split; [exact HRrq |].
        split; [exact HRrs |].
        intros x y Hxy_neq HRxy.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hxy_neq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (r,p) *)
            | (right; left; split; reflexivity)                   (* (r,q) *)
            | (right; right; left; split; reflexivity)            (* (p,q) *)
            | (right; right; right; split; reflexivity)           (* (r,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 s q)) as [HRsq | Hnsq].
      { (* Hnrs + HRsq: edges exactly {r→p, p→q, r→q, s→q} = L3a
           pattern.  Derive False from HnL3a. *)
        exfalso. apply HnL3a.
        split; [exact HRrp |].
        split; [exact HRrq |].
        split; [exact HRsq |].
        intros x y Hxy_neq HRxy.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hxy_neq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (r,p) *)
            | (right; left; split; reflexivity)                   (* (r,q) *)
            | (right; right; left; split; reflexivity)            (* (p,q) *)
            | (right; right; right; split; reflexivity)           (* (s,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* All s-edges are negated; only edges are {(r,p), (p,q), (r,q)}.
         This is class (b) chain r<p<q + isolated s, which the residual
         classifier's B2a test (line 6287, [HnB2a] in scope here)
         should have matched.  Derive False from HnB2a. *)
      exfalso. apply HnB2a.
      split; [exact HRrp |].
      split; [exact HRrq |].
      intros x y Hxy_neq HRxy.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hxy_neq; reflexivity);
        first
          [ (right; right; split; reflexivity)  (* (r, q) *)
          | (right; left; split; reflexivity)   (* (p, q) *)
          | (left; split; reflexivity)          (* (r, p) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnrq is in context.  r→p + p→q ⇒ r→q, contradicting Hnrq. *)
    apply (@n4_residual_one_extra_rp_contra B R2 HR2 p q r HRpq HRrp Hnrq). }
  destruct (classic (R2 p s)) as [HRps | Hnps].
  { (* Inside HRps: case-split on s→p (antisym contradiction) and on
       extras whose trans-closure contradicts Hnpr. *)
    destruct (classic (R2 s p)) as [HRsp | Hnsp].
    { (* p→s and s→p ⇒ p = s by antisymmetry, contradicting Hps_neq. *)
      apply (@n4_residual_antisym_contra B R2 HR2 p s Hps_neq HRps HRsp). }
    destruct (classic (R2 q r)) as [HRqr | Hnqr].
    { (* p→q + q→r ⇒ p→r, contradicting Hnpr. *)
      apply (@n4_residual_one_extra_qr_contra B R2 HR2 p q r HRpq HRqr Hnpr). }
    destruct (classic (R2 s r)) as [HRsr | Hnsr].
    { (* p→s + s→r ⇒ p→r, contradicting Hnpr. *)
      apply (@n4_residual_trans_contra B R2 HR2 p s r HRps HRsr Hnpr). }
    (* Context: HRpq, HRps, Hnpr, Hnrp, Hnsp, Hnqr, Hnsr.
       Undecided: R2 r q, R2 q s, R2 s q, R2 r s.  Dispatch the 16
       sub-cases by cascading classical splits, applying one of the
       per-class lemmas, antisym/trans contras, etc. *)
    destruct (classic (R2 r q)) as [HRrq | Hnrq].
    { destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { destruct (classic (R2 s q)) as [HRsq | Hnsq].
        { (* antisym q=s *)
          apply (@n4_residual_antisym_contra B R2 HR2 q s Hqs_neq HRqs HRsq). }
        destruct (classic (R2 r s)) as [HRrs | Hnrs].
        { (* Case 13: edges {p→q, p→s, r→q, q→s, r→s}.
             Y_chain_down with a=p, b=r, c=q, d=s. *)
          apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
          exists p, r, q, s.
          split; [exact Hpr_neq |].
          split; [exact Hpq_neq |].
          split; [exact Hps_neq |].
          split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
          split; [exact Hrs_neq |].
          split; [exact Hqs_neq |].
          split; [exact HRpq |].
          split; [exact HRrq |].
          split; [exact HRqs |].
          split; [exact HRps |].
          split; [exact HRrs |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,q) *)
              | (right; left; split; reflexivity)                         (* (r,q) *)
              | (right; right; left; split; reflexivity)                  (* (q,s) *)
              | (right; right; right; left; split; reflexivity)           (* (p,s) *)
              | (right; right; right; right; split; reflexivity)          (* (r,s) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        (* Case 12: HRrq + HRqs + Hnrs.  r→q + q→s ⇒ r→s by trans, contra Hnrs. *)
        apply (@n4_residual_trans_contra B R2 HR2 r q s HRrq HRqs Hnrs). }
      (* Hnqs branch *)
      destruct (classic (R2 s q)) as [HRsq | Hnsq].
      { destruct (classic (R2 r s)) as [HRrs | Hnrs].
        { (* Case 11: edges {p→q, p→s, r→q, s→q, r→s}.
             Y_chain_down with a=p, b=r, c=s, d=q. *)
          apply (@n4_Y_chain_down_two_realizer B R2 HR2 Hcard).
          exists p, r, s, q.
          split; [exact Hpr_neq |].
          split; [exact Hps_neq |].
          split; [exact Hpq_neq |].
          split; [exact Hrs_neq |].
          split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
          split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
          split; [exact HRps |].
          split; [exact HRrs |].
          split; [exact HRsq |].
          split; [exact HRpq |].
          split; [exact HRrq |].
          intros x y HRxy.
          destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
          right.
          destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
          destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
            subst x; subst y;
            try (exfalso; apply Hneq; reflexivity);
            first
              [ (left; split; reflexivity)                                (* (p,s) *)
              | (right; left; split; reflexivity)                         (* (r,s) *)
              | (right; right; left; split; reflexivity)                  (* (s,q) *)
              | (right; right; right; left; split; reflexivity)           (* (p,q) *)
              | (right; right; right; right; split; reflexivity)          (* (r,q) *)
              | (exfalso;
                 match goal with
                 | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
                 end)
              | (exfalso; apply Hpq_neq; apply poset_antisym;
                 [exact HRpq | exact HRxy]) ]. }
        (* Case 10: edges {p→q, p→s, r→q, s→q}.
           chain3+above with a=p, b=s, c=q, d=r. *)
        apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
        exists p, s, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRps |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrq |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,s) *)
            | (right; left; split; reflexivity)                   (* (p,q) *)
            | (right; right; left; split; reflexivity)            (* (s,q) *)
            | (right; right; right; split; reflexivity)           (* (r,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Hnsq branch under HRrq + Hnqs. *)
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* Case 9: edges {p→q, p→s, r→q, r→s}.
           Bowtie with a=p, b=r, c=q, d=s. *)
        apply (@n4_bowtie_two_realizer B R2 HR2 Hcard).
        exists p, r, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRrq |].
        split; [exact HRrs |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,q) *)
            | (right; left; split; reflexivity)                   (* (p,s) *)
            | (right; right; left; split; reflexivity)            (* (r,q) *)
            | (right; right; right; split; reflexivity)           (* (r,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Case 8: edges {p→q, p→s, r→q}.  N-pattern with a=r, b=q, c=p, d=s. *)
      apply (@n4_N_two_realizer B R2 HR2 Hcard).
      exists r, q, p, s.
      split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
      split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
      split; [exact Hrs_neq |].
      split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
      split; [exact Hqs_neq |].
      split; [exact Hps_neq |].
      split; [exact HRrq |].
      split; [exact HRpq |].
      split; [exact HRps |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (r,q) *)
          | (right; left; split; reflexivity)                   (* (p,q) *)
          | (right; right; split; reflexivity)                  (* (p,s) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnrq branch *)
    destruct (classic (R2 q s)) as [HRqs | Hnqs].
    { destruct (classic (R2 s q)) as [HRsq | Hnsq].
      { (* antisym *)
        apply (@n4_residual_antisym_contra B R2 HR2 q s Hqs_neq HRqs HRsq). }
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* Case 6: edges {p→q, p→s, q→s, r→s}.
           chain3+above with a=p, b=q, c=s, d=r. *)
        apply (@n4_chain3_plus_above_two_realizer B R2 HR2 Hcard).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRqs |].
        split; [exact HRrs |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (p,q) *)
            | (right; left; split; reflexivity)                   (* (p,s) *)
            | (right; right; left; split; reflexivity)            (* (q,s) *)
            | (right; right; right; split; reflexivity)           (* (r,s) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Case 5: edges {p→q, p→s, q→s}.
         chain_plus_isolated with a=p, b=q, c=s, d=r. *)
      apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
      exists p, q, s, r.
      split; [exact Hpq_neq |].
      split; [exact Hps_neq |].
      split; [exact Hpr_neq |].
      split; [exact Hqs_neq |].
      split; [exact Hqr_neq |].
      split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
      split; [exact HRpq |].
      split; [exact HRqs |].
      split; [exact HRps |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,q) *)
          | (right; left; split; reflexivity)                   (* (p,s) *)
          | (right; right; split; reflexivity)                  (* (q,s) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnqs branch under Hnrq. *)
    destruct (classic (R2 s q)) as [HRsq | Hnsq].
    { destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* Case 4: HRrs + HRsq ⇒ HRrq, but Hnrq.  Trans contra. *)
        apply (@n4_residual_trans_contra B R2 HR2 r s q HRrs HRsq Hnrq). }
      (* Case 3: edges {p→q, p→s, s→q}.
         chain_plus_isolated with a=p, b=s, c=q, d=r. *)
      apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
      exists p, s, q, r.
      split; [exact Hps_neq |].
      split; [exact Hpq_neq |].
      split; [exact Hpr_neq |].
      split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
      split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
      split; [exact Hqr_neq |].
      split; [exact HRps |].
      split; [exact HRsq |].
      split; [exact HRpq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,s) *)
          | (right; left; split; reflexivity)                   (* (p,q) *)
          | (right; right; split; reflexivity)                  (* (s,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnsq branch under Hnrq + Hnqs. *)
    destruct (classic (R2 r s)) as [HRrs | Hnrs].
    { (* Case 2: edges {p→q, p→s, r→s}.  N-pattern with a=r, b=s, c=p, d=q. *)
      apply (@n4_N_two_realizer B R2 HR2 Hcard).
      exists r, s, p, q.
      split; [exact Hrs_neq |].
      split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
      split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
      split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
      split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
      split; [exact Hpq_neq |].
      split; [exact HRrs |].
      split; [exact HRps |].
      split; [exact HRpq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (r,s) *)
          | (right; left; split; reflexivity)                   (* (p,s) *)
          | (right; right; split; reflexivity)                  (* (p,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Case 1: edges {p→q, p→s} only.  V at p with a=p, b=q, c=s, d=r. *)
    apply (@n4_V_two_realizer B R2 HR2 Hcard).
    exists p, q, s, r.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRpq |].
    split; [exact HRps |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
    destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
      subst x; subst y;
      try (exfalso; apply Hneq; reflexivity);
      first
        [ (left; split; reflexivity)                          (* (p,q) *)
        | (right; split; reflexivity)                         (* (p,s) *)
        | (exfalso;
           match goal with
           | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
           end)
        | (exfalso; apply Hpq_neq; apply poset_antisym;
           [exact HRpq | exact HRxy]) ]. }
  destruct (classic (R2 s p)) as [HRsp | Hnsp].
  { (* s→p + p→q ⇒ s→q.  Sub-cascade until Hnsq. *)
    destruct (classic (R2 q r)) as [HRqr | Hnqr].
    { (* p→q + q→r ⇒ p→r, contradicting Hnpr already in context. *)
      apply (@n4_residual_one_extra_qr_contra B R2 HR2 p q r HRpq HRqr Hnpr). }
    destruct (classic (R2 r q)) as [HRrq | Hnrq].
    { (* Inside HRsp + HRrq: case-split on r-s extras to discharge
         contradictions. *)
      destruct (classic (R2 q s)) as [HRqs | Hnqs].
      { (* p→q + q→s ⇒ p→s, contradicting Hnps. *)
        apply (@n4_residual_one_extra_qs_contra B R2 HR2 p q s HRpq HRqs Hnps). }
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* r→s + s→p ⇒ r→p, contradicting Hnrp. *)
        apply (@n4_residual_one_extra_rs_qp_contra B R2 HR2 p r s
                 HRrs HRsp Hnrp). }
      (* Inside HRsp + HRrq + Hnqs + Hnrs: split on HRsr.  Forced via
         trans: HRsq (sp+pq). *)
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { (* HRsp + HRsr + HRrq + HRpq: 5 edges {s→r, s→p, s→q, r→q, p→q}
           = D7b diamond pattern.  Derive False from HnD7b. *)
        assert (HRsq : R2 s q) by exact (poset_trans s p q HRsp HRpq).
        exfalso. apply HnD7b.
        split; [exact HRsr |].
        split; [exact HRsp |].
        split; [exact HRsq |].
        split; [exact HRrq |].
        intros x y Hxy_neq HRxy.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hxy_neq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (s,r) *)
            | (right; left; split; reflexivity)                   (* (s,p) *)
            | (right; right; left; split; reflexivity)            (* (s,q) *)
            | (right; right; right; left; split; reflexivity)     (* (r,q) *)
            | (right; right; right; right; split; reflexivity)    (* (p,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Hnsr also holds.  Only edges are {(s,p), (s,q), (p,q), (r,q)}
         = L3b pattern.  Derive False from HnL3b (in scope from
         ~6000) via Hcov4 enumeration. *)
      assert (HRsq : R2 s q) by exact (poset_trans s p q HRsp HRpq).
      exfalso. apply HnL3b.
      split; [exact HRsp |].
      split; [exact HRsq |].
      split; [exact HRrq |].
      intros x y Hxy_neq HRxy.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hxy_neq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (s,p) *)
          | (right; left; split; reflexivity)                   (* (s,q) *)
          | (right; right; left; split; reflexivity)            (* (p,q) *)
          | (right; right; right; split; reflexivity)           (* (r,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 q s)) as [HRqs | Hnqs].
    { (* HRsp + HRpq ⇒ HRsq (trans); combined with HRqs, antisymmetry
         forces q = s, contradicting Hqs_neq. *)
      apply (@n4_residual_one_extra_sp_qs_contra B R2 HR2 p q s
               Hqs_neq HRpq HRsp HRqs). }
    destruct (classic (R2 s q)) as [HRsq | Hnsq].
    { (* Inside HRsp + HRsq: split on r→s extra (forces r→p via trans
         against Hnrp). *)
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { (* r→s + s→p ⇒ r→p, contradicting Hnrp. *)
        apply (@n4_residual_one_extra_rs_qp_contra B R2 HR2 p r s
                 HRrs HRsp Hnrp). }
      (* Context: HRpq, HRsp, HRsq, Hnpr, Hnrp, Hnps, Hnqr, Hnrq, Hnqs, Hnrs.
         Case-split on HRsr:
         - HRsr: edges {s→p, p→q, s→q, s→r} = class (i) chain3-plus-below
           with a=s, b=p, c=q, d=r (chain s<p<q plus s→r).
         - Hnsr: edges {s→p, p→q, s→q} = class (b) chain-plus-isolated
           with a=s, b=p, c=q, d=r. *)
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { apply (@n4_chain3_plus_below_two_realizer B R2 HR2 Hcard).
        exists s, p, q, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRsp |].
        split; [exact HRsq |].
        split; [exact HRpq |].
        split; [exact HRsr |].
        intros x y HRxy.
        destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
        right.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hneq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (s,p) *)
            | (right; left; split; reflexivity)                   (* (s,q) *)
            | (right; right; left; split; reflexivity)            (* (p,q) *)
            | (right; right; right; split; reflexivity)           (* (s,r) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Hnsr: edges {s→p, p→q, s→q} = chain-plus-isolated. *)
      apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
      exists s, p, q, r.
      split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
      split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
      split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
      split; [exact Hpq_neq |].
      split; [exact Hpr_neq |].
      split; [exact Hqr_neq |].
      split; [exact HRsp |].
      split; [exact HRpq |].
      split; [exact HRsq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (s,p) *)
          | (right; left; split; reflexivity)                   (* (p,q) *)
          | (right; right; split; reflexivity)                  (* (s,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    apply (@n4_residual_one_extra_sp_contra B R2 HR2 p q s HRpq HRsp Hnsq). }
  destruct (classic (R2 q r)) as [HRqr | Hnqr].
  { (* p→q + q→r ⇒ p→r, contradicting Hnpr already in context. *)
    apply (@n4_residual_one_extra_qr_contra B R2 HR2 p q r HRpq HRqr Hnpr). }
  destruct (classic (R2 r q)) as [HRrq | Hnrq].
  { (* Inside the top-level HRrq leaf: case-split on q-s extras. *)
    destruct (classic (R2 q s)) as [HRqs | Hnqs].
    { (* p→q + q→s ⇒ p→s, contradicting Hnps. *)
      apply (@n4_residual_one_extra_qs_contra B R2 HR2 p q s HRpq HRqs Hnps). }
    destruct (classic (R2 s q)) as [HRsq | Hnsq].
    { (* Context: HRpq, HRrq, HRsq, Hnpr, Hnrp, Hnps, Hnsp, Hnqr, Hnqs.
         Case-split on r↔s: 4 sub-cases.
         - HRrs ∩ HRsr: antisym contra.
         - HRrs ∩ Hnsr: edges {p→q, r→q, s→q, r→s} = L4a → HnL4a.
         - HRsr ∩ Hnrs: edges {p→q, r→q, s→q, s→r} = L4b → HnL4b.
         - Hnrs ∩ Hnsr: edges {p→q, r→q, s→q} = class (h) 3-claw-down. *)
      destruct (classic (R2 r s)) as [HRrs | Hnrs].
      { destruct (classic (R2 s r)) as [HRsr | Hnsr].
        { apply (@n4_residual_antisym_contra B R2 HR2 r s Hrs_neq HRrs HRsr). }
        (* HRrs ∩ Hnsr: L4a pattern. *)
        exfalso. apply HnL4a.
        split; [exact HRrs |].
        split; [exact HRrq |].
        split; [exact HRsq |].
        intros x y Hxy_neq HRxy.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hxy_neq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (r,s) *)
            | (right; left; split; reflexivity)                   (* (r,q) *)
            | (right; right; left; split; reflexivity)            (* (s,q) *)
            | (right; right; right; split; reflexivity)           (* (p,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { (* HRsr ∩ Hnrs: L4b pattern. *)
        exfalso. apply HnL4b.
        split; [exact HRsr |].
        split; [exact HRsq |].
        split; [exact HRrq |].
        intros x y Hxy_neq HRxy.
        destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
        destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
          subst x; subst y;
          try (exfalso; apply Hxy_neq; reflexivity);
          first
            [ (left; split; reflexivity)                          (* (s,r) *)
            | (right; left; split; reflexivity)                   (* (s,q) *)
            | (right; right; left; split; reflexivity)            (* (r,q) *)
            | (right; right; right; split; reflexivity)           (* (p,q) *)
            | (exfalso;
               match goal with
               | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
               end)
            | (exfalso; apply Hpq_neq; apply poset_antisym;
               [exact HRpq | exact HRxy]) ]. }
      (* Hnrs ∩ Hnsr: only edges {p→q, r→q, s→q} = 3-claw-down at q. *)
      apply (@n4_3claw_down_two_realizer B R2 HR2 Hcard).
      exists p, r, s, q.
      split; [exact Hpr_neq |].
      split; [exact Hps_neq |].
      split; [exact Hpq_neq |].
      split; [exact Hrs_neq |].
      split; [exact Hrq_neq |].
      split; [exact Hsq_neq |].
      split; [exact HRpq |].
      split; [exact HRrq |].
      split; [exact HRsq |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,q) *)
          | (right; left; split; reflexivity)                   (* (r,q) *)
          | (right; right; split; reflexivity)                  (* (s,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 r s)) as [HRrs | Hnrs].
    { (* Context: HRpq, HRrq, HRrs, Hnpr, Hnrp, Hnps, Hnsp, Hnqr, Hnqs, Hnsq.
         Case-split on HRsr:
         - HRsr: r↔s antisym contra (Hrs_neq).
         - Hnsr: edges {p→q, r→q, r→s} = class (f) N pattern with
           a=p, b=q, c=r, d=s. *)
      destruct (classic (R2 s r)) as [HRsr | Hnsr].
      { apply (@n4_residual_antisym_contra B R2 HR2 r s Hrs_neq HRrs HRsr). }
      apply (@n4_N_two_realizer B R2 HR2 Hcard).
      exists p, q, r, s.
      split; [exact Hpq_neq |].
      split; [exact Hpr_neq |].
      split; [exact Hps_neq |].
      split; [exact Hqr_neq |].
      split; [exact Hqs_neq |].
      split; [exact Hrs_neq |].
      split; [exact HRpq |].
      split; [exact HRrq |].
      split; [exact HRrs |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,q) *)
          | (right; left; split; reflexivity)                   (* (r,q) *)
          | (right; right; split; reflexivity)                  (* (r,s) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    destruct (classic (R2 s r)) as [HRsr | Hnsr].
    { (* Hnsq + Hnrs + HRsr: edges {p→q, r→q, s→r, s→q forced via
         s→r→q (HRrq)}.  This is L4b pattern.  Derive False from HnL4b
         (in scope from ~6052) via Hcov4 enumeration. *)
      assert (HRsq_forced : R2 s q) by exact (poset_trans s r q HRsr HRrq).
      exfalso. apply HnL4b.
      split; [exact HRsr |].
      split; [exact HRsq_forced |].
      split; [exact HRrq |].
      intros x y Hxy_neq HRxy.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hxy_neq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (s,r) *)
          | (right; left; split; reflexivity)                   (* (s,q) *)
          | (right; right; left; split; reflexivity)            (* (r,q) *)
          | (right; right; right; split; reflexivity)           (* (p,q) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnqs + Hnsq + Hnrs + Hnsr: only edges are {p→q, r→q}.  This is
       class (d) inv-V with shared top q (a=p, b=r, c=q, d=s). *)
    apply (@n4_inv_V_two_realizer B R2 HR2 Hcard).
    exists p, r, q, s.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hrq_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hqs_neq |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
    destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
      subst x; subst y;
      try (exfalso; apply Hneq; reflexivity);
      first
        [ (left; split; reflexivity)             (* (p, q) *)
        | (right; split; reflexivity)            (* (r, q) *)
        | (exfalso;
           match goal with
           | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
           end)
        | (exfalso; apply Hpq_neq; apply poset_antisym;
           [exact HRpq | exact HRxy]) ]. }
  destruct (classic (R2 q s)) as [HRqs | Hnqs].
  { (* p→q + q→s ⇒ p→s, contradicting Hnps. *)
    apply (@n4_residual_one_extra_qs_contra B R2 HR2 p q s HRpq HRqs Hnps). }
  destruct (classic (R2 s q)) as [HRsq | Hnsq].
  { (* Inside the top-level HRsq leaf: case-split on r-s extras. *)
    destruct (classic (R2 r s)) as [HRrs | Hnrs].
    { (* r→s + s→q ⇒ r→q, contradicting Hnrq. *)
      apply (@n4_residual_one_extra_qs_contra B R2 HR2 r s q HRrs HRsq Hnrq). }
    (* Context: HRpq, HRsq, Hnpr, Hnrp, Hnps, Hnsp, Hnqr, Hnrq, Hnqs, Hnrs.
       Case-split on HRsr:
       - HRsr: edges {p→q, s→q, s→r} = class (f) N with a=p, b=q, c=s, d=r.
       - Hnsr: edges {p→q, s→q} = class (d) inv-V with a=p, b=s, c=q, d=r. *)
    destruct (classic (R2 s r)) as [HRsr | Hnsr].
    { apply (@n4_N_two_realizer B R2 HR2 Hcard).
      exists p, q, s, r.
      split; [exact Hpq_neq |].
      split; [exact Hps_neq |].
      split; [exact Hpr_neq |].
      split; [exact Hqs_neq |].
      split; [exact Hqr_neq |].
      split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
      split; [exact HRpq |].
      split; [exact HRsq |].
      split; [exact HRsr |].
      intros x y HRxy.
      destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
      right.
      destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
      destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
        subst x; subst y;
        try (exfalso; apply Hneq; reflexivity);
        first
          [ (left; split; reflexivity)                          (* (p,q) *)
          | (right; left; split; reflexivity)                   (* (s,q) *)
          | (right; right; split; reflexivity)                  (* (s,r) *)
          | (exfalso;
             match goal with
             | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
             end)
          | (exfalso; apply Hpq_neq; apply poset_antisym;
             [exact HRpq | exact HRxy]) ]. }
    (* Hnsr: edges {p→q, s→q} = inv-V. *)
    apply (@n4_inv_V_two_realizer B R2 HR2 Hcard).
    exists p, s, q, r.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hsq_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact Hqr_neq |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    intros x y HRxy.
    destruct (classic (x = y)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (Hcov4 x) as [Hx | [Hx | [Hx | Hx]]];
    destruct (Hcov4 y) as [Hy | [Hy | [Hy | Hy]]];
      subst x; subst y;
      try (exfalso; apply Hneq; reflexivity);
      first
        [ (left; split; reflexivity)             (* (p, q) *)
        | (right; split; reflexivity)            (* (s, q) *)
        | (exfalso;
           match goal with
           | [ HR : R2 ?x ?y, Hn : ~ R2 ?x ?y |- _ ] => apply Hn; exact HR
           end)
        | (exfalso; apply Hpq_neq; apply poset_antisym;
           [exact HRpq | exact HRxy]) ]. }
  destruct (classic (R2 r s)) as [HRrs | Hnrs].
  { (* Only [(p, q), (r, s)] are strict edges; class (e). *)
    destruct (classic (R2 s r)) as [HRsr | Hnsr].
    { (* Both r→s and s→r ⇒ r = s by antisymmetry, contradicting Hrs_neq. *)
      exfalso. apply Hrs_neq. apply poset_antisym; assumption. }
    exact (@n4_residual_edge_count_2_rs B R2 HR2 Hcard p q r s
             Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4
             HRpq HRrs Hnpr Hnrp Hnps Hnsp Hnqr Hnrq Hnqs Hnsq Hnsr). }
  destruct (classic (R2 s r)) as [HRsr | Hnsr].
  { (* Only [(p, q), (s, r)] are strict edges; class (e) alt labeling. *)
    exact (@n4_residual_edge_count_2_sr B R2 HR2 Hcard p q r s
             Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4
             HRpq HRsr Hnpr Hnrp Hnps Hnsp Hnqr Hnrq Hnqs Hnsq Hnrs). }
  (* All ten directed non-[{p,q}] edges are absent.  Class (a). *)
  exact (@n4_residual_edge_count_1 B R2 HR2 Hcard p q r s
           Hpq_neq Hpr_neq Hps_neq Hqr_neq Hqs_neq Hrs_neq Hcov4 HRpq
           Hnpr Hnrp Hnps Hnsp Hnqr Hnrq Hnqs Hnsq Hnrs Hnsr).
Qed.

(** Main n=4 dispatcher.

    Extracts one strict edge [R2 p q] (from non-antichain) and four
    pairwise distinct elements [p, q, r, s] (via
    [carrier_4_destructure]).  Walks a structural case tree to detect
    which of the EIGHT named isomorphism classes (a)-(h) the poset
    matches WITH RESPECT TO the canonical labeling
    [(witness-edge) = (p, q)]:

      - 1 strict edge        → class (a) via [n4_one_edge_two_realizer]
      - 2 strict edges       → class (e) [(r,s) or (s,r) disjoint],
                                class (c) [V with shared bottom p],
                                or class (d) [∧ with shared top q]
      - 3 strict edges       → class (b) [chain p<q<r or p<q<s],
                                class (f) [N with central edge (r,q,s)
                                  or (s,q,r)],
                                class (g) [3-claw-up at p:
                                  (p,q), (p,r), (p,s)],
                                or class (h) [3-claw-down at q:
                                  (p,q), (r,q), (s,q)]

    For each matching case the dispatcher invokes the corresponding
    Qed sub-lemma; otherwise it falls through to the focused admit
    [n4_residual_classes_two_realizer], which captures:
      - alternate labelings of (b)-(h) where the witness edge (p,q) is
        not the canonical "first" edge of the class
      - the 6 further isomorphism classes (i)-(n) — diamond, bowtie,
        chain-of-3 + below/above, Y-up/down extended — for each of
        which a Qed per-class sub-lemma already exists in this file
        ([n4_diamond_two_realizer], [n4_bowtie_two_realizer],
        [n4_chain3_plus_below_two_realizer],
        [n4_chain3_plus_above_two_realizer],
        [n4_Y_chain_up_two_realizer], [n4_Y_chain_down_two_realizer]).
        Extending the cascade to route them is left as follow-up. *)
Lemma n4_nonantichain_nonchain_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 4 ->
  ~ (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, @Incomparable B R2 a b) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex.
  (* Extract one strict edge (p, q) with p <> q and R2 p q. *)
  assert (Hedge : exists p q : B, p <> q /\ R2 p q).
  { apply Classical_Pred_Type.not_all_ex_not in Hnonantichain.
    destruct Hnonantichain as [p Hp].
    apply Classical_Pred_Type.not_all_ex_not in Hp.
    destruct Hp as [q Hq].
    exists p, q.
    split;
      [ intro Heq; apply Hq; intros HRpq_unused; exact Heq
      | destruct (classic (R2 p q)) as [HR | HnR];
          [ exact HR
          | exfalso; apply Hq; intro Hcontra; contradiction ]
      ]. }
  destruct Hedge as [p [q [Hpq_neq HRpq]]].
  (* Decide whether ANY other off-diagonal pair is in R2. *)
  destruct (classic (exists x y : B, x <> y /\ R2 x y /\
                       ~ (x = p /\ y = q))) as [Hother | Honly].
  - (* Some other strict edge exists.  Extract the other 2 elements
       [r, s] via [carrier_4_destructure] and try to route to class
       (e) (disjoint chains) if the other edge has disjoint endpoints
       from (p, q) and there is no third strict edge. *)
    destruct (@carrier_4_destructure B p q Hcard Hpq_neq)
      as [r [s [Hpr_neq [Hps_neq [Hqr_neq [Hqs_neq [Hrs_neq Hcov4]]]]]]].
    (* Test: is R2 r s the second strict edge, with no third edge? *)
    destruct (classic (R2 r s /\
                       forall x y : B, x <> y -> R2 x y ->
                         (x = p /\ y = q) \/ (x = r /\ y = s)))
      as [Hclass_e_rs | Hnot_e_rs].
    + (* Class (e), edges (p, q) and (r, s). *)
      apply (@n4_disjoint_chains_two_realizer B R2 HR2 Hcard).
      destruct Hclass_e_rs as [HRrs HR_only_e].
      exists p, q, r, s.
      repeat (split; [first [exact Hpq_neq | exact Hpr_neq | exact Hps_neq
                            | exact Hqr_neq | exact Hqs_neq | exact Hrs_neq] |]).
      split; [exact HRpq |].
      split; [exact HRrs |].
      intros a b HRab.
      destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
      destruct (HR_only_e a b Hneq HRab) as [[Hap Hbq] | [Har Hbs]].
      * right; left; split; assumption.
      * right; right; split; assumption.
    + (* Test: is R2 s r the second strict edge, with no third edge?
         (This handles disjoint chains where the second edge points
         the other way among the {r, s} pair.) *)
      destruct (classic (R2 s r /\
                         forall x y : B, x <> y -> R2 x y ->
                           (x = p /\ y = q) \/ (x = s /\ y = r)))
        as [Hclass_e_sr | Hnot_e_sr].
      * (* Class (e), edges (p, q) and (s, r). *)
        apply (@n4_disjoint_chains_two_realizer B R2 HR2 Hcard).
        destruct Hclass_e_sr as [HRsr HR_only_e].
        exists p, q, s, r.
        (* Distinctness for p, q, s, r: rearrangement of {p,q,r,s}. *)
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRsr |].
        intros a b HRab.
        destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
        destruct (HR_only_e a b Hneq HRab) as [[Hap Hbq] | [Has Hbr]].
        -- right; left; split; assumption.
        -- right; right; split; assumption.
      * (* Neither disjoint-chain pattern matched.  Try V-shape (class c)
           with shared bottom [p]: edges (p, q) and (p, r), or (p, q) and (p, s). *)
        destruct (classic (R2 p r /\
                           forall x y : B, x <> y -> R2 x y ->
                             (x = p /\ y = q) \/ (x = p /\ y = r)))
          as [Hclass_c_r | Hnot_c_r].
        -- (* Class (c) V-shape: a=p, b=q, c=r, d=s. *)
           apply (@n4_V_two_realizer B R2 HR2 Hcard).
           destruct Hclass_c_r as [HRpr HR_only_c].
           exists p, q, r, s.
           split; [exact Hpq_neq |].
           split; [exact Hpr_neq |].
           split; [exact Hps_neq |].
           split; [exact Hqr_neq |].
           split; [exact Hqs_neq |].
           split; [exact Hrs_neq |].
           split; [exact HRpq |].
           split; [exact HRpr |].
           intros a b HRab.
           destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
           destruct (HR_only_c a b Hneq HRab) as [[Hap Hbq] | [Hap Hbr]].
           ++ right; left; split; assumption.
           ++ right; right; split; assumption.
        -- (* Try class (c) with b=q, c=s. *)
           destruct (classic (R2 p s /\
                              forall x y : B, x <> y -> R2 x y ->
                                (x = p /\ y = q) \/ (x = p /\ y = s)))
             as [Hclass_c_s | Hnot_c_s].
           ++ (* Class (c) V-shape: a=p, b=q, c=s, d=r. *)
              apply (@n4_V_two_realizer B R2 HR2 Hcard).
              destruct Hclass_c_s as [HRps HR_only_c].
              exists p, q, s, r.
              split; [exact Hpq_neq |].
              split; [exact Hps_neq |].
              split; [exact Hpr_neq |].
              split; [exact Hqs_neq |].
              split; [exact Hqr_neq |].
              split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
              split; [exact HRpq |].
              split; [exact HRps |].
              intros a b HRab.
              destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
              destruct (HR_only_c a b Hneq HRab) as [[Hap Hbq] | [Hap Hbs]].
              ** right; left; split; assumption.
              ** right; right; split; assumption.
           ++ (* Try class (d) ∧-shape with shared top [q]: edges (p, q) and (r, q). *)
              destruct (classic (R2 r q /\
                                 forall x y : B, x <> y -> R2 x y ->
                                   (x = p /\ y = q) \/ (x = r /\ y = q)))
                as [Hclass_d_r | Hnot_d_r].
              ** (* Class (d) with a=p, b=r, c=q, d=s. *)
                 apply (@n4_inv_V_two_realizer B R2 HR2 Hcard).
                 destruct Hclass_d_r as [HRrq HR_only_d].
                 exists p, r, q, s.
                 split; [exact Hpr_neq |].
                 split; [exact Hpq_neq |].
                 split; [exact Hps_neq |].
                 split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
                 split; [exact Hrs_neq |].
                 split; [exact Hqs_neq |].
                 split; [exact HRpq |].
                 split; [exact HRrq |].
                 intros a b HRab.
                 destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
                 destruct (HR_only_d a b Hneq HRab) as [[Hap Hbq] | [Har Hbq]].
                 --- right; left; split; assumption.
                 --- right; right; split; assumption.
              ** (* Try class (d) with edges (p, q) and (s, q). *)
                 destruct (classic (R2 s q /\
                                    forall x y : B, x <> y -> R2 x y ->
                                      (x = p /\ y = q) \/ (x = s /\ y = q)))
                   as [Hclass_d_s | Hnot_d_s].
                 --- (* Class (d) with a=p, b=s, c=q, d=r. *)
                     apply (@n4_inv_V_two_realizer B R2 HR2 Hcard).
                     destruct Hclass_d_s as [HRsq HR_only_d].
                     exists p, s, q, r.
                     split; [exact Hps_neq |].
                     split; [exact Hpq_neq |].
                     split; [exact Hpr_neq |].
                     split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
                     split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
                     split; [exact Hqr_neq |].
                     split; [exact HRpq |].
                     split; [exact HRsq |].
                     intros a b HRab.
                     destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
                     destruct (HR_only_d a b Hneq HRab) as [[Hap Hbq] | [Has Hbq]].
                     +++ right; left; split; assumption.
                     +++ right; right; split; assumption.
                 --- (* Try class (b) chain-of-3 (p < q < r), isolated s. *)
                     destruct (classic (R2 q r /\ R2 p r /\
                                        forall x y : B, x <> y -> R2 x y ->
                                          (x = p /\ y = q) \/ (x = q /\ y = r) \/
                                          (x = p /\ y = r)))
                       as [Hclass_b_qr | Hnot_b_qr].
                     +++ (* Class (b) with a=p, b=q, c=r, d=s. *)
                         apply (@n4_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
                         destruct Hclass_b_qr as [HRqr [HRpr HR_only_b]].
                         exists p, q, r, s.
                         split; [exact Hpq_neq |].
                         split; [exact Hpr_neq |].
                         split; [exact Hps_neq |].
                         split; [exact Hqr_neq |].
                         split; [exact Hqs_neq |].
                         split; [exact Hrs_neq |].
                         split; [exact HRpq |].
                         split; [exact HRqr |].
                         split; [exact HRpr |].
                         intros a b HRab.
                         destruct (classic (a = b)) as [Heq | Hneq];
                           [left; exact Heq |].
                         destruct (HR_only_b a b Hneq HRab)
                           as [[Hap Hbq] | [[Haq Hbr] | [Hap Hbr]]].
                         *** right. left. split; assumption.
                         *** right. right. right. split; assumption.
                         *** right. right. left. split; assumption.
                     +++ (* Try chain (p < q < s), isolated r. *)
                         destruct (classic (R2 q s /\ R2 p s /\
                                            forall x y : B, x <> y -> R2 x y ->
                                              (x = p /\ y = q) \/ (x = q /\ y = s) \/
                                              (x = p /\ y = s)))
                           as [Hclass_b_qs | Hnot_b_qs].
                         *** (* Class (b) with a=p, b=q, c=s, d=r. *)
                             apply (@n4_chain_plus_isolated_two_realizer
                                      B R2 HR2 Hcard).
                             destruct Hclass_b_qs as [HRqs [HRps HR_only_b]].
                             exists p, q, s, r.
                             split; [exact Hpq_neq |].
                             split; [exact Hps_neq |].
                             split; [exact Hpr_neq |].
                             split; [exact Hqs_neq |].
                             split; [exact Hqr_neq |].
                             split; [intro Hsr_eq; apply Hrs_neq;
                                     symmetry; exact Hsr_eq |].
                             split; [exact HRpq |].
                             split; [exact HRqs |].
                             split; [exact HRps |].
                             intros a b HRab.
                             destruct (classic (a = b)) as [Heq | Hneq];
                               [left; exact Heq |].
                             destruct (HR_only_b a b Hneq HRab)
                               as [[Hap Hbq] | [[Haq Hbs] | [Hap Hbs]]].
                             ---- right. left. split; assumption.
                             ---- right. right. right. split; assumption.
                             ---- right. right. left. split; assumption.
                         *** (* Try class (f) N-shape with (p,q)=(a,b),
                                c=r, d=s: edges (p,q), (r,q), (r,s). *)
                             destruct (classic (R2 r q /\ R2 r s /\
                                                forall x y : B, x <> y -> R2 x y ->
                                                  (x = p /\ y = q) \/
                                                  (x = r /\ y = q) \/
                                                  (x = r /\ y = s)))
                               as [Hclass_f_rs | Hnot_f_rs].
                             ---- (* Class (f) with a=p, b=q, c=r, d=s. *)
                                  apply (@n4_N_two_realizer B R2 HR2 Hcard).
                                  destruct Hclass_f_rs as [HRrq [HRrs HR_only_f]].
                                  exists p, q, r, s.
                                  split; [exact Hpq_neq |].
                                  split; [exact Hpr_neq |].
                                  split; [exact Hps_neq |].
                                  split; [exact Hqr_neq |].
                                  split; [exact Hqs_neq |].
                                  split; [exact Hrs_neq |].
                                  split; [exact HRpq |].
                                  split; [exact HRrq |].
                                  split; [exact HRrs |].
                                  intros a b HRab.
                                  destruct (classic (a = b)) as [Heq | Hneq];
                                    [left; exact Heq |].
                                  destruct (HR_only_f a b Hneq HRab)
                                    as [[Hap Hbq] | [[Har Hbq] | [Har Hbs]]].
                                  ++++ right. left. split; assumption.
                                  ++++ right. right. left. split; assumption.
                                  ++++ right. right. right. split; assumption.
                             ---- (* Try class (f) with c=s, d=r:
                                     edges (p,q), (s,q), (s,r). *)
                                  destruct (classic (R2 s q /\ R2 s r /\
                                                     forall x y : B, x <> y -> R2 x y ->
                                                       (x = p /\ y = q) \/
                                                       (x = s /\ y = q) \/
                                                       (x = s /\ y = r)))
                                    as [Hclass_f_sr | Hnot_f_sr].
                                  ++++ (* Class (f) with a=p, b=q, c=s, d=r. *)
                                       apply (@n4_N_two_realizer B R2 HR2 Hcard).
                                       destruct Hclass_f_sr as [HRsq [HRsr HR_only_f]].
                                       exists p, q, s, r.
                                       split; [exact Hpq_neq |].
                                       split; [exact Hps_neq |].
                                       split; [exact Hpr_neq |].
                                       split; [exact Hqs_neq |].
                                       split; [exact Hqr_neq |].
                                       split; [intro Hsr_eq; apply Hrs_neq;
                                               symmetry; exact Hsr_eq |].
                                       split; [exact HRpq |].
                                       split; [exact HRsq |].
                                       split; [exact HRsr |].
                                       intros a b HRab.
                                       destruct (classic (a = b)) as [Heq | Hneq];
                                         [left; exact Heq |].
                                       destruct (HR_only_f a b Hneq HRab)
                                         as [[Hap Hbq] | [[Has Hbq] | [Has Hbr]]].
                                       **** right. left. split; assumption.
                                       **** right. right. left. split; assumption.
                                       **** right. right. right. split; assumption.
                                  ++++ (* Try class (g) 3-claw-up at p:
                                          edges (p, q), (p, r), (p, s). *)
                                       destruct (classic (R2 p r /\ R2 p s /\
                                                          forall x y : B, x <> y -> R2 x y ->
                                                            (x = p /\ y = q) \/
                                                            (x = p /\ y = r) \/
                                                            (x = p /\ y = s)))
                                         as [Hclass_g | Hnot_g].
                                       ****
                                            apply (@n4_3claw_up_two_realizer
                                                     B R2 HR2 Hcard).
                                            destruct Hclass_g as [HRpr [HRps HR_only_g]].
                                            exists p, q, r, s.
                                            split; [exact Hpq_neq |].
                                            split; [exact Hpr_neq |].
                                            split; [exact Hps_neq |].
                                            split; [exact Hqr_neq |].
                                            split; [exact Hqs_neq |].
                                            split; [exact Hrs_neq |].
                                            split; [exact HRpq |].
                                            split; [exact HRpr |].
                                            split; [exact HRps |].
                                            intros a b HRab.
                                            destruct (classic (a = b)) as [Heq | Hneq];
                                              [left; exact Heq |].
                                            destruct (HR_only_g a b Hneq HRab)
                                              as [[Hap Hbq] | [[Hap Hbr] | [Hap Hbs]]].
                                            ----- right; left; split; assumption.
                                            ----- right; right; left; split; assumption.
                                            ----- right; right; right; split; assumption.
                                       **** (* Try class (h) 3-claw-down at q:
                                               edges (p, q), (r, q), (s, q). *)
                                            destruct (classic (R2 r q /\ R2 s q /\
                                                               forall x y : B, x <> y -> R2 x y ->
                                                                 (x = p /\ y = q) \/
                                                                 (x = r /\ y = q) \/
                                                                 (x = s /\ y = q)))
                                              as [Hclass_h | Hnot_h].
                                            -----
                                                 apply (@n4_3claw_down_two_realizer
                                                          B R2 HR2 Hcard).
                                                 destruct Hclass_h as [HRrq [HRsq HR_only_h]].
                                                 (* class h: a, b, c, d with d=common top *)
                                                 (* edges p→q, r→q, s→q ⇒ a=p, b=r, c=s, d=q *)
                                                 exists p, r, s, q.
                                                 split; [exact Hpr_neq |].
                                                 split; [exact Hps_neq |].
                                                 split; [exact Hpq_neq |].
                                                 split; [exact Hrs_neq |].
                                                 split; [intro Hrq_eq; apply Hqr_neq;
                                                         symmetry; exact Hrq_eq |].
                                                 split; [intro Hsq_eq; apply Hqs_neq;
                                                         symmetry; exact Hsq_eq |].
                                                 split; [exact HRpq |].
                                                 split; [exact HRrq |].
                                                 split; [exact HRsq |].
                                                 intros a b HRab.
                                                 destruct (classic (a = b)) as [Heq | Hneq];
                                                   [left; exact Heq |].
                                                 destruct (HR_only_h a b Hneq HRab)
                                                   as [[Hap Hbq] | [[Har Hbq] | [Has Hbq]]].
                                                 ++++++ right; left; split; assumption.
                                                 ++++++ right; right; left; split; assumption.
                                                 ++++++ right; right; right; split; assumption.
                                            ----- (* No (g) or (h): dispatch the
                                                     remaining classes (i)-(n)
                                                     via the focused helper. *)
                                                  apply (@n4_dispatch_residual_after_h
                                                           B R2 HR2 Hcard
                                                           Hnonantichain Hinc_ex
                                                           p q r s
                                                           Hpq_neq Hpr_neq Hps_neq
                                                           Hqr_neq Hqs_neq Hrs_neq
                                                           Hcov4 HRpq).
  - (* No other strict edge: only (p, q) is a non-trivial relation.
       This is exactly class (a). *)
    apply (@n4_one_edge_two_realizer B R2 HR2 Hcard).
    exists p, q.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    intros a b HRab.
    destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (classic (a = p /\ b = q)) as [Hpq_match | Hnot_pq].
    + exact Hpq_match.
    + (* Suppose (a, b) is some other strict edge. *)
      exfalso. apply Honly.
      exists a, b. split; [exact Hneq |]. split; [exact HRab |]. exact Hnot_pq.
Qed.

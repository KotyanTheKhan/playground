(** * One-point removal: dim(X) ≤ 1 + dim(X − p)

    Core construction for Trotter's Theorem 2 (= Lemma 5.6), the basis of the
    direct proof of Hiraguchi's bound (see [AntichainDimBound.v]).

    Reference: Trotter 1975 (Proc. AMS 47, 311–316), inequality (1):
    given a realizer {L_1,…,L_d} of X−p, build d+1 linear extensions of X by
    keeping L_1..L_{d-1} (p inserted preserving L_i) and replacing L_d by two
    "block" orders — p as low as possible, p as high as possible.

    This file: the lifted "block" orders [lift_low], [lift_high] and the proof
    that they are linear extensions of R.  Each is a LEXICOGRAPHIC order
    (zone, L): zone ∈ {0,1,2} splits B into  Down(p) | {p} | rest  (for
    [lift_low]) and ties broken by the lifted suborder [Llift L]. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia.
From Stdlib Require Import Classical ClassicalDescription IndefiniteDescription ProofIrrelevance.
From Stdlib Require Import Constructive_sets.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs Szpilrajn Theorems.

Section OnePointRemoval.
  Context {B : Type}.
  Context (R : B -> B -> Prop) `{IsPoset B R}.
  Variable p : B.

  (** The subtype X − p and its restricted relation. *)
  Definition Sub := { a : B | a <> p }.
  Definition Qsub (a b : Sub) : Prop := R (proj1_sig a) (proj1_sig b).

  (** Lift a relation on the subtype to B (on the non-p elements). *)
  Definition Llift (L : Sub -> Sub -> Prop) (a b : B) : Prop :=
    exists (ha : a <> p) (hb : b <> p),
      L (exist _ a ha) (exist _ b hb).

  Section WithL.
    Variable L : Sub -> Sub -> Prop.
    Hypothesis HL : IsLinearExtension Qsub L.

    #[local] Instance HLtot : IsTotalOrder L := linear_is_total HL.
    #[local] Instance HLpos : IsPoset Sub L := total_is_poset (IsTotalOrder := HLtot).

    (** Properties of [Llift] inherited from [L] being a linear extension. *)
    Lemma Llift_proof_irrel :
      forall (a b : B) (ha ha' : a <> p) (hb hb' : b <> p),
        L (exist _ a ha) (exist _ b hb) ->
        L (exist _ a ha') (exist _ b hb').
    Proof.
      intros a b ha ha' hb hb' HLab.
      rewrite (proof_irrelevance _ ha' ha).
      rewrite (proof_irrelevance _ hb' hb). exact HLab.
    Qed.

    Lemma Llift_refl : forall a, a <> p -> Llift L a a.
    Proof.
      intros a ha. exists ha, ha.
      exact (poset_refl (R := L) (exist _ a ha)).
    Qed.

    Lemma Llift_antisym : forall a b, Llift L a b -> Llift L b a -> a = b.
    Proof.
      intros a b [ha [hb Hab]] [hb' [ha' Hba]].
      assert (Heq : exist (fun x => x <> p) a ha = exist _ b hb).
      { apply (poset_antisym (R := L)); [ exact Hab |].
        exact (Llift_proof_irrel b a hb' hb ha' ha Hba). }
      exact (f_equal (@proj1_sig _ _) Heq).
    Qed.

    Lemma Llift_trans : forall a b c, Llift L a b -> Llift L b c -> Llift L a c.
    Proof.
      intros a b c [ha [hb Hab]] [hb' [hc Hbc]].
      exists ha, hc.
      apply (poset_trans (R := L)) with (exist _ b hb); [ exact Hab |].
      exact (Llift_proof_irrel b c hb' hb hc hc Hbc).
    Qed.

    Lemma Llift_total : forall a b, a <> p -> b <> p -> Llift L a b \/ Llift L b a.
    Proof.
      intros a b ha hb.
      destruct (total_comparable (IsTotalOrder := linear_is_total HL)
                  (exist _ a ha) (exist _ b hb)) as [Hab | Hba].
      - left. exists ha, hb. exact Hab.
      - right. exists hb, ha. exact Hba.
    Qed.

    Lemma Llift_extends : forall a b, R a b -> a <> p -> b <> p -> Llift L a b.
    Proof.
      intros a b Hab ha hb. exists ha, hb.
      apply (linear_extends HL). unfold Qsub. simpl. exact Hab.
    Qed.

    (** Tie-break comparator: [L] on non-p pairs, plus [p ≤ p]. *)
    Definition cmp (a b : B) : Prop := (a = p /\ b = p) \/ Llift L a b.

    (** ---- [lift_low]: zone  Down(p) < {p} < rest,  L within zones ---- *)
    Definition zlow (a : B) : nat :=
      if excluded_middle_informative (a = p) then 1
      else if excluded_middle_informative (R a p) then 0 else 2.

    Definition lift_low (a b : B) : Prop :=
      zlow a < zlow b \/ (zlow a = zlow b /\ cmp a b).

    (** ---- [lift_high]: zone  rest < {p} < Up(p),  L within zones ---- *)
    Definition zhigh (a : B) : nat :=
      if excluded_middle_informative (a = p) then 1
      else if excluded_middle_informative (R p a) then 2 else 0.

    Definition lift_high (a b : B) : Prop :=
      zhigh a < zhigh b \/ (zhigh a = zhigh b /\ cmp a b).

    (** zlow case facts. *)
    Lemma zlow_p : zlow p = 1.
    Proof. unfold zlow. destruct (excluded_middle_informative (p = p)); [reflexivity | contradiction]. Qed.

    Lemma zlow_down : forall a, a <> p -> R a p -> zlow a = 0.
    Proof.
      intros a ha Hap. unfold zlow.
      destruct (excluded_middle_informative (a = p)); [contradiction |].
      destruct (excluded_middle_informative (R a p)); [reflexivity | contradiction].
    Qed.

    Lemma zlow_rest : forall a, a <> p -> ~ R a p -> zlow a = 2.
    Proof.
      intros a ha Hnap. unfold zlow.
      destruct (excluded_middle_informative (a = p)); [contradiction |].
      destruct (excluded_middle_informative (R a p)); [contradiction | reflexivity].
    Qed.

    Lemma zlow_eq_cases : forall a, zlow a = 0 \/ zlow a = 1 \/ zlow a = 2.
    Proof. intro a. unfold zlow. repeat destruct excluded_middle_informative; auto. Qed.

    Lemma zlow_1_iff : forall a, zlow a = 1 <-> a = p.
    Proof.
      intro a. unfold zlow. split.
      - repeat destruct excluded_middle_informative; intro; first [exact e | discriminate | lia | auto].
      - intro Ha. destruct (excluded_middle_informative (a = p)); [reflexivity | contradiction].
    Qed.

    (** [cmp] is reflexive / antisym / transitive where used (same zone). *)
    Lemma cmp_refl : forall a, cmp a a.
    Proof.
      intro a. unfold cmp. destruct (classic (a = p)) as [-> | Hne].
      - left; split; reflexivity.
      - right. apply Llift_refl; exact Hne.
    Qed.

    (** ---- [lift_low] is a linear extension of R ---- *)
    Lemma lift_low_refl : forall a, lift_low a a.
    Proof. intro a. right. split; [reflexivity | apply cmp_refl]. Qed.

    Lemma lift_low_antisym : forall a b, lift_low a b -> lift_low b a -> a = b.
    Proof.
      intros a b Hab Hba.
      destruct Hab as [Hlt | [Heq Hcab]]; destruct Hba as [Hlt' | [Heq' Hcba]]; try lia.
      (* both equal-zone branch: cmp a b /\ cmp b a *)
      unfold cmp in Hcab, Hcba.
      destruct Hcab as [[-> ->] | Hlab]; [reflexivity |].
      destruct Hcba as [[-> ->] | Hlba]; [reflexivity |].
      exact (Llift_antisym a b Hlab Hlba).
    Qed.

    Lemma lift_low_trans : forall a b c, lift_low a b -> lift_low b c -> lift_low a c.
    Proof.
      intros a b c Hab Hbc.
      destruct Hab as [Hlt | [Heq Hcab]]; destruct Hbc as [Hlt' | [Heq' Hcbc]].
      - left; lia.
      - left; lia.
      - left; lia.
      - right. split; [lia |].
        unfold cmp in *.
        destruct Hcab as [[Hap Hbp] | Hlab].
        + (* a = p, b = p *) subst a b. exact Hcbc.
        + destruct Hcbc as [[Hbp Hcp] | Hlbc].
          * subst b c.
            (* a <> p (since Llift L a p means a <> p) *)
            destruct Hlab as [ha [hb _]]. left; split; [|reflexivity].
            exfalso. apply hb; reflexivity.
          * right. exact (Llift_trans a b c Hlab Hlbc).
    Qed.

    Lemma lift_low_total : forall a b, lift_low a b \/ lift_low b a.
    Proof.
      intros a b. destruct (Nat.lt_trichotomy (zlow a) (zlow b)) as [Hlt | [Heq | Hgt]].
      - left; left; exact Hlt.
      - (* same zone *)
        destruct (classic (a = p)) as [-> | Ha].
        + rewrite zlow_p in Heq. symmetry in Heq. rewrite zlow_1_iff in Heq. subst b.
          left. apply lift_low_refl.
        + destruct (classic (b = p)) as [-> | Hb].
          * rewrite zlow_p in Heq. rewrite zlow_1_iff in Heq. contradiction.
          * destruct (Llift_total a b Ha Hb) as [Hl | Hl].
            -- left; right; split; [exact Heq | right; exact Hl].
            -- right; right; split; [lia | right; exact Hl].
      - right; left; exact Hgt.
    Qed.

    Lemma lift_low_poset : IsPoset B lift_low.
    Proof.
      constructor.
      - exact lift_low_refl.
      - exact lift_low_antisym.
      - exact lift_low_trans.
    Qed.

    Lemma lift_low_total_order : IsTotalOrder lift_low.
    Proof.
      constructor.
      - exact lift_low_poset.
      - exact lift_low_total.
    Qed.

    Lemma lift_low_extends : forall a b, R a b -> lift_low a b.
    Proof.
      intros a b Hab.
      destruct (classic (a = p)) as [-> | Ha].
      - (* a = p: zlow p = 1; need zlow b >= 1 *)
        destruct (classic (b = p)) as [-> | Hb].
        + apply lift_low_refl.
        + (* b <> p; R p b.  b not in Down(p): else R b p /\ R p b -> b = p. *)
          assert (Hnbp : ~ R b p).
          { intro Hbp. apply Hb. exact (poset_antisym _ _ Hbp Hab). }
          left. rewrite zlow_p, (zlow_rest b Hb Hnbp). lia.
      - destruct (classic (b = p)) as [-> | Hb].
        + (* b = p, a <> p, R a p -> zlow a = 0 < 1 *)
          left. rewrite zlow_p, (zlow_down a Ha Hab). lia.
        + (* a,b <> p *)
          destruct (classic (R a p)) as [Hap | Hnap].
          * destruct (classic (R b p)) as [Hbp | Hnbp].
            -- (* both Down: zone 0, tie by Llift *)
               right. rewrite (zlow_down a Ha Hap), (zlow_down b Hb Hbp).
               split; [reflexivity | right; apply Llift_extends; assumption].
            -- (* a Down (0), b rest (2) *)
               left. rewrite (zlow_down a Ha Hap), (zlow_rest b Hb Hnbp). lia.
          * (* a in rest (zlow=2); R a b, ~R a p -> ~R b p, so b in rest too *)
            assert (Hnbp : ~ R b p).
            { intro Hbp. apply Hnap. exact (poset_trans _ _ _ Hab Hbp). }
            right. rewrite (zlow_rest a Ha Hnap), (zlow_rest b Hb Hnbp).
            split; [reflexivity | right; apply Llift_extends; assumption].
    Qed.

    Lemma lift_low_is_linext : IsLinearExtension R lift_low.
    Proof.
      constructor.
      - exact lift_low_total_order.
      - exact lift_low_extends.
    Qed.

    (** ---- [lift_high] is a linear extension of R (dual of [lift_low]) ---- *)
    Lemma zhigh_p : zhigh p = 1.
    Proof. unfold zhigh. destruct (excluded_middle_informative (p = p)); [reflexivity | contradiction]. Qed.

    Lemma zhigh_up : forall a, a <> p -> R p a -> zhigh a = 2.
    Proof.
      intros a ha Hpa. unfold zhigh.
      destruct (excluded_middle_informative (a = p)); [contradiction |].
      destruct (excluded_middle_informative (R p a)); [reflexivity | contradiction].
    Qed.

    Lemma zhigh_rest : forall a, a <> p -> ~ R p a -> zhigh a = 0.
    Proof.
      intros a ha Hnpa. unfold zhigh.
      destruct (excluded_middle_informative (a = p)); [contradiction |].
      destruct (excluded_middle_informative (R p a)); [contradiction | reflexivity].
    Qed.

    Lemma zhigh_1_iff : forall a, zhigh a = 1 <-> a = p.
    Proof.
      intro a. unfold zhigh. split.
      - repeat destruct excluded_middle_informative; intro; first [exact e | discriminate | lia | auto].
      - intro Ha. destruct (excluded_middle_informative (a = p)); [reflexivity | contradiction].
    Qed.

    Lemma lift_high_refl : forall a, lift_high a a.
    Proof. intro a. right. split; [reflexivity | apply cmp_refl]. Qed.

    Lemma lift_high_antisym : forall a b, lift_high a b -> lift_high b a -> a = b.
    Proof.
      intros a b Hab Hba.
      destruct Hab as [Hlt | [Heq Hcab]]; destruct Hba as [Hlt' | [Heq' Hcba]]; try lia.
      unfold cmp in Hcab, Hcba.
      destruct Hcab as [[-> ->] | Hlab]; [reflexivity |].
      destruct Hcba as [[-> ->] | Hlba]; [reflexivity |].
      exact (Llift_antisym a b Hlab Hlba).
    Qed.

    Lemma lift_high_trans : forall a b c, lift_high a b -> lift_high b c -> lift_high a c.
    Proof.
      intros a b c Hab Hbc.
      destruct Hab as [Hlt | [Heq Hcab]]; destruct Hbc as [Hlt' | [Heq' Hcbc]].
      - left; lia.
      - left; lia.
      - left; lia.
      - right. split; [lia |].
        unfold cmp in *.
        destruct Hcab as [[Hap Hbp] | Hlab].
        + subst a b. exact Hcbc.
        + destruct Hcbc as [[Hbp Hcp] | Hlbc].
          * subst b c. destruct Hlab as [ha [hb _]]. left; split; [|reflexivity].
            exfalso. apply hb; reflexivity.
          * right. exact (Llift_trans a b c Hlab Hlbc).
    Qed.

    Lemma lift_high_total : forall a b, lift_high a b \/ lift_high b a.
    Proof.
      intros a b. destruct (Nat.lt_trichotomy (zhigh a) (zhigh b)) as [Hlt | [Heq | Hgt]].
      - left; left; exact Hlt.
      - destruct (classic (a = p)) as [-> | Ha].
        + rewrite zhigh_p in Heq. symmetry in Heq. rewrite zhigh_1_iff in Heq. subst b.
          left. apply lift_high_refl.
        + destruct (classic (b = p)) as [-> | Hb].
          * rewrite zhigh_p in Heq. rewrite zhigh_1_iff in Heq. contradiction.
          * destruct (Llift_total a b Ha Hb) as [Hl | Hl].
            -- left; right; split; [exact Heq | right; exact Hl].
            -- right; right; split; [lia | right; exact Hl].
      - right; left; exact Hgt.
    Qed.

    Lemma lift_high_poset : IsPoset B lift_high.
    Proof. constructor; [exact lift_high_refl | exact lift_high_antisym | exact lift_high_trans]. Qed.

    Lemma lift_high_total_order : IsTotalOrder lift_high.
    Proof. constructor; [exact lift_high_poset | exact lift_high_total]. Qed.

    Lemma lift_high_extends : forall a b, R a b -> lift_high a b.
    Proof.
      intros a b Hab.
      destruct (classic (a = p)) as [-> | Ha].
      - destruct (classic (b = p)) as [-> | Hb].
        + apply lift_high_refl.
        + left. rewrite zhigh_p, (zhigh_up b Hb Hab). lia.
      - destruct (classic (b = p)) as [-> | Hb].
        + (* b = p, a <> p, R a p -> ~ R p a -> zhigh a = 0 < 1 *)
          assert (Hnpa : ~ R p a).
          { intro Hpa. apply Ha. exact (poset_antisym _ _ Hab Hpa). }
          left. rewrite zhigh_p, (zhigh_rest a Ha Hnpa). lia.
        + destruct (classic (R p a)) as [Hpa | Hnpa].
          * (* a in Up; R p a, R a b -> R p b -> b in Up *)
            assert (Hpb : R p b) by exact (poset_trans _ _ _ Hpa Hab).
            right. rewrite (zhigh_up a Ha Hpa), (zhigh_up b Hb Hpb).
            split; [reflexivity | right; apply Llift_extends; assumption].
          * destruct (classic (R p b)) as [Hpb | Hnpb].
            -- left. rewrite (zhigh_rest a Ha Hnpa), (zhigh_up b Hb Hpb). lia.
            -- right. rewrite (zhigh_rest a Ha Hnpa), (zhigh_rest b Hb Hnpb).
               split; [reflexivity | right; apply Llift_extends; assumption].
    Qed.

    Lemma lift_high_is_linext : IsLinearExtension R lift_high.
    Proof. constructor; [exact lift_high_total_order | exact lift_high_extends]. Qed.

    (** ---- Reversal facts (the coverage core for the singled-out L_d) ---- *)

    (** [lift_low] reverses (a,p) when a is not below p. *)
    Lemma lift_low_rev_ap : forall a, a <> p -> ~ R a p -> ~ lift_low a p.
    Proof.
      intros a Ha Hnap Hl. unfold lift_low in Hl.
      rewrite (zlow_rest a Ha Hnap), zlow_p in Hl.
      destruct Hl as [Hlt | [Heq _]]; lia.
    Qed.

    (** [lift_high] reverses (p,b) when p is not below b. *)
    Lemma lift_high_rev_pb : forall b, b <> p -> ~ R p b -> ~ lift_high p b.
    Proof.
      intros b Hb Hnpb Hh. unfold lift_high in Hh.
      rewrite zhigh_p, (zhigh_rest b Hb Hnpb) in Hh.
      destruct Hh as [Hlt | [Heq _]]; lia.
    Qed.

    (** A non-p pair not L-ordered (a → b) is reversed by [lift_low] or
        [lift_high]: the only way both keep it is a∈D(p) ∧ b∈U(p), forcing R a b
        hence Llift L a b. *)
    Lemma lift_low_high_rev_SS :
      forall a b, a <> p -> b <> p -> ~ Llift L a b ->
        ~ lift_low a b \/ ~ lift_high a b.
    Proof.
      intros a b Ha Hb Hnl.
      destruct (classic (lift_low a b)) as [Hlo | Hlo]; [| left; exact Hlo].
      destruct (classic (lift_high a b)) as [Hhi | Hhi]; [| right; exact Hhi].
      exfalso.
      assert (Hcmp : ~ cmp a b).
      { intros [[Hap _] | Hl]; [ apply Ha; exact Hap | exact (Hnl Hl) ]. }
      (* both hold ⟹ zlow a < zlow b and zhigh a < zhigh b *)
      assert (Hzlo : zlow a < zlow b).
      { unfold lift_low in Hlo. destruct Hlo as [H' | [_ Hc]]; [ exact H' | exfalso; exact (Hcmp Hc) ]. }
      assert (Hzhi : zhigh a < zhigh b).
      { unfold lift_high in Hhi. destruct Hhi as [H' | [_ Hc]]; [ exact H' | exfalso; exact (Hcmp Hc) ]. }
      (* zlow a < zlow b ⟹ R a p (else zlow a = 2 ≥ zlow b) *)
      assert (Hap : R a p).
      { destruct (classic (R a p)) as [Hap | Hnap]; [ exact Hap |].
        rewrite (zlow_rest a Ha Hnap) in Hzlo.
        destruct (zlow_eq_cases b) as [E | [E | E]]; rewrite E in Hzlo; lia. }
      (* zhigh a < zhigh b ⟹ R p b (else zhigh b = 0) *)
      assert (Hpb : R p b).
      { destruct (classic (R p b)) as [Hpb | Hnpb]; [ exact Hpb |].
        rewrite (zhigh_rest b Hb Hnpb) in Hzhi. lia. }
      (* R a p ∧ R p b ⟹ R a b ⟹ Llift L a b, contradiction *)
      apply Hnl. apply Llift_extends; [ exact (poset_trans _ _ _ Hap Hpb) | exact Ha | exact Hb ].
    Qed.

    (** ---- [lift_keep]: a linear extension of R restricting to [Llift L] on
        X − p (p inserted WITHOUT reordering S).  Obtained from Szpilrajn applied
        to the partial order [Qkeep], which already contains R and [Llift L]. ---- *)
    Definition Qkeep (a b : B) : Prop :=
      (a = p /\ b = p)
      \/ (a = p /\ b <> p /\ (exists u, u <> p /\ R p u /\ Llift L u b))
      \/ (a <> p /\ b = p /\ (exists d, d <> p /\ R d p /\ Llift L a d))
      \/ (a <> p /\ b <> p /\ Llift L a b).

    Lemma Qkeep_refl : forall a, Qkeep a a.
    Proof.
      intro a. unfold Qkeep. destruct (classic (a = p)) as [-> | Ha].
      - left; split; reflexivity.
      - right; right; right. split; [exact Ha | split; [exact Ha | apply Llift_refl; exact Ha]].
    Qed.

    (** Collapse lemma: a strict down-element and a strict up-element of p are
        L-ordered  d ≤_L u  (since R d p, R p u ⟹ R d u). *)
    Lemma Qkeep_collapse :
      forall d u, d <> p -> u <> p -> R d p -> R p u -> Llift L d u.
    Proof.
      intros d u Hd Hu Hdp Hpu.
      apply Llift_extends; [ exact (poset_trans _ _ _ Hdp Hpu) | exact Hd | exact Hu ].
    Qed.

    Lemma Qkeep_refl' : forall a, Qkeep a a. Proof. exact Qkeep_refl. Qed.

    Lemma Qkeep_antisym : forall a b, Qkeep a b -> Qkeep b a -> a = b.
    Proof.
      intros a b Hab Hba. unfold Qkeep in Hab, Hba.
      destruct Hab as [[Ha Hb] | [[Ha [Hb [u [Hu [Hpu Hub]]]]] | [[Ha [Hb [d [Hd [Hdp Had]]]]] | [Ha [Hb Hl]]]]].
      - subst; reflexivity.
      - (* a=p, b<>p; Hba must be the (b<>p,a=p) i.e. C-branch with witness d *)
        destruct Hba as [[Hb1 Ha1] | [[Hb1 [Ha1 _]] | [[Hb1 [Ha1 [d [Hd [Hdp Hbd]]]]] | [Hb1 [Ha1 _]]]]];
          try (exfalso; congruence).
        exfalso.
        assert (Hud : Llift L u d) by exact (Llift_trans u b d Hub Hbd).
        assert (Hdu : Llift L d u) by exact (Qkeep_collapse d u Hd Hu Hdp Hpu).
        assert (Hdeq : d = u) by exact (Llift_antisym d u Hdu Hud).
        subst u. apply Hd. exact (poset_antisym _ _ Hdp Hpu).
      - (* a<>p, b=p; Hba must be B-branch with witness u *)
        destruct Hba as [[Hb1 Ha1] | [[Hb1 [Ha1 [u [Hu [Hpu Hua]]]]] | [[Hb1 [Ha1 _]] | [Hb1 [Ha1 _]]]]];
          try (exfalso; congruence).
        exfalso.
        assert (Hud : Llift L u d) by exact (Llift_trans u a d Hua Had).
        assert (Hdu : Llift L d u) by exact (Qkeep_collapse d u Hd Hu Hdp Hpu).
        assert (Hdeq : d = u) by exact (Llift_antisym d u Hdu Hud).
        subst u. apply Hd. exact (poset_antisym _ _ Hdp Hpu).
      - (* both <>p *)
        destruct Hba as [[Hb1 Ha1] | [[Hb1 [Ha1 _]] | [[Hb1 [Ha1 _]] | [Hb1 [Ha1 Hl']]]]];
          try (exfalso; congruence).
        exact (Llift_antisym a b Hl Hl').
    Qed.

    Lemma Qkeep_trans : forall a b c, Qkeep a b -> Qkeep b c -> Qkeep a c.
    Proof.
      intros a b c Hab Hbc.
      destruct (classic (a = p)) as [Ha | Ha];
      destruct (classic (b = p)) as [Hb | Hb];
      destruct (classic (c = p)) as [Hc | Hc];
      unfold Qkeep in *.
      - left; split; assumption.
      - (* a=p,b=p,c<>p *)
        destruct Hbc as [[E1 E2]|[[E1 [E2 Hex]]|[[E1 [E2 _]]|[E1 [E2 _]]]]]; try (exfalso; congruence).
        right; left; split; [assumption | split; assumption].
      - left; split; assumption.
      - (* a=p,b<>p,c<>p *)
        destruct Hab as [[E1 E2]|[[E1 [E2 [u [Hu [Hpu Hub]]]]]|[[E1 [E2 _]]|[E1 [E2 _]]]]]; try (exfalso; congruence).
        destruct Hbc as [[F1 F2]|[[F1 [F2 _]]|[[F1 [F2 _]]|[F1 [F2 Hbc']]]]]; try (exfalso; congruence).
        right; left; split; [assumption | split; [assumption |]].
        exists u; split; [assumption | split; [assumption | exact (Llift_trans u b c Hub Hbc')]].
      - (* a<>p,b=p,c=p *)
        destruct Hab as [[E1 E2]|[[E1 [E2 _]]|[[E1 [E2 [d [Hd [Hdp Had]]]]]|[E1 [E2 _]]]]]; try (exfalso; congruence).
        right; right; left; split; [assumption | split; [assumption |]].
        exists d; split; [assumption | split; assumption].
      - (* a<>p,b=p,c<>p *)
        destruct Hab as [[E1 E2]|[[E1 [E2 _]]|[[E1 [E2 [d [Hd [Hdp Had]]]]]|[E1 [E2 _]]]]]; try (exfalso; congruence).
        destruct Hbc as [[F1 F2]|[[F1 [F2 [u [Hu [Hpu Hub]]]]]|[[F1 [F2 _]]|[F1 [F2 _]]]]]; try (exfalso; congruence).
        right; right; right; split; [assumption | split; [assumption |]].
        apply (Llift_trans a d c Had).
        exact (Llift_trans d u c (Qkeep_collapse d u Hd Hu Hdp Hpu) Hub).
      - (* a<>p,b<>p,c=p *)
        destruct Hab as [[E1 E2]|[[E1 [E2 _]]|[[E1 [E2 _]]|[E1 [E2 Hab']]]]]; try (exfalso; congruence).
        destruct Hbc as [[F1 F2]|[[F1 [F2 _]]|[[F1 [F2 [d [Hd [Hdp Hbd]]]]]|[F1 [F2 _]]]]]; try (exfalso; congruence).
        right; right; left; split; [assumption | split; [assumption |]].
        exists d; split; [assumption | split; [assumption | exact (Llift_trans a b d Hab' Hbd)]].
      - (* a<>p,b<>p,c<>p *)
        destruct Hab as [[E1 E2]|[[E1 [E2 _]]|[[E1 [E2 _]]|[E1 [E2 Hab']]]]]; try (exfalso; congruence).
        destruct Hbc as [[F1 F2]|[[F1 [F2 _]]|[[F1 [F2 _]]|[F1 [F2 Hbc']]]]]; try (exfalso; congruence).
        right; right; right; split; [assumption | split; [assumption | exact (Llift_trans a b c Hab' Hbc')]].
    Qed.

    #[local] Instance Qkeep_poset : IsPoset B Qkeep :=
      {| poset_refl := Qkeep_refl; poset_antisym := Qkeep_antisym; poset_trans := Qkeep_trans |}.

    (** [Qkeep] contains R and [Llift L]. *)
    Lemma Qkeep_R : forall a b, R a b -> Qkeep a b.
    Proof.
      intros a b Hab. unfold Qkeep.
      destruct (classic (a = p)) as [-> | Ha]; destruct (classic (b = p)) as [-> | Hb].
      - left; split; reflexivity.
      - right; left. split; [reflexivity | split; [exact Hb |]].
        exists b; split; [exact Hb | split; [exact Hab | apply Llift_refl; exact Hb]].
      - right; right; left. split; [exact Ha | split; [reflexivity |]].
        exists a; split; [exact Ha | split; [exact Hab | apply Llift_refl; exact Ha]].
      - right; right; right. split; [exact Ha | split; [exact Hb | apply Llift_extends; assumption]].
    Qed.

    Lemma Qkeep_Llift : forall a b, a <> p -> b <> p -> Llift L a b -> Qkeep a b.
    Proof. intros a b Ha Hb Hl. right; right; right. repeat split; assumption. Qed.

    (** [lift_keep] exists: a linear extension of R that agrees with [Llift L]
        on all non-p pairs. *)
    Lemma lift_keep_exists :
      exists M : B -> B -> Prop,
        IsLinearExtension R M /\
        (forall a b, a <> p -> b <> p -> (M a b <-> Llift L a b)).
    Proof.
      destruct (szpilrajn_theorem B Qkeep) as [M [HMpos [HMtot HMext]]].
      assert (HMlin : IsLinearExtension R M).
      { constructor.
        - constructor; [ exact HMpos | exact HMtot ].
        - intros a b Hab. apply HMext. apply Qkeep_R. exact Hab. }
      exists M. split; [ exact HMlin |].
      intros a b Ha Hb. split.
      - intro HMab.
        destruct (Llift_total a b Ha Hb) as [Hl | Hl]; [ exact Hl |].
        (* if Llift b a then M b a; with M a b and antisym, a=b, so Llift a b by refl *)
        assert (HMba : M b a) by (apply HMext; apply Qkeep_Llift; assumption).
        assert (Hab_eq : a = b) by exact (poset_antisym (R := M) _ _ HMab HMba).
        subst b. apply Llift_refl; exact Ha.
      - intro Hl. apply HMext. apply Qkeep_Llift; assumption.
    Qed.

  End WithL.

  (** ---- Assembly: dim R ≤ 1 + dim(X − p) ---- *)

  (** Adding one element increases cardinality by at most 1. *)
  Lemma card_add_le :
    forall (U : Type) (T : Ensemble U) (x : U) (n : nat),
      cardinal U T n -> exists m, cardinal U (Add U T x) m /\ m <= S n.
  Proof.
    intros U T x n Hn. destruct (classic (In U T x)) as [Hin | Hnin].
    - exists n. split; [| lia].
      replace (Add U T x) with T; [ exact Hn |].
      apply Extensionality_Ensembles. split; intros y Hy.
      + left; exact Hy.
      + destruct Hy as [y Hy | y Hy]; [ exact Hy | destruct Hy; exact Hin ].
    - exists (S n). split; [ apply card_add; assumption | lia ].
  Qed.

  (** Choice function: a fixed [lift_keep] for each linear extension. *)
  Definition keepf (L : Sub -> Sub -> Prop) : B -> B -> Prop :=
    match excluded_middle_informative (IsLinearExtension Qsub L) with
    | left HL => proj1_sig (constructive_indefinite_description _ (lift_keep_exists L HL))
    | right _ => (fun _ _ => True)
    end.

  Lemma keepf_spec :
    forall L, IsLinearExtension Qsub L ->
      IsLinearExtension R (keepf L) /\
      (forall a b, a <> p -> b <> p -> (keepf L a b <-> Llift L a b)).
  Proof.
    intros L HL. unfold keepf.
    destruct (excluded_middle_informative (IsLinearExtension Qsub L)) as [HL' | Hno];
      [| exfalso; exact (Hno HL)].
    exact (proj2_sig (constructive_indefinite_description _ (lift_keep_exists L HL'))).
  Qed.

  Theorem one_point_removal :
    forall d d' : nat,
      1 <= d' ->
      PosetDimension R d ->
      @PosetDimension Sub Qsub d' ->
      d <= d' + 1.
  Proof.
    intros d d' Hd1 HdB HdSub.
    pose proof (dimension_is_realizer HdSub) as HrQ.
    pose proof (dimension_cardinality HdSub) as HrQcard.
    set (rQ := dimension_realizer HdSub) in *.
    (* rQ nonempty: cardinal rQ d' with d' = S (d'-1) *)
    assert (Hd'eq : d' = S (d' - 1)) by lia.
    rewrite Hd'eq in HrQcard.
    destruct (cardinal_invert _ rQ _ HrQcard) as [A' [Ld [HrQ_eq [HLd_nin HA'card]]]].
    assert (HLd_in : In _ rQ Ld) by (rewrite HrQ_eq; apply Add_intro2).
    pose proof (realizer_linear HrQ Ld HLd_in) as HLd_lin.
    (* the assembled realizer of R *)
    set (rB := Add _ (Add _ (Im _ _ A' keepf) (lift_low Ld)) (lift_high Ld)).
    (* membership helpers *)
    assert (Hlow_in : In _ rB (lift_low Ld)) by (left; apply Add_intro2).
    assert (Hhigh_in : In _ rB (lift_high Ld)) by (apply Add_intro2).
    assert (Hkeep_in : forall L, In _ A' L -> In _ rB (keepf L)).
    { intros L HL'. left; left. exists L; [ exact HL' | reflexivity ]. }
    (* every member of A' is a linear extension of Qsub *)
    assert (HA'_lin : forall L, In _ A' L -> IsLinearExtension Qsub L).
    { intros L HL'. apply (realizer_linear HrQ). rewrite HrQ_eq. left; exact HL'. }
    (* IsRealizer R rB *)
    assert (HrB_real : IsRealizer R rB).
    { constructor.
      - (* every member is a linear extension of R *)
        intros M HM. apply Add_inv in HM. destruct HM as [HM | HMeq2].
        + apply Add_inv in HM. destruct HM as [HMim | HMeq1].
          * destruct HMim as [L HL' M0 HMeq]. subst M0.
            exact (proj1 (keepf_spec L (HA'_lin L HL'))).
          * subst M. exact (lift_low_is_linext Ld HLd_lin).
        + subst M. exact (lift_high_is_linext Ld HLd_lin).
      - intros a b. split.
        + (* R a b -> every member holds *)
          intros Hab M HM. apply Add_inv in HM. destruct HM as [HM | HMeq2].
          * apply Add_inv in HM. destruct HM as [HMim | HMeq1].
            -- destruct HMim as [L HL' M0 HMeq]. subst M0.
               exact (linear_extends (proj1 (keepf_spec L (HA'_lin L HL'))) _ _ Hab).
            -- subst M. exact (lift_low_extends Ld HLd_lin a b Hab).
          * subst M. exact (lift_high_extends Ld HLd_lin a b Hab).
        + (* coverage: all members hold -> R a b *)
          intro Hall. apply NNPP. intro Hnab.
          destruct (classic (a = p)) as [-> | Ha].
          * (* a = p, b <> p (else R p p) *)
            assert (Hb : b <> p) by (intro Hbp; subst b; apply Hnab; apply (poset_refl (R := R))).
            assert (Hnpb : ~ R p b) by exact Hnab.
            exact (lift_high_rev_pb Ld b Hb Hnpb (Hall _ Hhigh_in)).
          * destruct (classic (b = p)) as [-> | Hb].
            -- assert (Hnap : ~ R a p) by exact Hnab.
               exact (lift_low_rev_ap Ld a Ha Hnap (Hall _ Hlow_in)).
            -- (* a,b <> p: use rQ realizer to find a reversing L *)
               assert (HnQ : ~ (forall L, In _ rQ L ->
                                  L (exist _ a Ha) (exist _ b Hb))).
               { intro Hq. apply Hnab.
                 exact (proj2 (realizer_intersection HrQ (exist _ a Ha) (exist _ b Hb)) Hq). }
               apply not_all_ex_not in HnQ. destruct HnQ as [L HnL].
               apply imply_to_and in HnL. destruct HnL as [HL_in HnLab].
               assert (HnLlift : ~ Llift L a b).
               { intros [ha [hb HLl]]. apply HnLab.
                 rewrite (proof_irrelevance _ Ha ha), (proof_irrelevance _ Hb hb). exact HLl. }
               destruct (classic (L = Ld)) as [-> | HLneq].
               ++ destruct (lift_low_high_rev_SS Ld HLd_lin a b Ha Hb HnLlift) as [Hlo | Hhi].
                  ** exact (Hlo (Hall _ Hlow_in)).
                  ** exact (Hhi (Hall _ Hhigh_in)).
               ++ (* L in A' (= rQ minus Ld); use keepf L *)
                  assert (HL_A' : In _ A' L).
                  { rewrite HrQ_eq in HL_in. destruct HL_in as [L HL' | L HLs];
                      [ exact HL' | destruct HLs; exfalso; apply HLneq; reflexivity ]. }
                  pose proof (proj2 (keepf_spec L (HA'_lin L HL_A')) a b Ha Hb) as Hiff.
                  apply HnLlift. apply Hiff. exact (Hall _ (Hkeep_in L HL_A')). }
    (* cardinality of rB ≤ d' - 1 + 2 = d' + 1 *)
    destruct (cardinal_Im_le_local _ _ A' keepf _ HA'card)
      as [k [HImcard Hk_le]].
    destruct (card_add_le _ (Im _ _ A' keepf) (lift_low Ld) _ HImcard)
      as [k1 [Hk1card Hk1_le]].
    destruct (card_add_le _ (Add _ (Im _ _ A' keepf) (lift_low Ld)) (lift_high Ld) _ Hk1card)
      as [k2 [Hk2card Hk2_le]].
    assert (Hk2_bound : k2 <= d' + 1) by lia.
    apply (Nat.le_trans d k2 (d' + 1)); [| exact Hk2_bound].
    exact (dimension_is_minimum HdB rB k2 HrB_real Hk2card).
  Qed.

End OnePointRemoval.

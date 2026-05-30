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

From Stdlib Require Import Ensembles Finite_sets Arith Lia.
From Stdlib Require Import Classical ClassicalDescription ProofIrrelevance.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.

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

  End WithL.
End OnePointRemoval.

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Third sub-block of micro-case (xvi): 4th-edge cases (m) = (r,s),
    (n) = (s,r) — disjoint 2-chain (HnCC); plus antisymmetry cases
    (o) = (q,p), (p) = (t,q), (q) = (t,p); plus the final exfalso
    using all 17 accumulated negations. *)
Lemma n5_dispatcher_microcase_xvi_subcase_c :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 q t)
    (HRpt : R2 p t)
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
                (x = d /\ y = e)))))
    (Hfourth :
       exists a b : B,
         a <> b /\ R2 a b /\
         ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
         ~ (a = p /\ b = t))
    (HnRrp : ~ R2 r p) (HnRsp : ~ R2 s p)
    (HnRtr_fourth : ~ R2 t r) (HnRts : ~ R2 t s)
    (HnRqr : ~ R2 q r) (HnRqs : ~ R2 q s)
    (HnRrq : ~ R2 r q) (HnRsq : ~ R2 s q)
    (HnRrt : ~ R2 r t) (HnRst : ~ R2 s t)
    (HnRpr : ~ R2 p r) (HnRps : ~ R2 p s),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy HRpt
         HnCC Hfourth
         HnRrp HnRsp HnRtr_fourth HnRts HnRqr HnRqs
         HnRrq HnRsq HnRrt HnRst HnRpr HnRps.
    (* (m) fourth edge = (r, s): 3-chain p<q<t + disjoint 2-chain r<s (HnCC). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRrs |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; exact Hurs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urs. }
    (* (n) fourth edge = (s, r): 3-chain p<q<t + disjoint 2-chain s<r (HnCC). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr |].
        intros [Htp _]; apply Hps_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRsr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; exact Husr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_usr. }
    (* (o) fourth edge = (q, p) — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (p) fourth edge = (t, q) — antisymmetry contradiction. *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { exfalso. apply Hqt_neq.
      exact (HR2.(poset_antisym) q t HRxy HRtq). }
    (* (q) fourth edge = (t, p) — antisymmetry contradiction. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { exfalso. apply Hpt_neq.
      exact (HR2.(poset_antisym) p t HRpt HRtp). }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_qt Hnot_ab_pt]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_qt; split; reflexivity
        | apply Hnot_ab_pt; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRps; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRtr_fourth; exact HRab
        | apply HnRts; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRst; exact HRab
        | apply HnRsr; exact HRab ].
Qed.

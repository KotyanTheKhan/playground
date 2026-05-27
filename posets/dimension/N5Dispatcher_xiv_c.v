From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Third sub-block of micro-case (xiv): 4th-edge cases (m) = (s,t),
    (n) = (t,s) — disjoint 2-chain (HnCC); plus antisymmetry cases
    (o) = (q,p), (p) = (r,q), (q) = (r,p); plus the final exfalso
    using all 17 accumulated negations. *)
Lemma n5_dispatcher_microcase_xiv_subcase_c :
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
    (HRxy : R2 q r)
    (HRpr : R2 p r)
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                (x = d /\ y = e)))))
    (Hfourth :
       exists a b : B,
         a <> b /\ R2 a b /\
         ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
         ~ (a = p /\ b = r))
    (HnRsp : ~ R2 s p) (HnRtp : ~ R2 t p)
    (HnRrs_fourth : ~ R2 r s) (HnRrt : ~ R2 r t)
    (HnRqs : ~ R2 q s) (HnRqt : ~ R2 q t)
    (HnRsq : ~ R2 s q) (HnRtq : ~ R2 t q)
    (HnRsr : ~ R2 s r) (HnRtr : ~ R2 t r)
    (HnRps : ~ R2 p s) (HnRpt : ~ R2 p t),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy HRpr
         HnCC Hfourth
         HnRsp HnRtp HnRrs_fourth HnRrt HnRqs HnRqt
         HnRsq HnRtq HnRsr HnRtr HnRps HnRpt.
    (* (m) fourth edge = (s, t): 3-chain p<q<r + disjoint 2-chain s<t (HnCC). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRst |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_ust. }
    (* (n) fourth edge = (t, s): 3-chain p<q<r + disjoint 2-chain t<s (HnCC). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRts |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; exact Huts |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* (o) fourth edge = (q, p) — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (p) fourth edge = (r, q) — antisymmetry contradiction. *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { exfalso. apply Hqr_neq.
      exact (HR2.(poset_antisym) q r HRxy HRrq). }
    (* (q) fourth edge = (r, p) — antisymmetry contradiction. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { exfalso. apply Hpr_neq.
      exact (HR2.(poset_antisym) p r HRpr HRrp). }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_qr Hnot_ab_pr]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_qr; split; reflexivity
        | apply Hnot_ab_pr; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRst; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRts; exact HRab ].
Qed.

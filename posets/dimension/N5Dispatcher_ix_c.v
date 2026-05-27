From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Third sub-block of micro-case (ix): 3rd-edge cases (m) = (r,q),
    (n) = (t,q), (o) = (r,s), (p) = (t,s), (q) = (r,t), (s) = (t,r),
    plus the final exfalso using all 18 accumulated negations. *)
Lemma n5_dispatcher_microcase_ix_subcase_c :
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
    (HRxy : R2 p s)
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (Hthird :
       exists a b : B,
         a <> b /\ R2 a b /\
         ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s))
    (HnRqp : ~ R2 q p) (HnRsp : ~ R2 s p)
    (HnRqs_third : ~ R2 q s) (HnRsq_third : ~ R2 s q)
    (HnRpr_third : ~ R2 p r) (HnRpt_third : ~ R2 p t)
    (HnRrp_third : ~ R2 r p) (HnRtp_third : ~ R2 t p)
    (HnRqr_third : ~ R2 q r) (HnRqt_third : ~ R2 q t)
    (HnRsr_third : ~ R2 s r) (HnRst_third : ~ R2 s t),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy
         HnN HnVc Hthird
         HnRqp HnRsp HnRqs_third HnRsq_third HnRpr_third HnRpt_third
         HnRrp_third HnRtp_third HnRqr_third HnRqt_third HnRsr_third HnRst_third.
    (* (m) third edge = (r, q): N-shape (a<b, c<b, c<d) with a=r, b=q,
       c=p, d=s. iso t. (HnN) *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists r, q, p, s, t.
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urq. }
    (* (n) third edge = (t, q): N-shape with a=t, c=p, b=q, d=s. iso r. *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists t, q, p, s, r.
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRtq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_utq. }
    (* (o) third edge = (r, s): N-shape with a=r, b=s, c=p, d=q. iso t. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists r, s, p, q, t.
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRrs_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    (* (p) third edge = (t, s): N-shape with a=t, b=s, c=p, d=q. iso r. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists t, s, p, q, r.
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRts_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (q) third edge = (r, t): V at p + disjoint chain r<t (HnVc) with
       a=p, b=q, c=s, d=r, e=t. *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urt. }
    (* (s) third edge = (t, r): V at p + disjoint chain t<r (HnVc) with
       a=p, b=q, c=s, d=t, e=r. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRtr_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVc.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_utr. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_ps]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_ps; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRrs_third; exact HRab
        | apply HnRts_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRtr_third; exact HRab ].
Qed.

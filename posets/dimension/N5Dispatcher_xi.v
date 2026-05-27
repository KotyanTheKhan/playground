From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (xi) of the second-edge cascade inside the residual handler:
    second edge is [(r, q)] — inv-V at [q] with bottoms [p] and [r], plus
    isolated [s], [t].  If no third strict edge exists, this contradicts
    [HninvV] (the inv-V+2isolated shape).  Otherwise the third-edge
    expansion peels off each well-defined labeling and routes to the
    matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xi :
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
    (HRxy : R2 r q)
    (Hnot_pq : ~ (r = p /\ q = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HninvV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c))))
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
    (HnClawDn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a d /\ R2 b d /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HniVcol :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d a /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = c)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q)))
    as [Hthird | Hno_third].
  - destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { exfalso. apply Hqr_neq.
      exact (HR2.(poset_antisym) q r HRqr HRxy). }
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnChain3.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpr_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_upr. }
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = p)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp_third |].
        intros [_ Hpq]; apply Hpq_neq; exact Hpq.
      - exfalso. apply HnChain3.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrp_third |].
        split; [exact HRpq |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_urp. }
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists r, q, p, s, t.
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps_third |].
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
        split; [exact Hnot_urq |]. exact Hnot_ups. }
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists r, q, p, t, s.
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_upt. }
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HniVcol.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsp_third |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HniVcol.
        exists p, r, q, t, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs_third).
      assert (HRrs_via : R2 r s) by exact (HR2.(poset_trans) r q s HRxy HRqs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists s, q, p, r, t.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqs_third |].
        split; [exact HRps_via |].
        split; [exact HRrs_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      assert (HRrt_via : R2 r t) by exact (HR2.(poset_trans) r q t HRxy HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists t, q, p, r, s.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt_third |].
        split; [exact HRpt_via |].
        split; [exact HRrt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnClawDn.
        exists p, r, s, q, t.
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_usq. }
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnClawDn.
        exists p, r, t, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_utq. }
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
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
        split; [exact HRrs_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
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
      - exfalso. apply HnN.
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
        split; [exact HRrt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s r q HRsr_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = r) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HniVcol.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsr_third |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_usr |]. exact Hnot_usq. }
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t r q HRtr_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = r) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HniVcol.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtr_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utr |]. exact Hnot_utq. }
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_ust. }
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HninvVc.
        exists p, r, q, t, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_rq]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRsp_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRrs_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRtr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRts_third; exact HRab ].
  - exfalso. apply HninvV.
    exists p, r, q, s, t.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hst_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
      [right; exact Hurq |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_urq.
Qed.

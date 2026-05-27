From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (ix) of the second-edge cascade inside the residual handler:
    second edge is [(p, s)] — V at [p] with leaves [q] and [s], plus
    isolated [r], [t].  If no third strict edge exists, this contradicts
    [HnV] (the V+2isolated shape).  Otherwise the third-edge expansion
    peels off each well-defined labeling and routes to the matching
    upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_ix :
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
    (Hnot_pq : ~ (p = p /\ s = q))
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
    (HnV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c))))
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
    (HnClawUp :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
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
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnVpb :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d a /\ R2 d b /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = b) \/ (x = d /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnV HnN HnClawUp HnVc HnPd HnVpb.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (s, p) — antisymmetry with HRxy : R2 p s. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { exfalso. apply Hps_neq.
      exact (HR2.(poset_antisym) p s HRxy HRsp). }
    (* (c) third edge = (q, s): 3-chain p<q<s + iso r, t (HnChain3). *)
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = q /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnChain3.
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
        split; [exact HRqs_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; exact Huqs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* (d) third edge = (s, q): 3-chain p<s<q + iso r, t (HnChain3). *)
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnChain3.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRsq_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_usq. }
    (* (e) third edge = (p, r): 3-claw-up at p with leaves q, s, r + iso t
       (HnClawUp). *)
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
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
      - exfalso. apply HnClawUp.
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
        split; [exact HRpr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_upr. }
    (* (f) third edge = (p, t): 3-claw-up, iso r. *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
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
      - exfalso. apply HnClawUp.
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
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_upt. }
    (* (g) third edge = (r, p): V with pendant below the common bottom
       (HnVpb) with a=p, b=q, c=s, d=r. Edges a<b, a<c, d<a, d<b, d<c.
       iso t. *)
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      assert (HRrs_via : R2 r s) by exact (HR2.(poset_trans) r p s HRrp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVpb.
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
        split; [exact HRrp_third |].
        split; [exact HRrq_via |].
        split; [exact HRrs_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (h) third edge = (t, p): V with pendant below (HnVpb), iso r. *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      assert (HRts_via : R2 t s) by exact (HR2.(poset_trans) t p s HRtp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVpb.
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
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        split; [exact HRts_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (i) third edge = (q, r): pendant 3-chain p<q<r + pendant p<s
       (HnPd) with a=p, b=q, c=r, d=s. iso t. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRqr_third |].
        split; [exact HRxy |].
        split; [exact HRpr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (j) third edge = (q, t): pendant 3-chain p<q<t + pendant p<s
       (HnPd), iso r. *)
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRqt_third |].
        split; [exact HRxy |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (k) third edge = (s, r): pendant 3-chain p<s<r + pendant p<q
       (HnPd) with a=p, b=s, c=r, d=q. iso t. *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p s r HRxy HRsr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = s /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
        exists p, s, r, q, t.
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRxy |].
        split; [exact HRsr_third |].
        split; [exact HRpq |].
        split; [exact HRpr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_usr |]. exact Hnot_upr. }
    (* (l) third edge = (s, t): pendant 3-chain p<s<t + pendant p<q
       (HnPd), iso r. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p s t HRxy HRst_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = s /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
        exists p, s, t, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        split; [exact HRpq |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; left; exact Hust |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_ust |]. exact Hnot_upt. }
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
  - exfalso. apply HnV.
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
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
      [right; exact Hups |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_ups.
Qed.

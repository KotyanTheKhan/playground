From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (xii) of the second-edge cascade inside the residual handler:
    second edge is [(s, q)] — inv-V at [q] with bottoms [p] and [s], plus
    isolated [r], [t].  If no third strict edge exists, this contradicts
    [HninvV] (the inv-V+2isolated shape).  Otherwise the third-edge
    expansion peels off each well-defined labeling and routes to the
    matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xii :
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
    (HRxy : R2 s q)
    (Hnot_pq : ~ (s = p /\ q = q))
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
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (q, s) — antisymmetry with HRxy : R2 s q. *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { exfalso. apply Hqs_neq.
      exact (HR2.(poset_antisym) q s HRqs HRxy). }
    (* (c) third edge = (p, s): 3-chain p<s<q + iso r, t (HnChain3). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
        split; [exact HRps_third |].
        split; [exact HRxy |].
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
        split; [exact Hnot_usq |]. exact Hnot_ups. }
    (* (d) third edge = (s, p): 3-chain s<p<q + iso r, t (HnChain3). *)
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = p)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact HRsp_third |].
        intros [_ Hpq]; apply Hpq_neq; exact Hpq.
      - exfalso. apply HnChain3.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRsp_third |].
        split; [exact HRpq |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_usp. }
    (* (e) third edge = (p, r): N-shape (a→b, c→b, c→d with
       a=s, b=q, c=p, d=r); iso t (HnN). *)
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
      - exfalso. apply HnN.
        exists s, q, p, r, t.
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_upr. }
    (* (f) third edge = (p, t): N-shape, iso r (HnN). *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
        exists s, q, p, t, r.
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_upt. }
    (* (g) third edge = (r, p): inv-V chain on one bottom (HniVcol)
       with a=p, c=q, b=s, d=r. Edges a<c, b<c, d<a, d<c. iso t. *)
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HniVcol.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrp_third |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (h) third edge = (t, p): inv-V chain on one bottom (HniVcol)
       with a=p, c=q, b=s, d=t. iso r. *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HniVcol.
        exists p, s, q, t, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
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
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (i) third edge = (q, r): Y-down at r (HnYdn) with a=r, b=q,
       c=p, d=s. R2 c b, R2 d b, R2 b a, R2 c a, R2 d a. iso t. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr_third).
      assert (HRsr_via : R2 s r) by exact (HR2.(poset_trans) s q r HRxy HRqr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists r, q, p, s, t.
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqr_third |].
        split; [exact HRpr_via |].
        split; [exact HRsr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (j) third edge = (q, t): Y-down at t (HnYdn), iso r. *)
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      assert (HRst_via : R2 s t) by exact (HR2.(poset_trans) s q t HRxy HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = t)))
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
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt_third |].
        split; [exact HRpt_via |].
        split; [exact HRst_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (k) third edge = (r, q): 3-claw-down (HnClawDn) with
       a=p, b=s, c=r, d=q (R2 a d, R2 b d, R2 c d). iso t. *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
      - exfalso. apply HnClawDn.
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
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_urq. }
    (* (l) third edge = (t, q): 3-claw-down, iso r. *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
      - exfalso. apply HnClawDn.
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
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (m) third edge = (s, r): N-shape (a→b, c→b, c→d) with
       a=p, b=q, c=s, d=r. iso t. *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnN.
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
        split; [exact HRsr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (n) third edge = (s, t): N-shape, iso r. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
      - exfalso. apply HnN.
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
        split; [exact HRst_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (o) third edge = (r, s): inv-V chain (HniVcol) with
       a=s, c=q, b=p, d=r (a<c, b<c, d<a, d<c). iso t. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r s q HRrs_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = s) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HniVcol.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrs_third |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urs |]. exact Hnot_urq. }
    (* (p) third edge = (t, s): inv-V chain (HniVcol), iso r. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t s q HRts_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = s) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HniVcol.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRts_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uts |]. exact Hnot_utq. }
    (* (q) third edge = (r, t): inv-V + disjoint chain (HninvVc) with
       a=p, b=s, c=q, d=r, e=t (R2 a c, R2 b c, R2 d e). *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
      - exfalso. apply HninvVc.
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
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_urt. }
    (* (r) third edge = (t, r): inv-V + disjoint chain (HninvVc) with
       a=p, b=s, c=q, d=t, e=r. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
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
      - exfalso. apply HninvVc.
        exists p, s, q, t, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
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
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_utr. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_sq]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_sq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRsp_third; exact HRab
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
  - exfalso. apply HninvV.
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
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
      [right; exact Husq |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_usq.
Qed.

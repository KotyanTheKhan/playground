From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (viii) of the second-edge cascade inside the residual handler:
    second edge is [(p, r)] — V at [p] with leaves [q] and [r], plus
    isolated [s], [t].  If no third strict edge exists, this contradicts
    [HnV] (the V+2isolated shape).  Otherwise the third-edge expansion
    peels off each well-defined labeling and routes to the matching
    upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_viii :
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
    (HRxy : R2 p r)
    (Hnot_pq : ~ (p = p /\ r = q))
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
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
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
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
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
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
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
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
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
         HnChain3 HnV HnN HnClawUp HnCC HnVc HnC4 HnPd HnYup HnYdn HnTopP HnVpb.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (r, p) — antisymmetry with HRxy : R2 p r. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { exfalso. apply Hpr_neq.
      exact (HR2.(poset_antisym) p r HRxy HRrp). }
    (* (c) third edge = (q, r): 3-chain p<q<r + iso s, t (HnChain3).
       If a 4th edge exists, peel off all 14 well-defined labelings and
       route to upstream per-class shapes; the residual lemma is only
       reached via reduced 5th-edge witnesses inside each sub-branch. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = q /\ b = r)))
        as [Hfourth | Hno_fourth].
      - (* (c.i) fourth edge = (s, p): 4-chain s<p<q<r + iso t (HnC4). *)
        destruct (classic (R2 s p)) as [HRsp | HnRsp].
        { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
          assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s q r HRsq_new HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = p) /\
                    ~ (a = s /\ b = q) /\ ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, p.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
            split; [exact HRsp |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnC4.
            exists s, p, q, r, t.
            split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
            split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact Hst_neq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrt_neq |].
            split; [exact HRsp |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRsq_new |].
            split; [exact HRsr_new |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
              [left; exact Husp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
              [right; right; right; left; exact Husq |].
            destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
              [right; right; right; right; left; exact Husr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_usp |].
            split; [exact Hnot_usq |]. exact Hnot_usr. }
        (* (c.ii) fourth edge = (t, p): 4-chain t<p<q<r + iso s (HnC4). *)
        destruct (classic (R2 t p)) as [HRtp | HnRtp].
        { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
          assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t q r HRtq_new HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, p.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
            split; [exact HRtp |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnC4.
            exists t, p, q, r, s.
            split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
            split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrs_neq |].
            split; [exact HRtp |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRtq_new |].
            split; [exact HRtr_new |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; right; right; left; exact Hutr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_utr. }
        (* (c.iii) fourth edge = (r, s): 4-chain p<q<r<s + iso t (HnC4). *)
        destruct (classic (R2 r s)) as [HRrs_fourth | HnRrs_fourth].
        { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p r s HRxy HRrs_fourth).
          assert (HRqs_new : R2 q s) by exact (HR2.(poset_trans) q r s HRqr_third HRrs_fourth).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = r /\ b = s) /\
                    ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hrs_neq |].
            split; [exact HRrs_fourth |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnC4.
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
            split; [exact HRqr_third |].
            split; [exact HRrs_fourth |].
            split; [exact HRxy |].
            split; [exact HRps_new |].
            split; [exact HRqs_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
              [right; right; left; exact Hurs |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; right; right; left; exact Hups |].
            destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
              [right; right; right; right; right; exact Huqs |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_urs |].
            split; [exact Hnot_ups |]. exact Hnot_uqs. }
        (* (c.iv) fourth edge = (r, t): 4-chain p<q<r<t + iso s (HnC4). *)
        destruct (classic (R2 r t)) as [HRrt | HnRrt].
        { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p r t HRxy HRrt).
          assert (HRqt_new : R2 q t) by exact (HR2.(poset_trans) q r t HRqr_third HRrt).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = r /\ b = t) /\
                    ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hrt_neq |].
            split; [exact HRrt |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnC4.
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
            split; [exact HRqr_third |].
            split; [exact HRrt |].
            split; [exact HRxy |].
            split; [exact HRpt_new |].
            split; [exact HRqt_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
              [right; right; left; exact Hurt |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
              [right; right; right; right; left; exact Hupt |].
            destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
              [right; right; right; right; right; exact Huqt |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_urt |].
            split; [exact Hnot_upt |]. exact Hnot_uqt. }
        (* (c.v) fourth edge = (q, s): Y-up apex p, branch q->{r,s} (HnYup). *)
        destruct (classic (R2 q s)) as [HRqs | HnRqs].
        { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = q /\ b = s) /\
                    ~ (a = p /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, q, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hqs_neq |].
            split; [exact HRqs |].
            intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
          - exfalso. apply HnYup.
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
            split; [exact HRqr_third |].
            split; [exact HRqs |].
            split; [exact HRxy |].
            split; [exact HRps_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
              [right; right; left; exact Huqs |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; right; right; exact Hups |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_uqs |]. exact Hnot_ups. }
        (* (c.vi) fourth edge = (q, t): Y-up apex p, branch q->{r,t} (HnYup). *)
        destruct (classic (R2 q t)) as [HRqt | HnRqt].
        { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = q /\ b = t) /\
                    ~ (a = p /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, q, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hqt_neq |].
            split; [exact HRqt |].
            intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
          - exfalso. apply HnYup.
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
            split; [exact HRqr_third |].
            split; [exact HRqt |].
            split; [exact HRxy |].
            split; [exact HRpt_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
              [right; right; left; exact Huqt |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
              [right; right; right; right; exact Hupt |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_uqt |]. exact Hnot_upt. }
        (* (c.vii) fourth edge = (s, q): Y-down apex r, q parents p,s (HnYdn). *)
        destruct (classic (R2 s q)) as [HRsq | HnRsq].
        { assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s q r HRsq HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = q) /\
                    ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, q.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
            split; [exact HRsq |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnYdn.
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
            split; [exact HRpq |].
            split; [exact HRsq |].
            split; [exact HRqr_third |].
            split; [exact HRxy |].
            split; [exact HRsr_new |].
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
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_usq |]. exact Hnot_usr. }
        (* (c.viii) fourth edge = (t, q): Y-down apex r, q parents p,t (HnYdn). *)
        destruct (classic (R2 t q)) as [HRtq | HnRtq].
        { assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t q r HRtq HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = q) /\
                    ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, q.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
            split; [exact HRtq |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnYdn.
            exists r, q, p, t, s.
            split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
            split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
            split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
            split; [exact Hrs_neq |].
            split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
            split; [exact Hqs_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRtq |].
            split; [exact HRqr_third |].
            split; [exact HRxy |].
            split; [exact HRtr_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; left; exact Hutq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; right; right; exact Hutr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_utq |]. exact Hnot_utr. }
        (* (c.ix) fourth edge = (s, r): top pendant s<r (HnTopP). *)
        destruct (classic (R2 s r)) as [HRsr | HnRsr].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
            split; [exact HRsr |].
            intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
          - exfalso. apply HnTopP.
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
            split; [exact HRqr_third |].
            split; [exact HRsr |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
              [right; right; left; exact Husr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_usr. }
        (* (c.x) fourth edge = (t, r): top pendant t<r (HnTopP). *)
        destruct (classic (R2 t r)) as [HRtr | HnRtr].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
            split; [exact HRtr |].
            intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
          - exfalso. apply HnTopP.
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
            split; [exact HRqr_third |].
            split; [exact HRtr |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; left; exact Hutr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_utr. }
        (* (c.xi) fourth edge = (p, s): bottom pendant p<s (HnPd). *)
        destruct (classic (R2 p s)) as [HRps | HnRps].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = p /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, p, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hps_neq |].
            split; [exact HRps |].
            intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
          - exfalso. apply HnPd.
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
            split; [exact HRqr_third |].
            split; [exact HRps |].
            split; [exact HRxy |].
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
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_ups. }
        (* (c.xii) fourth edge = (p, t): bottom pendant p<t (HnPd). *)
        destruct (classic (R2 p t)) as [HRpt | HnRpt].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = p /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, p, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hpt_neq |].
            split; [exact HRpt |].
            intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
          - exfalso. apply HnPd.
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
            split; [exact HRqr_third |].
            split; [exact HRpt |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
              [right; right; left; exact Hupt |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_upt. }
        (* (c.xiii) fourth edge = (s, t): disjoint 2-chain s<t (HnCC). *)
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
            split; [exact HRqr_third |].
            split; [exact HRxy |].
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
        (* (c.xiv) fourth edge = (t, s): disjoint 2-chain t<s (HnCC). *)
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
            split; [exact HRqr_third |].
            split; [exact HRxy |].
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
        (* (c.xv) fourth edge = (r, q) — antisymmetry contradiction. *)
        destruct (classic (R2 r q)) as [HRrq | HnRrq].
        { exfalso. apply Hqr_neq.
          exact (HR2.(poset_antisym) q r HRqr_third HRrq). }
        (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
        exfalso.
        destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_pr Hnot_ab_qr]]]]]].
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
      - exfalso. apply HnChain3.
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
        split; [exact HRqr_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; exact Huqr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (d) third edge = (r, q): 3-chain p<r<q + iso s, t (HnChain3). *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
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
        split; [exact HRxy |].
        split; [exact HRrq_third |].
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
        split; [exact Hnot_upr |]. exact Hnot_urq. }
    (* (e) third edge = (p, s): 3-claw-up at p with leaves q, r, s + iso t
       (HnClawUp). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
      - exfalso. apply HnClawUp.
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
        split; [exact HRps_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_ups. }
    (* (f) third edge = (p, t): 3-claw-up, iso s. *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_upt. }
    (* (g) third edge = (s, p): V with pendant below the common bottom
       (HnVpb) with a=p, b=q, c=r, d=s. Edges a<b, a<c, d<a, d<b, d<c.
       iso t. *)
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      assert (HRsr_via : R2 s r) by exact (HR2.(poset_trans) s p r HRsp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnVpb.
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
        split; [exact HRsp_third |].
        split; [exact HRsq_via |].
        split; [exact HRsr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (h) third edge = (t, p): V with pendant below (HnVpb), iso s. *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      assert (HRtr_via : R2 t r) by exact (HR2.(poset_trans) t p r HRtp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVpb.
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
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        split; [exact HRtr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_utr. }
    (* (i) third edge = (q, s): pendant 3-chain p<q<s + pendant p<r
       (HnPd) with a=p, b=q, c=s, d=r. iso t. *)
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
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
        split; [exact HRps_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (j) third edge = (q, t): pendant 3-chain p<q<t + pendant p<r
       (HnPd), iso s. *)
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (k) third edge = (r, s): pendant 3-chain p<r<s + pendant p<q
       (HnPd) with a=p, b=r, c=s, d=q. iso t. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p r s HRxy HRrs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = r /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
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
        split; [exact HRxy |].
        split; [exact HRrs_third |].
        split; [exact HRpq |].
        split; [exact HRps_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_urs |]. exact Hnot_ups. }
    (* (l) third edge = (r, t): pendant 3-chain p<r<t + pendant p<q
       (HnPd), iso s. *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p r t HRxy HRrt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = r /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
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
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        split; [exact HRpq |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_urt |]. exact Hnot_upt. }
    (* (m) third edge = (s, q): N-shape (a<b, c<b, c<d) with a=s, b=q,
       c=p, d=r. iso t. (HnN) *)
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
      - exfalso. apply HnN.
        exists s, q, p, r, t.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRsq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
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
        split; [exact Hnot_upr |]. exact Hnot_usq. }
    (* (n) third edge = (t, q): N-shape with a=t, c=p, b=q, d=r. iso s. *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
      - exfalso. apply HnN.
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
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_utq. }
    (* (o) third edge = (s, r): N-shape with a=s, b=r, c=p, d=q. iso t. *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists s, r, p, q, t.
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRsr_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [left; exact Husr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (p) third edge = (t, r): N-shape with a=t, b=r, c=p, d=q. iso s. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists t, r, p, q, s.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRtr_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_utr. }
    (* (q) third edge = (s, t): V at p + disjoint chain s<t (HnVc) with
       a=p, b=q, c=r, d=s, e=t. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
      - exfalso. apply HnVc.
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
        split; [exact HRst_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_ust. }
    (* (r) third edge = (t, s): V at p + disjoint chain t<s (HnVc) with
       a=p, b=q, c=r, d=t, e=s. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
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
      - exfalso. apply HnVc.
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
        split; [exact HRts_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_pr]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_pr; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRrq_third; exact HRab
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
  - exfalso. apply HnV.
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
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
      [right; exact Hupr |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_upr.
Qed.

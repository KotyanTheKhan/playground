From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (xix) of the second-edge cascade inside the residual handler:
    second edge is [(t, p)] — by transitivity [R2 t q] holds, so the carrier
    admits the 3-chain [t < p < q] plus isolated [r], [s].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xix :
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
    (HRxy : R2 t p)
    (Hnot_pq : ~ (t = p /\ p = q))
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
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\
            R2 a c /\ R2 a d /\ R2 b d /\
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
            R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = a /\ y = d)))))
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
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn.
  assert (HRtq : R2 t q) by exact (HR2.(poset_trans) t p q HRxy HRpq).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
            ~ (a = t /\ b = q)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) fourth edge = (p, t) — antisymmetry with HRxy : R2 t p. *)
    destruct (classic (R2 p t)) as [HRpr_fourth | HnRpr_fourth].
    { exfalso. apply Hpt_neq.
      exact (HR2.(poset_antisym) p t HRpr_fourth HRxy). }
    (* (c) fourth edge = (q, t) — antisymmetry with HRtq : R2 t q. *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { exfalso. apply Hqt_neq.
      exact (HR2.(poset_antisym) q t HRqt HRtq). }
    (* (d) fourth edge = (s, t): 4-chain s<t<p<q + iso r (HnC4). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { assert (HRsp_new : R2 s p) by exact (HR2.(poset_trans) s t p HRst HRxy).
      assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact HRst |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
        exists s, t, p, q, r.
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRst |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsp_new |].
        split; [exact HRsq_new |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* (e) fourth edge = (r, t): 4-chain r<t<p<q + iso s (HnC4). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { assert (HRtp_new : R2 r p) by exact (HR2.(poset_trans) r t p HRrt HRxy).
      assert (HRtq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRtp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact HRrt |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists r, t, p, q, s.
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRrt |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtp_new |].
        split; [exact HRtq_new |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (f) fourth edge = (q, s): 4-chain t<p<q<s + iso r (HnC4). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      assert (HRrs_new : R2 t s) by exact (HR2.(poset_trans) t p s HRxy HRps_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRtq |].
        split; [exact HRrs_new |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (g) fourth edge = (q, r): 4-chain t<p<q<r + iso s (HnC4). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpt_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      assert (HRrt_new : R2 t r) by exact (HR2.(poset_trans) t p r HRxy HRpt_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists t, p, q, r, s.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRtq |].
        split; [exact HRrt_new |].
        split; [exact HRpt_new |].
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
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_utr. }
    (* (h) fourth edge = (t, s): 3-chain t<p<q + pendant t<s + iso r
       (HnPd) with a=t, b=p, c=q, d=s. *)
    destruct (classic (R2 t s)) as [HRrs_fourth | HnRrs_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRrs_fourth |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnPd.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrs_fourth |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (i) fourth edge = (t, r): 3-chain t<p<q + pendant t<r + iso s
       (HnPd) with a=t, b=p, c=q, d=r. *)
    destruct (classic (R2 t r)) as [HRrt_fourth | HnRrt_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRrt_fourth |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnPd.
        exists t, p, q, r, s.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrt_fourth |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_utr. }
    (* (j) fourth edge = (p, s): Y-up apex t, branch p->{q,s} (HnYup)
       with a=t, b=p, c=q, d=s. *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { assert (HRts_via : R2 t s) by exact (HR2.(poset_trans) t p s HRxy HRps).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnYup.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRtq |].
        split; [exact HRts_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; exact Huts |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (k) fourth edge = (p, r): Y-up apex t, branch p->{q,r} (HnYup). *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { assert (HRtr_via : R2 t r) by exact (HR2.(poset_trans) t p r HRxy HRpr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnYup.
        exists t, p, q, r, s.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRtq |].
        split; [exact HRtr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; right; exact Hutr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_upr |]. exact Hnot_utr. }
    (* (l) fourth edge = (s, p): Y-down apex q, p has parents t,s
       (HnYdn) with a=q, b=p, c=t, d=s. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact HRsp |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnYdn.
        exists q, p, t, s, r.
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* (m) fourth edge = (r, p): Y-down apex q, p has parents t,r
       (HnYdn) with a=q, b=p, c=t, d=r. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnYdn.
        exists q, p, t, r, s.
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (n) fourth edge = (s, q): 3-chain t<p<q + top pendant s<q + iso r
       (HnTopP) with a=t, b=p, c=q, d=s. *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnTopP.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_usq. }
    (* (o) fourth edge = (r, q): 3-chain t<p<q + top pendant r<q + iso s
       (HnTopP). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnTopP.
        exists t, p, q, r, s.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_urq. }
    (* (p) fourth edge = (s, r): 3-chain t<p<q + disjoint chain s<r
       (HnCC). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRsr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; exact Husr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_usr. }
    (* (q) fourth edge = (r, s): 3-chain t<p<q + disjoint chain r<s
       (HnCC). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnCC.
        exists t, p, q, r, s.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRrs |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; exact Hurs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_urs. }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_tp Hnot_ab_tq]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_tp; split; reflexivity
        | apply Hnot_ab_tq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr_fourth; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRst; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt_fourth; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRrs; exact HRab ].
  - exfalso. apply HnChain3.
    exists t, p, q, s, r.
    split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
    split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRxy |].
    split; [exact HRpq |].
    split; [exact HRtq |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
      [left; exact Hutp |].
    destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
      [right; left; exact Hutq |].
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [right; right; exact Hupq |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_utp |]. exact Hnot_utq.
Qed.

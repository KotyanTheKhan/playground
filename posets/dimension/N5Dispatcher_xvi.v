From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (xvi) of the second-edge cascade inside the residual handler:
    second edge is [(q, t)] — by transitivity [R2 p t] holds, so the carrier
    contains the 3-chain [p < q < t] plus isolated [r], [s].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xvi :
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
    (Hnot_pq : ~ (q = p /\ t = q))
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
  assert (HRpt : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRxy).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
            ~ (a = p /\ b = t)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (r, p): 4-chain r<p<q<t + iso s (HnC4). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r q t HRrq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
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
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_new |].
        split; [exact HRrt_new |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    (* (b) fourth edge = (s, p): 4-chain s<p<q<t + iso r (HnC4). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      assert (HRst_new : R2 s t) by exact (HR2.(poset_trans) s q t HRsq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Htp _]; apply Hps_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists s, p, q, t, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_new |].
        split; [exact HRst_new |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (c) fourth edge = (t, r): 4-chain p<q<t<r + iso s (HnC4). *)
    destruct (classic (R2 t r)) as [HRtr_fourth | HnRtr_fourth].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p t r HRpt HRtr_fourth).
      assert (HRqr_new : R2 q r) by exact (HR2.(poset_trans) q t r HRxy HRtr_fourth).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = t /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_fourth |].
        intros [Hrp _]; apply Hpt_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
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
        split; [exact HRtr_fourth |].
        split; [exact HRpt |].
        split; [exact HRpr_new |].
        split; [exact HRqr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; right; right; right; exact Huqr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (d) fourth edge = (t, s): 4-chain p<q<t<s + iso r (HnC4). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p t s HRpt HRts).
      assert (HRqs_new : R2 q s) by exact (HR2.(poset_trans) q t s HRxy HRts).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = t /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Hrp _]; apply Hpt_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
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
        split; [exact HRts |].
        split; [exact HRpt |].
        split; [exact HRps_new |].
        split; [exact HRqs_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; right; right; right; exact Huqs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* (e) fourth edge = (q, r): 5-edge Y-up shape with apex p, branch
       q->{t,r} (HnYup). Note: positioned before (k) (p,r) so that when
       edge = (q,r), transitive p<r is also true but we route here first. *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
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
        split; [exact HRqr |].
        split; [exact HRpt |].
        split; [exact HRpr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (f) fourth edge = (q, s): Y-up apex p, branch q->{t,s} (HnYup). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = s) /\
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
        split; [exact HRqs |].
        split; [exact HRpt |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (g) fourth edge = (r, q): Y-down apex t, q has parents p,r (HnYdn). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r q t HRrq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnYdn.
        exists t, q, p, r, s.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRrt_new |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    (* (h) fourth edge = (s, q): Y-down apex t, q has parents p,s (HnYdn). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRst_new : R2 s t) by exact (HR2.(poset_trans) s q t HRsq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Htp _]; apply Hps_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists t, q, p, s, r.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRst_new |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (i) fourth edge = (r, t): 3-chain p<q<t + top pendant r<t + iso s
       (HnTopP). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [_ Hrq]; apply Hqt_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
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
        split; [exact HRrt |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    (* (j) fourth edge = (s, t): 3-chain p<q<t + top pendant s<t + iso r
       (HnTopP). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [_ Hrq]; apply Hqt_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
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
        split; [exact HRst |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (k) fourth edge = (p, r): pendant from chain bottom (HnPd):
       3-chain p<q<t + pendant p<r + iso s. *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = p /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hsq]; apply Hqr_neq; symmetry; exact Hsq.
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
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRpt |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_upr. }
    (* (l) fourth edge = (p, s): pendant from chain bottom (HnPd). *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = p /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Htq]; apply Hqs_neq; symmetry; exact Htq.
      - exfalso. apply HnPd.
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
        split; [exact HRps |].
        split; [exact HRpt |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ups. }
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
  - exfalso. apply HnChain3.
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
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
      [right; left; exact Hupt |].
    destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
      [right; right; exact Huqt |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_uqt |]. exact Hnot_upt.
Qed.

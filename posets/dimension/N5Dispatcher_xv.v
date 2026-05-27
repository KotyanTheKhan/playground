From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (xv) of the second-edge cascade inside the residual handler:
    second edge is [(q, s)] — by transitivity [R2 p s] holds, so the carrier
    contains the 3-chain [p < q < s] plus isolated [r], [t].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xv :
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
    (HRxy : R2 q s)
    (Hnot_pq : ~ (q = p /\ s = q))
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
  assert (HRps : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRxy).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
            ~ (a = p /\ b = s)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (r, p): 4-chain r<p<q<s + iso t (HnC4). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r q s HRrq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = r /\ b = s)))
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
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_new |].
        split; [exact HRrs_new |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (b) fourth edge = (t, p): 4-chain t<p<q<s + iso r (HnC4). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t q s HRtq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = t /\ b = s)))
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
        exists t, p, q, s, r.
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_new |].
        split; [exact HRts_new |].
        split; [exact HRps |].
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
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (c) fourth edge = (s, r): 4-chain p<q<s<r + iso t (HnC4). *)
    destruct (classic (R2 s r)) as [HRsr_fourth | HnRsr_fourth].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p s r HRps HRsr_fourth).
      assert (HRqr_new : R2 q r) by exact (HR2.(poset_trans) q s r HRxy HRsr_fourth).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = s /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_fourth |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
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
        split; [exact HRsr_fourth |].
        split; [exact HRps |].
        split; [exact HRpr_new |].
        split; [exact HRqr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; right; right; right; exact Huqr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_usr |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (d) fourth edge = (s, t): 4-chain p<q<s<t + iso r (HnC4). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p s t HRps HRst).
      assert (HRqt_new : R2 q t) by exact (HR2.(poset_trans) q s t HRxy HRst).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = s /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
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
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst |].
        split; [exact HRps |].
        split; [exact HRpt_new |].
        split; [exact HRqt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; left; exact Hupt |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; right; right; right; exact Huqt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    (* (e) fourth edge = (q, r): 5-edge Y-up shape with apex p, branch
       q->{s,r} (HnYup). Note: positioned before (k) (p,r) so that when
       edge = (q,r), transitive p<r is also true but we route here first. *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = r) /\
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
        split; [exact HRqr |].
        split; [exact HRps |].
        split; [exact HRpr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (f) fourth edge = (q, t): Y-up apex p, branch q->{s,t} (HnYup). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = t) /\
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
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt |].
        split; [exact HRps |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (g) fourth edge = (r, q): Y-down apex s, q has parents p,r (HnYdn). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r q s HRrq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = s)))
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
        exists s, q, p, r, t.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRrs_new |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (h) fourth edge = (t, q): Y-down apex s, q has parents p,t (HnYdn). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t q s HRtq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = s)))
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
        exists s, q, p, t, r.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRts_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; exact Huts |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (i) fourth edge = (r, s): 3-chain p<q<s + top pendant r<s + iso t
       (HnTopP). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
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
        split; [exact HRrs |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    (* (j) fourth edge = (t, s): 3-chain p<q<s + top pendant t<s + iso r
       (HnTopP). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
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
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (k) fourth edge = (p, r): pendant from chain bottom (HnPd):
       3-chain p<q<s + pendant p<r + iso t. *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = p /\ b = r)))
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
        split; [exact HRpr |].
        split; [exact HRps |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_upr. }
    (* (l) fourth edge = (p, t): pendant from chain bottom (HnPd). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = p /\ b = t)))
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
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_upt. }
    (* (m) fourth edge = (r, t): 3-chain p<q<s + disjoint 2-chain r<t (HnCC). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
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
        split; [exact HRps |].
        split; [exact HRrt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; exact Hurt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urt. }
    (* (n) fourth edge = (t, r): 3-chain p<q<s + disjoint 2-chain t<r (HnCC). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
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
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRtr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; exact Hutr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_utr. }
    (* (o) fourth edge = (q, p) — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (p) fourth edge = (s, q) — antisymmetry contradiction. *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { exfalso. apply Hqs_neq.
      exact (HR2.(poset_antisym) q s HRxy HRsq). }
    (* (q) fourth edge = (s, p) — antisymmetry contradiction. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { exfalso. apply Hps_neq.
      exact (HR2.(poset_antisym) p s HRps HRsp). }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_qs Hnot_ab_ps]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_qs; split; reflexivity
        | apply Hnot_ab_ps; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRsr_fourth; exact HRab
        | apply HnRst; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRts; exact HRab
        | apply HnRtr; exact HRab ].
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
    split; [exact HRxy |].
    split; [exact HRps |].
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
    split; [exact Hnot_uqs |]. exact Hnot_ups.
Qed.

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (xviii) of the second-edge cascade inside the residual handler:
    second edge is [(s, p)] — by transitivity [R2 s q] holds, so the carrier
    admits the 3-chain [s < p < q] plus isolated [r], [t].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xviii :
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
    (HRxy : R2 s p)
    (Hnot_pq : ~ (s = p /\ p = q))
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
  assert (HRsq : R2 s q) by exact (HR2.(poset_trans) s p q HRxy HRpq).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
            ~ (a = s /\ b = q)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) fourth edge = (p, s) — antisymmetry with HRxy : R2 s p. *)
    destruct (classic (R2 p s)) as [HRpr_fourth | HnRpr_fourth].
    { exfalso. apply Hps_neq.
      exact (HR2.(poset_antisym) p s HRpr_fourth HRxy). }
    (* (c) fourth edge = (q, s) — antisymmetry with HRsq : R2 s q. *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { exfalso. apply Hqs_neq.
      exact (HR2.(poset_antisym) q s HRqs HRsq). }
    (* (d) fourth edge = (r, s): 4-chain r<s<p<q + iso t (HnC4). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { assert (HRsp_new : R2 r p) by exact (HR2.(poset_trans) r s p HRrs HRxy).
      assert (HRsq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRsp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
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
        split; [exact HRrs |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsp_new |].
        split; [exact HRsq_new |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (e) fourth edge = (t, s): 4-chain t<s<p<q + iso r (HnC4). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { assert (HRtp_new : R2 t p) by exact (HR2.(poset_trans) t s p HRts HRxy).
      assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
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
        split; [exact HRts |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtp_new |].
        split; [exact HRtq_new |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (f) fourth edge = (q, r): 4-chain s<p<q<r + iso t (HnC4). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRps_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      assert (HRrs_new : R2 s r) by exact (HR2.(poset_trans) s p r HRxy HRps_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = r)))
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRsq |].
        split; [exact HRrs_new |].
        split; [exact HRps_new |].
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
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (g) fourth edge = (q, t): 4-chain s<p<q<t + iso r (HnC4). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      assert (HRrt_new : R2 s t) by exact (HR2.(poset_trans) s p t HRxy HRpt_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
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
        split; [exact HRqt |].
        split; [exact HRsq |].
        split; [exact HRrt_new |].
        split; [exact HRpt_new |].
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
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (h) fourth edge = (s, r): 3-chain s<p<q + pendant s<r + iso t
       (HnPd) with a=s, b=p, c=q, d=r. *)
    destruct (classic (R2 s r)) as [HRrs_fourth | HnRrs_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRrs_fourth |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrs_fourth |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (i) fourth edge = (s, t): 3-chain s<p<q + pendant s<t + iso r
       (HnPd) with a=s, b=p, c=q, d=t. *)
    destruct (classic (R2 s t)) as [HRrt_fourth | HnRrt_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRrt_fourth |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
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
        split; [exact HRrt_fourth |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (j) fourth edge = (p, r): Y-up apex s, branch p->{q,r} (HnYup)
       with a=s, b=p, c=q, d=r. *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { assert (HRsr_via : R2 s r) by exact (HR2.(poset_trans) s p r HRxy HRpr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = r)))
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRsq |].
        split; [exact HRsr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (k) fourth edge = (p, t): Y-up apex s, branch p->{q,t} (HnYup). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { assert (HRst_via : R2 s t) by exact (HR2.(poset_trans) s p t HRxy HRpt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnYup.
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
        split; [exact HRpt |].
        split; [exact HRsq |].
        split; [exact HRst_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (l) fourth edge = (r, p): Y-down apex q, p has parents s,r
       (HnYdn) with a=q, b=p, c=s, d=r. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = p) /\
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
        exists q, p, s, r, t.
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (m) fourth edge = (t, p): Y-down apex q, p has parents s,t
       (HnYdn) with a=q, b=p, c=s, d=t. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists q, p, s, t, r.
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (n) fourth edge = (r, q): 3-chain s<p<q + top pendant r<q + iso t
       (HnTopP) with a=s, b=p, c=q, d=r. *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = q)))
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_urq. }
    (* (o) fourth edge = (t, q): 3-chain s<p<q + top pendant t<q + iso r
       (HnTopP). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnTopP.
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
        split; [exact HRtq |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (p) fourth edge = (r, t): 3-chain s<p<q + disjoint chain r<t
       (HnCC). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnCC.
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; exact Hurt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_urt. }
    (* (q) fourth edge = (t, r): 3-chain s<p<q + disjoint chain t<r
       (HnCC). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
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
        split; [exact HRsq |].
        split; [exact HRtr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; exact Hutr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utr. }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_sp Hnot_ab_sq]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_sp; split; reflexivity
        | apply Hnot_ab_sq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr_fourth; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRts; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt_fourth; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRtr; exact HRab ].
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
    split; [exact HRxy |].
    split; [exact HRpq |].
    split; [exact HRsq |].
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
    split; [exact Hnot_usp |]. exact Hnot_usq.
Qed.

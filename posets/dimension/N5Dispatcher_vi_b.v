From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From Dimension Require Import N5Dispatcher_vi_c.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Second sub-block of micro-case [vi]: 3rd-edge cases (g) [= (s, r)],
    (h) [= (r, t)], (i) [= (q, s)], (j) [= (t, p)], (k) [= (p, s)],
    (l) [= (s, p)].  If none fire, delegates to subcase_c with the
    accumulated negations. *)
Lemma n5_dispatcher_microcase_vi_subcase_b :
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
    (HRxy : R2 s t)
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
    (Hthird :
       exists a b : B,
         a <> b /\ R2 a b /\
         ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t))
    (HnRqr : ~ R2 q r) (HnRrp : ~ R2 r p) (HnRtr : ~ R2 t r)
    (HnRrs : ~ R2 r s) (HnRpr : ~ R2 p r) (HnRrq : ~ R2 r q),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy
         HnN HnVc HninvVc HnC4 HnPd HnTopP Hthird
         HnRqr HnRrp HnRtr HnRrs HnRpr HnRrq.
    (* (g) third edge = (s, r): V at s with leaves t, r + chain p<q (HnVc). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRsr |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists s, t, r, p, q.
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRsr |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |]. exact Hnot_usr. }
    (* (h) third edge = (r, t): inv-V at t with bottoms s, r + chain p<q (HninvVc). *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists s, r, t, p, q.
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |]. exact Hnot_urt. }
    (* (i) third edge = (q, s): 4-chain p<q<s<t + iso r (HnC4). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      assert (HRqt : R2 q t) by exact (HR2.(poset_trans) q s t HRqs HRxy).
      assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = s /\ b = t) /\ ~ (a = p /\ b = s) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
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
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRpt_new |].
        split; [exact HRqt |].
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
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    (* (j) third edge = (t, p): 4-chain s<t<p<q + iso r (HnC4). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRsp : R2 s p) by exact (HR2.(poset_trans) s t p HRxy HRtp).
      assert (HRtq : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      assert (HRsq : R2 s q) by exact (HR2.(poset_trans) s t q HRxy HRtq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = t /\ b = p) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists s, t, p, q, r.
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRsp |].
        split; [exact HRsq |].
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
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (k) third edge = (p, s): 3-chain p<s<t + pendant p<q (HnPd). *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p s t HRps HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = p /\ b = s) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnPd.
        exists p, s, t, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRps |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_new |].
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
        split; [exact Hnot_ust |].
        split; [exact Hnot_ups |]. exact Hnot_upt. }
    (* (l) third edge = (s, p): 3-chain s<p<q + pendant s<t (HnPd). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists s, p, q, t, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
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
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* None of cases (g)-(l) fired - delegate to subcase_c with all 12 negations. *)
    apply (@n5_dispatcher_microcase_vi_subcase_c B R2 HR2 Hcard
             Hnonantichain Hinc_ex p q r s t
             Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
             Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy
             HnN HnTopP Hthird
             HnRqr HnRrp HnRtr HnRrs HnRpr HnRrq
             HnRsr HnRrt_third HnRqs HnRtp HnRps HnRsp).
Qed.

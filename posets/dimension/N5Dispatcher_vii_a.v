From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From Dimension Require Import N5Dispatcher_vii_b.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** First sub-block of micro-case (vii): 3rd-edge cases (a) = (q,r),
    (b) = (r,p), (c) = (s,r), (d) = (r,t), (e) = (p,r), (f) = (r,q).
    If none fire, delegates to subcase_b. *)
Lemma n5_dispatcher_microcase_vii_subcase_a :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (HRpq : R2 p q)
    (HRxy : R2 t s)
    (Hnot_pq : ~ (t = p /\ s = q))
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
                (x = d /\ y = c) \/ (x = a /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq
         HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP.
    (* (a) third edge = (q, r): p<q<r chain + t<s chain (HnCC). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnCC.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRpr_new |].
        split; [exact HRxy |].
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
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* (b) third edge = (r, p): r<p<q chain + t<s chain (HnCC). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRrq_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    (* (c) third edge = (s, r): t<s<r chain + p<q chain (HnCC). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t s r HRxy HRsr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = s /\ b = r) /\ ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRsr |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnCC.
        exists t, s, r, p, q.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRsr |].
        split; [exact HRtr_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_usr |]. exact Hnot_utr. }
    (* (d) third edge = (r, t): r<t<s chain + p<q chain (HnCC). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r t s HRrt HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = r /\ b = t) /\ ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, t, s, p, q.
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRrt |].
        split; [exact HRxy |].
        split; [exact HRrs_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_urt |]. exact Hnot_urs. }
    (* (e) third edge = (p, r): V at p with leaves q, r + chain t<s (HnVc). *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hsq]; apply Hqr_neq; symmetry; exact Hsq.
      - exfalso. apply HnVc.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRxy |].
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
    (* (f) third edge = (r, q): inv-V at q with bottoms p, r + chain t<s (HninvVc). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, r, q, t, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
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
    (* None of cases (a)-(f) fired - delegate to subcase_b. *)
    apply (@n5_dispatcher_microcase_vii_subcase_b B R2 HR2 Hcard
             Hnonantichain Hinc_ex p q r s t
             Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
             Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq
             HnN HnVc HninvVc HnC4 HnPd HnTopP).
Qed.

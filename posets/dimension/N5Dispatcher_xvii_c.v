From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Third sub-block of micro-case (xvii): 4th-edge cases (m) = (t,p)
    Y-down (HnYdn); (n) = (s,q), (o) = (t,q) top pendant (HnTopP);
    (p) = (s,t), (q) = (t,s) disjoint chain (HnCC); plus the final
    exfalso using all 17 accumulated negations. *)
Lemma n5_dispatcher_microcase_xvii_subcase_c :
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
    (HRxy : R2 r p)
    (HRrq : R2 r q)
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
                (x = d /\ y = e)))))
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
    (Hfourth :
       exists a b : B,
         a <> b /\ R2 a b /\
         ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
         ~ (a = r /\ b = q))
    (HnRqp : ~ R2 q p) (HnRpr_fourth : ~ R2 p r) (HnRqr : ~ R2 q r)
    (HnRsr : ~ R2 s r) (HnRtr : ~ R2 t r)
    (HnRqs : ~ R2 q s) (HnRqt : ~ R2 q t)
    (HnRrs_fourth : ~ R2 r s) (HnRrt_fourth : ~ R2 r t)
    (HnRps : ~ R2 p s) (HnRpt : ~ R2 p t)
    (HnRsp : ~ R2 s p),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy HRrq
         HnCC HnTopP HnYdn Hfourth
         HnRqp HnRpr_fourth HnRqr HnRsr HnRtr HnRqs HnRqt
         HnRrs_fourth HnRrt_fourth HnRps HnRpt HnRsp.
    (* (m) fourth edge = (t, p): Y-down apex q, p has parents r,t
       (HnYdn) with a=q, b=p, c=r, d=t. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists q, p, r, t, s.
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (n) fourth edge = (s, q): 3-chain r<p<q + top pendant s<q + iso t
       (HnTopP) with a=r, b=p, c=q, d=s. *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnTopP.
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_usq. }
    (* (o) fourth edge = (t, q): 3-chain r<p<q + top pendant t<q + iso s
       (HnTopP). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnTopP.
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
        split; [exact HRtq |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_utq. }
    (* (p) fourth edge = (s, t): 3-chain r<p<q + disjoint chain s<t
       (HnCC). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = t)))
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
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRst |].
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
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_ust. }
    (* (q) fourth edge = (t, s): 3-chain r<p<q + disjoint chain t<s
       (HnCC). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = s)))
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
        split; [exact HRrq |].
        split; [exact HRts |].
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
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_rp Hnot_ab_rq]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rp; split; reflexivity
        | apply Hnot_ab_rq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr_fourth; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt_fourth; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRst; exact HRab
        | apply HnRts; exact HRab ].
Qed.

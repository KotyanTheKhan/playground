From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Third sub-block of micro-case (ii): 3rd-edge cases (o) = (q,s),
    (p) = (s,q), (m) = (p,s), (n) = (r,q), plus antisymmetry (q),(r) and
    the final exfalso using all 18 accumulated negations. *)
Lemma n5_dispatcher_microcase_ii_subcase_c :
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
    (HRxy : R2 r s)
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
         ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s))
    (HnRqt : ~ R2 q t) (HnRtp : ~ R2 t p) (HnRst_third : ~ R2 s t)
    (HnRtr : ~ R2 t r) (HnRpt : ~ R2 p t) (HnRtq : ~ R2 t q)
    (HnRrt : ~ R2 r t) (HnRts : ~ R2 t s)
    (HnRqr : ~ R2 q r) (HnRsp : ~ R2 s p)
    (HnRpr : ~ R2 p r) (HnRrp : ~ R2 r p),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy
         HnN HnTopP Hthird
         HnRqt HnRtp HnRst_third HnRtr HnRpt HnRtq
         HnRrt HnRts HnRqr HnRsp HnRpr HnRrp.
    (* Sub-case (o): third edge is [(q, s)].  By transitivity R2 p s.
       R2 = {(p,q),(r,s),(q,s),(p,s)}: 3-chain p<q<s + pendant r<s (HnTopP). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
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
        split; [exact HRqs |].
        split; [exact HRxy |].
        split; [exact HRps_new |].
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
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* Sub-case (p): third edge is [(s, q)].  By transitivity R2 r q.
       R2 = {(p,q),(r,s),(s,q),(r,q)}: 3-chain r<s<q + pendant p<q (HnTopP). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r s q HRxy HRsq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnTopP.
        exists r, s, q, p, t.
        split; [exact Hrs_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hpt_neq |].
        split; [exact HRxy |].
        split; [exact HRsq |].
        split; [exact HRpq |].
        split; [exact HRrq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_usq |]. exact Hnot_urq. }
    (* Sub-case (m): third edge is [(p, s)].  R2 contains {(p,q),(p,s),
       (r,s)}: N-shape (HnN) with a=r, c=p, b=s, d=q, plus isolated t.
       Note: positioned after (o) so that when 3rd edge is (q,s) — which
       also implies R2 p s by transitivity — case (o) fires first. *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
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
      - exfalso. apply HnN.
        exists r, s, p, q, t.
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRxy |].
        split; [exact HRps_third |].
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
        split; [exact Hnot_urs |]. exact Hnot_ups. }
    (* Sub-case (n): third edge is [(r, q)].  R2 contains {(p,q),(r,s),
       (r,q)}: N-shape with a=p, b=q, c=r, d=s, plus isolated t.
       Note: positioned after (p) so that when 3rd edge is (s,q) — which
       also implies R2 r q by transitivity — case (p) fires first. *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
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
      - exfalso. apply HnN.
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
        split; [exact HRrq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |]. exact Hnot_urq. }
    (* Sub-case (q): third edge is [(q, p)] — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* Sub-case (r): third edge is [(s, r)] — antisymmetry contradiction. *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { exfalso. apply Hrs_neq.
      exact (HR2.(poset_antisym) r s HRxy HRsr). }
    (* All 18 possible 3rd-edge labelings are ruled out: by Hcov5 the
       witness (a, b) from Hthird must be one of the 18 remaining ordered
       pairs over {p, q, r, s, t} (excluding diagonal and (p,q), (r,s)),
       and each negative classical hypothesis above rejects one. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_rs]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rs; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRts; exact HRab ].
Qed.

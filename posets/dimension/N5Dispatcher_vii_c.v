From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Third sub-block of micro-case (vii): 3rd-edge cases (o) = (q,s),
    (p) = (s,q), (m) = (p,s), (n) = (t,q), antisymmetry (q),(r) and
    the residual routing via [n5_residual_classes_two_realizer] keyed
    by [Hnot_pq]. *)
Lemma n5_dispatcher_microcase_vii_subcase_c :
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
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnN HnTopP.
    (* (o) third edge = (q, s): 3-chain p<q<s + pendant t<s (HnTopP). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
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
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
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
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (p) third edge = (s, q): 3-chain t<s<q + pendant p<q (HnTopP). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t s q HRxy HRsq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnTopP.
        exists t, s, q, p, r.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hpr_neq |].
        split; [exact HRxy |].
        split; [exact HRsq |].
        split; [exact HRpq |].
        split; [exact HRtq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (m) third edge = (p, s): N-shape t<s, p<s, p<q (HnN). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists t, s, p, q, r.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRps_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |]. exact Hnot_ups. }
    (* (n) third edge = (t, q): N-shape p<q, t<q, t<s (HnN). *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
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
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRtq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |]. exact Hnot_utq. }
    (* (q) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (r) third edge = (s, t) — antisymmetry with HRxy : R2 t s. *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { exfalso. apply Hst_neq.
      exact (HR2.(poset_antisym) s t HRst HRxy). }
    (* Otherwise route remaining third-edge cases to the focused admit. *)
    apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, t, s.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [exact HRxy |].
    exact Hnot_pq.
Qed.

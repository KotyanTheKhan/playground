From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (ii), sub-case (d): third edge = [(t, r)].
    By transitivity [R2 t s].  Carrier is 3-chain [t < r < s] disjoint
    from chain [p < q].  Contradicts [HnCC]. *)
Lemma n5_dispatcher_microcase_ii_subcase_a_tr :
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
    (HRxy : R2 r s)
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
    (HRtr : R2 t r),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy HnCC HRtr.
  assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t r s HRtr HRxy).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
            ~ (a = t /\ b = r) /\ ~ (a = t /\ b = s)))
    as [Hfourth | Hno_fourth].
  - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, t, r.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [exact HRtr |].
    intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
  - exfalso. apply HnCC.
    exists t, r, s, p, q.
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
    split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
    split; [exact Hrs_neq |].
    split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
    split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
    split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
    split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
    split; [exact Hpq_neq |].
    split; [exact HRtr |].
    split; [exact HRxy |].
    split; [exact HRts_new |].
    split; [exact HRpq |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
      [left; exact Hutr |].
    destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
      [right; left; exact Hurs |].
    destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
      [right; right; left; exact Huts |].
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [right; right; right; exact Hupq |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_urs |].
    split; [exact Hnot_utr |]. exact Hnot_uts.
Qed.

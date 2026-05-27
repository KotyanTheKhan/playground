From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (ii), sub-case (c): third edge = [(s, t)].
    By transitivity [R2 r t].  Carrier is 3-chain [r < s < t] disjoint
    from chain [p < q].  Contradicts [HnCC]. *)
Lemma n5_dispatcher_microcase_ii_subcase_a_st :
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
    (HRst_third : R2 s t),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy HnCC HRst_third.
  assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r s t HRxy HRst_third).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
            ~ (a = s /\ b = t) /\ ~ (a = r /\ b = t)))
    as [Hfourth | Hno_fourth].
  - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, s, t.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [exact Hst_neq |].
    split; [exact HRst_third |].
    intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
  - exfalso. apply HnCC.
    exists r, s, t, p, q.
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
    split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
    split; [exact Hst_neq |].
    split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
    split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
    split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
    split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
    split; [exact Hpq_neq |].
    split; [exact HRxy |].
    split; [exact HRst_third |].
    split; [exact HRrt_new |].
    split; [exact HRpq |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
      [left; exact Hurs |].
    destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
      [right; left; exact Hust |].
    destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
      [right; right; left; exact Hurt |].
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [right; right; right; exact Hupq |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_urs |].
    split; [exact Hnot_ust |]. exact Hnot_urt.
Qed.

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (ii), sub-case (a): third edge = [(q, t)].
    By transitivity [R2 p t].  If no fourth edge exists beyond
    [{(p,q), (q,t), (p,t), (r,s)}], the carrier is the 3-chain
    [p < q < t] disjoint from the chain [r < s], contradicting [HnCC]. *)
Lemma n5_dispatcher_microcase_ii_subcase_a_qt :
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
    (HRqt : R2 q t),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy HnCC HRqt.
  assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
            ~ (a = p /\ b = t) /\ ~ (a = r /\ b = s)))
    as [Hfourth | Hno_fourth].
  - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, q, t.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [exact Hqt_neq |].
    split; [exact HRqt |].
    intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
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
    split; [exact HRqt |].
    split; [exact HRpt_new |].
    split; [exact HRxy |].
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
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_uqt |].
    split; [exact Hnot_upt |]. exact Hnot_urs.
Qed.

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (ii), sub-case (f): third edge = [(t, q)].
    Inv-V at [q] with bottoms [p], [t], plus chain [r < s].
    Contradicts [HninvVc].  Written in expanded form (no
    [n5_split_witness]/[n5_close_forall_via] combinators) for faster
    Qed checking. *)
Lemma n5_dispatcher_microcase_ii_subcase_a_tq :
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
    (HRtq : R2 t q),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy HninvVc HRtq.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
            ~ (a = r /\ b = s)))
    as [Hfourth | Hno_fourth].
  - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, t, q.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
    split; [exact HRtq |].
    intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
  - exfalso. apply HninvVc.
    exists p, t, q, r, s.
    split; [exact Hpt_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRtq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
      [right; left; exact Hutq |].
    destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
      [right; right; exact Hurs |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_utq |]. exact Hnot_urs.
Qed.

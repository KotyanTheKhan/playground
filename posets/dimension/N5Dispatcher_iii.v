From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Micro-case (iii) of the second-edge cascade inside the residual handler:
    second edge is [(s, r)].  Extracted from
    [n5_nonantichain_nonchain_two_realizer] so that its Qed-closure compiles
    independently of the surrounding ~17k-line cascade.

    Shape: if no third strict edge exists, the carrier consists of disjoint
    chains [(p, q)] and [(s, r)] plus isolated [t], contradicting [HnDisj];
    otherwise route to [n5_residual_classes_two_realizer]. *)
Lemma n5_dispatcher_microcase_iii :
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
    (HRxy : R2 s r)
    (Hnot_pq : ~ (s = p /\ r = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d)))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = r)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists: route to the focused admit. *)
    apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, s, r.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRxy |].
    exact Hnot_pq.
  - exfalso. apply HnDisj.
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
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
      [right; exact Husr |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_usr.
Qed.

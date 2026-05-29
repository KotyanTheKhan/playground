(** Shared focused admit and helper imports for the n=5 dispatcher
    micro-cases.

    Extracted from [N5Dispatcher.v] so that each micro-case file can
    [Require Import] this small module instead of pulling in the entire
    dispatcher source.  The focused admit
    [n5_residual_classes_two_realizer] is the single remaining TODO for
    the n=5 non-antichain non-chain residual catch-all. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers.
From Dimension.N5Exhaustive Require Import
  EdgeCount EdgeCount1 EdgeCount2 EdgeCount3 EdgeCount4
  EdgeCount5 EdgeCount6 EdgeCount7 EdgeCount8 EdgeCount9.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** If any two carrier elements are incomparable, the edge count is at
    most 9: that pair contributes 0 to the count, and the other nine
    unordered pairs each contribute at most 1 (antisymmetry). *)
Lemma edge_count_5_le_9_of_incomp :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
         (p q r s t : B),
    p <> q -> p <> r -> p <> s -> p <> t ->
    q <> r -> q <> s -> q <> t ->
    r <> s -> r <> t -> s <> t ->
    (forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t) ->
    (exists a b : B, @Incomparable B R2 a b) ->
    edge_count_5 R2 p q r s t <= 9.
Proof.
  intros B R2 HR2 p q r s t Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Hinc.
  destruct Hinc as [a [b Hincp]].
  assert (Hab0 : strict_indicator R2 a b = 0).
  { apply strict_indicator_eq_0. intros [HR _]. apply Hincp. left. exact HR. }
  assert (Hba0 : strict_indicator R2 b a = 0).
  { apply strict_indicator_eq_0. intros [HR _]. apply Hincp. right. exact HR. }
  pose proof (strict_indicator_antisym R2 p q Hpq).
  pose proof (strict_indicator_antisym R2 p r Hpr).
  pose proof (strict_indicator_antisym R2 p s Hps).
  pose proof (strict_indicator_antisym R2 p t Hpt).
  pose proof (strict_indicator_antisym R2 q r Hqr).
  pose proof (strict_indicator_antisym R2 q s Hqs).
  pose proof (strict_indicator_antisym R2 q t Hqt).
  pose proof (strict_indicator_antisym R2 r s Hrs).
  pose proof (strict_indicator_antisym R2 r t Hrt).
  pose proof (strict_indicator_antisym R2 s t Hst).
  unfold edge_count_5.
  destruct (Hcov a) as [Ha|[Ha|[Ha|[Ha|Ha]]]];
  destruct (Hcov b) as [Hb|[Hb|[Hb|[Hb|Hb]]]];
  subst a b;
  try (exfalso; apply Hincp; left; apply poset_refl);
  lia.
Qed.

(** n=5 non-antichain non-chain residual: dispatch on the edge count.

    From the >=2-edges hypothesis pick a strict edge [(p, q)] and complete
    it (via [carrier_5_destructure]) to all five carrier elements.  The
    edge count [k = edge_count_5 R2 p q r s t] satisfies [1 <= k <= 9]
    (non-antichain gives [k >= 1]; an incomparable pair gives [k <= 9]).
    Route each value to its per-edge-count two-realizer handler:
    counts 1-4 are Qed; counts 5-9 are the focused admits
    [n5_edge_count_{5..9}_two_realizer] (see
    docs/superpowers/plans/2026-05-29-admit1-n5-residual.md). *)
Lemma n5_residual_classes_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 5 ->
  ~ (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, @Incomparable B R2 a b) ->
  (exists p q x y : B,
     p <> q /\ R2 p q /\
     x <> y /\ R2 x y /\ ~ (x = p /\ y = q)) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard Hnac Hinc Hedges.
  destruct Hedges as [p [q [x [y [Hpq_ne [HRpq [Hxy_ne [HRxy Hne]]]]]]]].
  destruct (carrier_5_destructure p q Hcard Hpq_ne)
    as [r [s [t [Hpr [Hps [Hpt [Hqr [Hqs [Hqt [Hrs [Hrt [Hst Hcov]]]]]]]]]]]].
  assert (Hk_pos : edge_count_5 R2 p q r s t >= 1).
  { apply (proj1 (non_antichain_iff_edge_count_pos R2 p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov)). exact Hnac. }
  assert (Hk_le9 : edge_count_5 R2 p q r s t <= 9).
  { apply (edge_count_5_le_9_of_incomp R2 p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov). exact Hinc. }
  destruct (edge_count_5 R2 p q r s t)
    as [|[|[|[|[|[|[|[|[|[|k']]]]]]]]]] eqn:Ek.
  - lia.
  - exact (n5_edge_count_1_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_2_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_3_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_4_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_5_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_6_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_7_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_8_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - exact (n5_edge_count_9_two_realizer R2 Hcard p q r s t
             Hpq_ne Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcov Ek).
  - lia.
Qed.

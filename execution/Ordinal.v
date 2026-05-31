(* ordinal-sum decomposition of executions *)

From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimCriticalPairs Frontier.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* Execution order restricted to a sub-ensemble S — a sub-poset. *)
Definition sub_order (E : ExecPoset) (S : Ensemble (ep_carrier E))
  : {x : ep_carrier E | Ensembles.In _ S x} -> {x | Ensembles.In _ S x} -> Prop :=
  fun x y => ep_order E (proj1_sig x) (proj1_sig y).

Instance sub_order_poset (E : ExecPoset) (S : Ensemble (ep_carrier E))
  : IsPoset _ (sub_order E S) := subtype_is_poset (ep_order E) S.

Definition no_alt_cycle (A : Type) (R : A -> A -> Prop) : Prop :=
  ~ (exists cycle,
       (forall p, List.In p cycle -> IsCriticalPair R (fst p) (snd p))
       /\ IsAlternatingCycle R cycle).

(* A poset's dimension is unique. *)
Lemma posdim_unique :
  forall (A : Type) (R : A -> A -> Prop) `{IsPoset A R} d d',
    PosetDimension R d -> PosetDimension R d' -> d = d'.
Proof.
  intros A R HP d d' Hd Hd'.
  apply Nat.le_antisymm.
  - apply (dimension_is_minimum Hd (dimension_realizer Hd')
             d' (dimension_is_realizer Hd') (dimension_cardinality Hd')).
  - apply (dimension_is_minimum Hd' (dimension_realizer Hd)
             d (dimension_is_realizer Hd) (dimension_cardinality Hd)).
Qed.

Lemma barrier_critical_pairs :
  forall E L U, IsBarrier E L U ->
    forall x y, IsCriticalPair (ep_order E) x y ->
      (Ensembles.In _ L x /\ Ensembles.In _ L y) \/
      (Ensembles.In _ U x /\ Ensembles.In _ U y).
Proof.
  intros E L U HB x y Hcp.
  assert (Hinc : Incomparable (ep_order E) x y) by exact Hcp.(critical_incomparable).
  unfold Incomparable in Hinc.
  destruct HB as [Hcov [_ [_ [_ Hbelow]]]].
  destruct (Hcov x) as [HxL | HxU]; destruct (Hcov y) as [HyL | HyU].
  - left. split; assumption.
  - exfalso. apply Hinc. left. apply Hbelow; assumption.
  - exfalso. apply Hinc. right. apply Hbelow; assumption.
  - right. split; assumption.
Qed.

Lemma barrier_dim_ge :
  forall E L U, IsBarrier E L U ->
    forall dL dU d,
      PosetDimension (sub_order E L) dL ->
      PosetDimension (sub_order E U) dU ->
      PosetDimension (ep_order E) d ->
      Nat.max dL dU <= d.
Proof.
  intros E L U HB dL dU d HdimL HdimU Hd.
  (* L block *)
  destruct (subposet_dimension_le (ep_order E) L d Hd)
    as [d_qL [HdimL_inh HleL]].
  destruct HdimL_inh as [HdimL_q].
  assert (HeqL : dL = d_qL)
    by exact (posdim_unique _ (sub_order E L) dL d_qL HdimL HdimL_q).
  (* U block *)
  destruct (subposet_dimension_le (ep_order E) U d Hd)
    as [d_qU [HdimU_inh HleU]].
  destruct HdimU_inh as [HdimU_q].
  assert (HeqU : dU = d_qU)
    by exact (posdim_unique _ (sub_order E U) dU d_qU HdimU HdimU_q).
  lia.
Qed.

From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              Reduction ExtremumReduction DimExamples FrontierExamples BarrierDim2.

#[local] Existing Instance hb_IsPoset.

Lemma E_min_block_dim2 :
  forall S : Ensemble (ep_carrier E_min),
    exists d, inhabited (PosetDimension (sub_order E_min S) d) /\ d <= 2.
Proof.
  intro S.
  destruct E_min_dim_2 as [Hd2].
  destruct (subposet_dimension_le (ep_order E_min) S 2 Hd2) as [dq [Hinh Hle]].
  exists dq; split; [exact Hinh | exact Hle].
Qed.

Example E_min_dim_le_2_via_barrier :
  exists d, exec_has_dimension E_min d /\ d <= 2.
Proof.
  apply (barrier_dim_le2 E_min Lmin Umin E_min_barrier).
  - apply E_min_block_dim2.
  - apply E_min_block_dim2.
Qed.

Print Assumptions E_min_dim_le_2_via_barrier.

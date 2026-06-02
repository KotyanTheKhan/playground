(* Transformation B example: a concrete 2-process block and its simplification,
   both dim <= 2 (test-only). *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                           ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import TransformB DimTwoGeneric ChainDim.

(* the 2-process inter-sync block has dim <= 2 (the "<= 2 critical pairs" content) *)
Example B2_dim_le2_demo : forall d, PosetDimension B2_R d -> d <= 2.
Proof. exact B2_dim_le2. Qed.

(* The equal-bound that drives Transformation B: both the 2-process block and its
   one-local-modification simplification have dim <= 2, so swapping one for the other
   preserves the bound (and hence, via fully_sync_dim_le2, the whole execution's dim <= 2). *)
Example transform_B_equal_bound :
  (forall d, PosetDimension B2_R d -> d <= 2) /\
  (forall d, PosetDimension B2s_R d -> d <= 2).
Proof. split; [exact B2_dim_le2 | exact B2s_dim_le2]. Qed.

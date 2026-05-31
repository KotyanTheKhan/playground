(* extremum reduction examples (test-only)

   The concrete E_min extremum-removal instance: ev_a = (0,0) is the global
   minimum, so removing it preserves dim<=2.  Reuses the DimExamples helpers. *)

From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Reduction
                              DimExamples ExtremumReduction.

#[local] Existing Instance hb_IsPoset.

Example E_min_a_global_min : IsGlobalMin E_min ev_a.
Proof.
  unfold IsGlobalMin. intro x.
  destruct (valid_event_min_cases x) as [H | [H | [H | H]]]; simpl in H.
  - rewrite (eq_ev_a x H). apply poset_refl.
  - rewrite (eq_ev_b x H). exact hb_a_b.
  - rewrite (eq_ev_c x H). exact hb_a_c.
  - rewrite (eq_ev_d x H). exact hb_a_d.
Qed.

Example E_min_remove_min_dim2 :
  (exists d, inhabited (PosetDimension (sub_order E_min (fun x => x <> ev_a)) d) /\ d <= 2)
  <->
  (exists d, exec_has_dimension E_min d /\ d <= 2).
Proof.
  exact (remove_min_preserves_dim2 E_min ev_a E_min_a_global_min).
Qed.

Example E_min_block_dim_le_2_via_extremum :
  exists d, inhabited (PosetDimension (sub_order E_min (fun x => x <> ev_a)) d) /\ d <= 2.
Proof.
  apply (proj2 E_min_remove_min_dim2).
  exists 2. split; [exact E_min_dim_2 | lia].
Qed.

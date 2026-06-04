(* generic finite-poset lever examples (test-only)

   Applies the carrier-generic levers from FinPosetDimSurgery / FinPosetDim to
   the concrete E_min execution, showing they reproduce the same dim<=2 result
   obtained by the execution-specific levers.  No new mathematical content. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Finite Edges Rank Poset DimBridge Ordinal
                              DimExamples ExtremumReduction FinPosetDimSurgery FinPosetDim.

#[local] Existing Instance hb_IsPoset.

(* The carrier of E_min is finite (Finite A (Full_set A) form needed by generic levers). *)
Lemma E_min_carrier_finite : Finite (ep_carrier E_min) (Full_set (ep_carrier E_min)).
Proof.
  apply (cardinal_finite _ _ (total (ep_ranked E_min))).
  exact (event_cardinal (ep_ranked E_min)).
Qed.

(* ev_a is a generic global minimum in the sense of fin_global_min. *)
Lemma E_min_fin_global_min : fin_global_min (ep_order E_min) ev_a.
Proof.
  unfold fin_global_min. intro x.
  destruct (valid_event_min_cases x) as [H | [H | [H | H]]]; simpl in H.
  - rewrite (eq_ev_a x H). apply poset_refl.
  - rewrite (eq_ev_b x H). exact hb_a_b.
  - rewrite (eq_ev_c x H). exact hb_a_c.
  - rewrite (eq_ev_d x H). exact hb_a_d.
Qed.

(* The generic lever reproduces E_min's dim<=2 result. *)
Example fin_chain_reproduces_E_min :
  exists d, inhabited (PosetDimension (ep_order E_min) d) /\ d <= 2.
Proof.
  (* E_min has dimension 2 (from DimExamples) *)
  destruct E_min_dim_2 as [Hd2].
  (* Apply the generic min-removal lever *)
  apply (proj1 (fin_remove_min_dim2 (ep_order E_min) E_min_carrier_finite
                  ev_a E_min_fin_global_min)).
  (* The complement of {ev_a} in E_min has dim<=2: it's a subposet of E_min *)
  apply (subposet_dimension_le (ep_order E_min) (fun x => x <> ev_a) 2 Hd2).
Qed.
Print Assumptions fin_chain_reproduces_E_min.

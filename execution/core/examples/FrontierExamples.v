(* frontier/barrier examples (test-only)

   A concrete bottom barrier on the minimal execution E_min:
     Lmin = { a }            (the unique minimum (0,0))
     Umin = { b, c, d }      (everything else)
   This is a barrier, and so every critical pair lands inside one block. *)

From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical Relation_Operators ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs.
From Execution Require Import Op Event Edges Rank Poset Schedule DimExamples Frontier Ordinal.

#[local] Existing Instance hb_IsPoset.

Definition Lmin : Ensemble (ep_carrier E_min) := fun x => proj1_sig x = (0,0).
Definition Umin : Ensemble (ep_carrier E_min) := fun x => proj1_sig x <> (0,0).

Example E_min_barrier : IsBarrier E_min Lmin Umin.
Proof.
  unfold IsBarrier. repeat split.
  - (* cover *)
    intro x. unfold Ensembles.In, Lmin, Umin.
    destruct (classic (proj1_sig x = (0,0))) as [Heq | Hne].
    + left. exact Heq.
    + right. exact Hne.
  - (* disjoint *)
    intros x [HL HU]. exact (HU HL).
  - (* inhabited Lmin: event a = (0,0) *)
    exists ev_a. unfold Ensembles.In, Lmin. reflexivity.
  - (* inhabited Umin: event b = (0,1) *)
    exists ev_b. unfold Ensembles.In, Umin. discriminate.
  - (* Hbelow *)
    intros x y HxL HyU.
    unfold Ensembles.In, Lmin in HxL.
    unfold Ensembles.In, Umin in HyU.
    (* canonicalize x to ev_a *)
    rewrite (eq_ev_a x HxL).
    (* split y into the four cases; (0,0) is excluded by HyU *)
    pose proof (valid_event_min_cases y) as Hy. simpl in Hy.
    destruct Hy as [Hy | [Hy | [Hy | Hy]]].
    + exfalso. apply HyU. exact Hy.
    + rewrite (eq_ev_b y Hy). exact hb_a_b.
    + rewrite (eq_ev_c y Hy). exact hb_a_c.
    + rewrite (eq_ev_d y Hy). exact hb_a_d.
Qed.

Example E_min_barrier_cps :
  forall x y, IsCriticalPair (ep_order E_min) x y ->
    (Ensembles.In _ Lmin x /\ Ensembles.In _ Lmin y) \/
    (Ensembles.In _ Umin x /\ Ensembles.In _ Umin y).
Proof.
  exact (barrier_critical_pairs E_min Lmin Umin E_min_barrier).
Qed.

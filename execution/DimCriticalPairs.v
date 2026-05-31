(* execution dimension bridge — DimCriticalPairs (layer 2a) *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset.
From Execution Require Import DimBridge.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition exec_critical_pair (E : ExecPoset) (x y : ep_carrier E) : Prop :=
  IsCriticalPair (ep_order E) x y.

(* Every incomparable pair of an execution contains a critical pair. *)
Lemma exec_incomparable_has_critical_pair :
  forall E (x y : ep_carrier E),
    Incomparable (ep_order E) x y ->
    exists x' y',
      ep_order E x' x /\ ep_order E y y' /\ exec_critical_pair E x' y'.
Proof.
  intros E x y Hinc.
  unfold exec_critical_pair, ep_carrier, ep_order in *.
  pose (Hfin := cardinal_finite (Event (ep_ranked E))
                  (Full_set (Event (ep_ranked E))) (ep_size E) (ep_size_ok E)).
  apply (incomparable_lifting_to_critical_pair
           (hb (ep_ranked E)) Hfin x y Hinc).
Qed.

(* Reversibility characterization, specialized to executions.
   NOTE the HS hypothesis: S must consist of critical pairs (required by the library). *)
Lemma exec_critical_pairs_reversible_iff_no_alt_cycle :
  forall E (S : Ensemble (ep_carrier E * ep_carrier E)),
    (forall p, Ensembles.In _ S p -> exec_critical_pair E (fst p) (snd p)) ->
    ((exists L, IsLinearExtension (ep_order E) L /\
                forall x y, Ensembles.In _ S (x, y) -> L y x)
     <->
     ~ (exists cycle,
          (forall p, List.In p cycle -> Ensembles.In _ S p)
          /\ IsAlternatingCycle (ep_order E) cycle)).
Proof.
  intros E S HS.
  unfold exec_critical_pair, ep_carrier, ep_order in *.
  apply (critical_pairs_reversible_iff_no_alternating_cycle
           (hb (ep_ranked E)) S HS).
Qed.

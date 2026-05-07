(* Lamport's Happened-Before Relation for Distributed Systems *)

(* ========== Notation Summary ========== *)
(*
   Events and Messages:
   - ⟨p, i⟩         : Event with process p and index i
   - e1 →ₘ e2       : Message from event e1 to event e2
   
   Relations:
   - e1 ≺[h] e2     : e1 happened-before e2 in history h
   - e1 ≺ e2        : e1 happened-before e2 (empty history)
   - e1 ∥[h] e2     : e1 and e2 are concurrent in history h
   - e1 ∥ e2        : e1 and e2 are concurrent (empty history)
*)

(* Import all submodules *)
Require Import EventStructure.
Require Import CausalRelation.
Require Import CausalRelationProps.
From HappenedBefore Require Import PosetInstance.


(* Re-export for convenience *)
Export EventStructure.
Export CausalRelation.
Export CausalRelationProps.
Require Import LamportClock.
Export LamportClock.

(* ========== Happened-Before Class ========== *)

Require Import Posets.PosetClasses.

Class IsHappenedBefore (h : History) (R : Event -> Event -> Prop) := {
  hb_is_poset :> IsPoset Event R
}.

(* Instance for the standard happened_before relation 
   Requires the history to be acyclic for antisymmetry to hold. *)
Instance is_happened_before_inst (h : History) (H_acyclic : IsAcyclic h) : IsHappenedBefore h (happened_before h).
Proof.
  constructor.
  apply happened_before_poset; assumption.
Defined.

(* Instance for Lamport Clock Total Order *)
Instance lamport_hb_inst (h : History) (c : Clock) : IsHappenedBefore h (lamport_le c).
Proof.
  constructor.
  apply lamport_le_poset.
Defined.

(* ========== Summary ========== *)

(* Lamport's happened-before relation demonstrates:
   
   1. POSET: It is a partial order (reflexive, antisymmetric, transitive)
      - Reflexive: Every event happened before itself
      - Antisymmetric: No cycles (e1 ≺ e2 and e2 ≺ e1 implies e1 = e2)
      - Transitive: Built into the definition via hb_trans
      - ✅ FULLY PROVEN
   
   2. NOT A LATTICE:
      - The happened-before relation is NOT a lattice, nor even a semilattice.
      - For an empty history, events on different processes have no common predecessor (no GLB)
        and no common successor (no LUB).
      - See `SemilatticeContradiction.v` for formal proofs of these impossibilities.
   
   3. LAMPORT CLOCK:
      - We can define a total ordering consistent with the happened-before relation
        using Lamport timestamps and process IDs.
   
   This structure is fundamental to understanding causality in distributed systems,
   vector clocks, and eventual consistency. *)

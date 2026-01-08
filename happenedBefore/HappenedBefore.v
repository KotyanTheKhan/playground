(* Lamport's Happened-Before Relation for Distributed Systems *)

(* ========== Notation Summary ========== *)
(*
   Events and Messages:
   - ⟨p, c⟩         : Event with process p and clock c
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
   
   This structure is fundamental to understanding causality in distributed systems,
   vector clocks, and eventual consistency. *)

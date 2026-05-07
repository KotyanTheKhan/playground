(* Eventual Consistency Module - Main Entry Point *)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import PeanoNat.

(* ========== Comprehensive Notation Guide ========== *)
(*
   ╔══════════════════════════════════════════════════════════════════╗
   ║                   REPLICA STATES & UPDATES                       ║
   ╚══════════════════════════════════════════════════════════════════╝
   
   Construction:
   - ⟨r, s, v⟩ᵣ        : Replica with id r, state s, version vector v
   - ⟨o, r, ctx⟩ᵤ      : Update with operation o, from replica r, context ctx
   - s ⟶ r ∶ u        : Message from replica s to r with update u
   
   ╔══════════════════════════════════════════════════════════════════╗
   ║                    VERSION VECTORS                               ║
   ╚══════════════════════════════════════════════════════════════════╝
   
   Operations:
   - v1 ⊑ v2          : Version v1 causally precedes v2 (v1[i] ≤ v2[i] ∀i)
   - v1 ⊔ᵥ v2         : Merge (join) version vectors (max component-wise)
   - v ↑ r            : Increment version v at replica r
   
   ╔══════════════════════════════════════════════════════════════════╗
   ║                    STATE OPERATIONS                              ║
   ╚══════════════════════════════════════════════════════════════════╝
   
   State Operations:
   - s1 ⊔ s2          : Merge (join/LUB) of states s1 and s2
   - s ⊕ op           : Apply operation op to state s
   - rs ⊙ u           : Apply update u to replica state rs
   - rs1 ⊔ᵣ rs2       : Merge replica states rs1 and rs2
   
   ╔══════════════════════════════════════════════════════════════════╗
   ║                    CAUSALITY & ORDERING                          ║
   ╚══════════════════════════════════════════════════════════════════╝
   
   Update Relations:
   - u1 ≺ᵤ u2         : Update u1 causally precedes u2
   - u1 ∥ᵤ u2         : Updates u1 and u2 are concurrent
   
   State Relations:
   - s1 ≈ s2          : States s1 and s2 are equivalent
   - s1 ⊑ₛ s2         : State s1 grows to s2 (monotonic)
   
   ╔══════════════════════════════════════════════════════════════════╗
   ║                    CONVERGENCE                                   ║
   ╚══════════════════════════════════════════════════════════════════╝
   
   System Properties:
   - rs1 ≈ᵣ rs2       : Replicas rs1 and rs2 have converged
   - ⊤[cfg]           : Configuration cfg has converged (all replicas agree)
   
   ╔══════════════════════════════════════════════════════════════════╗
   ║                    EXAMPLE USAGE                                 ║
   ╚══════════════════════════════════════════════════════════════════╝
   
   Given replicas r1, r2 and updates u1, u2:
   
   1. Apply update:     r1' = r1 ⊙ u1
   2. Merge replicas:   r = r1 ⊔ᵣ r2
   3. Merge states:     s = s1 ⊔ s2
   4. Apply operation:  s' = s ⊕ op
   5. Check causality:  u1 ≺ᵤ u2  or  u1 ∥ᵤ u2
   6. Check convergence: r1 ≈ᵣ r2  or  ⊤[cfg]
   
   Lattice Properties:
   - Commutativity: s1 ⊔ s2 = s2 ⊔ s1
   - Associativity: (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3)
   - Idempotency:   s ⊔ s = s
*)

(* Import all submodules *)
Require Import StateModel.
Require Import ReplicatedStructure.
Require Import MergeOperations.
Require Import ConvergenceProof.
Require Import EventualConsistencyClass.

(* Re-export for convenience *)
Export StateModel.
Export ReplicatedStructure.
Export MergeOperations.
Export ConvergenceProof.
(* Note: EventualConsistencyClass is not exported to avoid notation conflicts.
   Users can explicitly import it when needed with: 
   Require Import EventualConsistencyClass. *)

(* ========== Summary ========== *)

(* Eventual Consistency Guarantees:
   
   1. EVENTUAL CONSISTENCY: 
      In a distributed system with replicas, if all replicas eventually 
      receive all updates, they will converge to the same state.
   
   2. STRONG EVENTUAL CONSISTENCY (SEC):
      Replicas that have delivered the same set of updates have 
      equivalent states, regardless of the order of delivery.
   
   3. REPLICATED DATA STRUCTURES:
      Data structures that satisfy commutativity, associativity, 
      and idempotency of merge operations guarantee SEC.
   
   4. CONVERGENCE IN FINITE TIME:
      Under reliable delivery assumptions, the system converges 
      in finite time after all updates have been delivered.
   
   Key Properties:
   - Commutativity: merge s1 s2 = merge s2 s1
   - Associativity: merge (merge s1 s2) s3 = merge s1 (merge s2 s3)
   - Idempotency: merge s s = s
   - Monotonicity: States grow monotonically with updates
   
   Applications:
   - Distributed databases (Cassandra, Riak, Redis)
   - Collaborative editing (Google Docs, Figma)
   - Distributed caching
   - Mobile offline-first applications
   
   This formalization is based on:
   - Shapiro et al. "A comprehensive study of Convergent and Commutative Replicated Data Types" (2011)
   - Shapiro et al. "Conflict-free Replicated Data Types" (2011)
   - Burckhardt et al. "Replicated Data Types: Specification, 
     Verification, Optimality" (2014)
*)

(* ========== Example: Grow-Only Counter ========== *)

(* A simple example of a replicated counter *)
Section CounterExample.
  
  (* State is a natural number *)
  Definition CounterState := nat.
  
  (* Merge takes the maximum *)
  Definition counter_merge (c1 c2 : CounterState) : CounterState :=
    Nat.max c1 c2.
  
  (* Increment operation *)
  Definition counter_increment (c : CounterState) : CounterState :=
    S c.
  
  (* Verify consistency properties *)
  Lemma counter_merge_commutative : forall c1 c2,
    counter_merge c1 c2 = counter_merge c2 c1.
  Proof.
    intros c1 c2.
    unfold counter_merge.
    apply Nat.max_comm.
  Qed.
  
  Lemma counter_merge_associative : forall c1 c2 c3,
    counter_merge (counter_merge c1 c2) c3 = 
    counter_merge c1 (counter_merge c2 c3).
  Proof.
    intros c1 c2 c3.
    unfold counter_merge.
    symmetry.
    apply Nat.max_assoc.
  Qed.
  
  Lemma counter_merge_idempotent : forall c,
    counter_merge c c = c.
  Proof.
    intros c.
    unfold counter_merge.
    apply Nat.max_idempotent.
  Qed.

End CounterExample.

(* ========== Connection to Posets and Lattices ========== *)

(* The convergence property of eventual consistency is deeply connected
   to the lattice structure of states:
   
   1. PARTIAL ORDER: States form a poset under the "causally precedes" relation
   
   2. JOIN SEMILATTICE: The merge operation is the join (least upper bound)
      - Associative: (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3)
      - Commutative: s1 ⊔ s2 = s2 ⊔ s1
      - Idempotent: s ⊔ s = s
   
   3. MONOTONIC: Applying updates moves states upward in the lattice
   
   4. CONVERGENCE: All execution paths lead to the same least upper bound
   
   This is why lattice theory is fundamental to distributed systems! *)

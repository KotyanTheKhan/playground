# Eventual Consistency Module

This module provides a formal verification of eventual consistency and convergence properties in distributed systems using Coq.

## Overview

Eventual consistency is a consistency model used in distributed computing to achieve high availability. It guarantees that, in the absence of new updates, all replicas will eventually converge to the same state.

## Notation Reference

This module uses rich mathematical notation to express distributed systems concepts clearly:

### Replica States & Construction
- `⟨r, s, v⟩ᵣ` — Replica with id `r`, state `s`, version vector `v`
- `⟨o, r, ctx⟩ᵤ` — Update with operation `o`, origin `r`, causal context `ctx`
- `s ⟶ r ∶ u` — Message from replica `s` to `r` containing update `u`

### Version Vectors
- `v1 ⊑ v2` — Version `v1` causally precedes `v2` (component-wise ≤)
- `v1 ⊔ᵥ v2` — Merge (join) of version vectors (max component-wise)
- `v ↑ r` — Increment version `v` at replica `r`

### State Operations
- `s1 ⊔ s2` — Merge (join/LUB) of states `s1` and `s2`
- `s ⊕ op` — Apply operation `op` to state `s`
- `rs ⊙ u` — Apply update `u` to replica state `rs`
- `rs1 ⊔ᵣ rs2` — Merge replica states `rs1` and `rs2`

### Causality & Ordering
- `u1 ≺ᵤ u2` — Update `u1` causally precedes `u2`
- `u1 ∥ᵤ u2` — Updates `u1` and `u2` are concurrent
- `s1 ≈ s2` — States `s1` and `s2` are equivalent
- `s1 ⊑ₛ s2` — State `s1` grows to `s2` (monotonic)

### Convergence Properties
- `rs1 ≈ᵣ rs2` — Replicas `rs1` and `rs2` have converged
- `⊤[cfg]` — Configuration `cfg` has converged (all replicas agree)

## Module Structure

### StateModel.v
- Defines replica states, version vectors, and update operations
- Establishes causal ordering between updates using version vectors
- Provides helper functions for version vector comparisons and merging

### ReplicatedStructure.v  
- Defines replicated data structure properties
- Specifies the axioms for eventual consistency:
  - **Commutativity**: `merge s1 s2 = merge s2 s1`
  - **Associativity**: `merge (merge s1 s2) s3 = merge s1 (merge s2 s3)`
  - **Idempotency**: `merge s s = s`
  - **Monotonicity**: States grow monotonically with updates
- Proves that merge operations form a semilattice

### MergeOperations.v
- Implements system evolution through update delivery
- Defines quiescence (when all replicas have received all updates)
- Provides operations for merging replica states
- Proves that merge order doesn't affect the final state

### ConvergenceProof.v
- **Main Theorem**: Strong Eventual Consistency
  - If all replicas deliver all updates, they converge to the same state
- Proves convergence in finite time under reliable delivery
- Shows that concurrent updates commute
- Establishes monotonic state growth property

### EventualConsistency.v
- Main entry point that exports all submodules
- Provides example replicated data structure (grow-only counter)
- Connects eventual consistency to lattice theory

## Key Theorems

### Strong Eventual Consistency
```coq
Theorem strong_eventual_consistency : 
  forall (n : nat) (updates : list Update),
    let cfg := initial_configuration n in
    let final_cfg := deliver_all_updates cfg updates in
    configuration_converged final_cfg.
```

### Finite Convergence
```coq
Theorem finite_convergence :
  forall (cfg : Configuration) (updates : UpdateHistory),
    finite_quiescence cfg updates ->
    exists final_cfg : Configuration,
      configuration_converged final_cfg.
```

## Connection to Lattice Theory

The convergence property of eventual consistency is deeply connected to lattice structures:

1. **Partial Order**: States form a poset under "causally precedes"
2. **Join Semilattice**: Merge operation is the join (⊔) 
3. **Monotonic**: Updates move states upward in the lattice
4. **Convergence**: All paths lead to the same least upper bound

## Applications

- Distributed databases (Cassandra, Riak, Redis)
- Collaborative editing (Google Docs, Figma)  
- Distributed caching
- Mobile offline-first applications

## References

- Shapiro et al. "A comprehensive study of Convergent and Commutative Replicated Data Types" (2011)
- Shapiro et al. "Conflict-free Replicated Data Types" (2011)
- Burckhardt et al. "Replicated Data Types: Specification, Verification, Optimality" (2014)

## Building

This module is part of the larger `playground` Coq project. To build:

```bash
dune build
```

## Usage

```coq
Require Import EventualConsistency.

(* Use the definitions and theorems *)
Check strong_eventual_consistency.
Check merge_commutative.
```

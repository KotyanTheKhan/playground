# Eventual Consistency Module - Notations Summary

## Overview

The Eventual Consistency module uses rich mathematical notation to express distributed systems concepts. This document provides a complete reference.

## 📚 Files with Notations

1. **StateModel.v** - Replica states, version vectors, causality
2. **ReplicatedStructure.v** - State operations, consistency properties
3. **MergeOperations.v** - Convergence properties
4. **ConvergenceProof.v** - Theorems and proofs
5. **Examples.v** - Practical examples using all notations
6. **NOTATION_REFERENCE.md** - Quick reference card

## 🎨 Complete Notation List

### Construction Notations
```coq
⟨r, s, v⟩ᵣ          Replica state with id, state, version
⟨o, r, ctx⟩ᵤ        Update with operation, origin, context  
s ⟶ r ∶ u          Message from s to r containing update u
```

### Version Vector Notations
```coq
v1 ⊑ v2            v1 causally precedes v2
v1 ⊔ᵥ v2           Merge version vectors
v ↑ r              Increment version at replica r
```

### State Operation Notations
```coq
s1 ⊔ s2            Merge (join) states
s ⊕ op             Apply operation to state
rs ⊙ u             Apply update to replica
rs1 ⊔ᵣ rs2         Merge replica states
```

### Relation Notations
```coq
u1 ≺ᵤ u2           Causal precedence
u1 ∥ᵤ u2           Concurrent updates
s1 ≈ s2            State equivalence
s1 ⊑ₛ s2           Monotonic state growth
rs1 ≈ᵣ rs2         Replica convergence
⊤[cfg]             Configuration convergence
```

## 🔧 Usage Examples

### Basic Operations
```coq
(* Create a replica *)
Definition my_replica := ⟨0, init_state, cons 0 (cons 0 nil)⟩ᵣ.

(* Create an update *)
Definition my_update := ⟨increment, 0, cons 0 (cons 0 nil)⟩ᵤ.

(* Apply update to replica *)
Definition updated_replica := my_replica ⊙ my_update.

(* Merge two replicas *)
Definition merged := replica1 ⊔ᵣ replica2.
```

### Version Vectors
```coq
(* Compare versions *)
Example v1_before_v2 : v1 ⊑ v2 := ...

(* Merge versions *)
Definition merged_version := v1 ⊔ᵥ v2.

(* Increment version *)
Definition new_version := old_version ↑ 0.
```

### Causality
```coq
(* Check if updates are causally ordered *)
Lemma ordered : u1 ≺ᵤ u2 -> ...

(* Check if updates are concurrent *)
Lemma concurrent : u1 ∥ᵤ u2 -> ...
```

### Convergence
```coq
(* Prove replicas have converged *)
Theorem replicas_agree : r1 ≈ᵣ r2.

(* Prove system has converged *)
Theorem system_converged : ⊤[configuration].
```

## 📊 Notation Categories

### Level 0 (Highest Precedence)
- `⟨r, s, v⟩ᵣ` - Replica construction
- `⟨o, r, ctx⟩ᵤ` - Update construction
- `⊤[cfg]` - Convergence predicate

### Level 40
- `v ↑ r` - Version increment

### Level 45
- `s ⊕ op` - Apply operation
- `rs ⊙ u` - Apply update to replica

### Level 50
- `s1 ⊔ s2` - State merge
- `v1 ⊔ᵥ v2` - Version vector merge
- `rs1 ⊔ᵣ rs2` - Replica merge

### Level 70
- `v1 ⊑ v2` - Version precedence
- `u1 ≺ᵤ u2` - Causal precedence
- `u1 ∥ᵤ u2` - Concurrent
- `s1 ≈ s2` - State equivalence
- `s1 ⊑ₛ s2` - State growth
- `rs1 ≈ᵣ rs2` - Replica convergence

### Level 80
- `s ⟶ r ∶ u` - Message construction

## 🎯 Design Principles

1. **Subscripts distinguish types**:
   - `⊔ᵥ` for version vectors
   - `⊔ᵣ` for replica states
   - `⊔` for plain states
   - `≺ᵤ` for updates
   - `≈ᵣ` for replicas
   - `⊑ₛ` for states

2. **Lattice-inspired notation**:
   - `⊔` (join/LUB) for merging
   - `⊑` (less-than-or-equal) for ordering
   - `⊤` (top) for convergence

3. **Causality notation**:
   - `≺` (precedes) for causal ordering
   - `∥` (parallel) for concurrency

4. **Consistency with existing modules**:
   - Similar to happenedBefore module
   - Follows lattice theory conventions

## 🔍 Theorem Examples with Notation

```coq
(* Strong Eventual Consistency *)
Theorem SEC : 
  ∀ cfg updates. deliver_all(cfg, updates) → ⊤[cfg].

(* Commutativity of Merge *)
Axiom merge_comm : 
  ∀ s1 s2. s1 ⊔ s2 = s2 ⊔ s1.

(* Concurrent Updates Commute *)
Lemma concurrent_commute :
  ∀ u1 u2. u1 ∥ᵤ u2 → (s ⊕ op u1) ⊕ op u2 = (s ⊕ op u2) ⊕ op u1.

(* Monotonic Growth *)
Lemma monotonic :
  ∀ rs u. state rs ⊑ₛ state (rs ⊙ u).

(* Causal Precedence Transitive *)
Lemma causal_trans :
  ∀ u1 u2 u3. u1 ≺ᵤ u2 → u2 ≺ᵤ u3 → u1 ≺ᵤ u3.
```

## 💡 Tips for Using Notations

1. **Import the module**: `Require Import EventualConsistency.`
2. **Export makes notations available**: `Export EventualConsistency.`
3. **Check precedence**: Use parentheses when unsure
4. **Use `Locate` in Coq**: `Locate "⊔".` to find definition
5. **See Examples.v**: Contains working examples of all notations

## 🌟 Benefits

- **Concise**: `r ⊙ u` vs `apply_update r u`
- **Mathematical**: Follows lattice theory conventions
- **Readable**: `u1 ≺ᵤ u2` clearly shows causality
- **Consistent**: Same style across the module
- **Typed**: Subscripts prevent confusion between types

## 📖 Further Reading

- See `NOTATION_REFERENCE.md` for quick reference
- See `Examples.v` for practical usage
- See `README.md` for module overview
- See individual `.v` files for definitions

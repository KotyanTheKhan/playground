# Tree Poset Notation Guide

This document describes the convenient notation available for working with tree posets and lattices.

## Tree Construction

### Basic Constructors
- `leaf n` - Create a leaf node with value `n`
  - Example: `leaf 5`
  - Equivalent to: `Leaf 5`

- `l ⟨ r ⟩` - Create a node with left subtree `l` and right subtree `r`
  - Example: `(leaf 1) ⟨ (leaf 2) ⟩`
  - Equivalent to: `Node (Leaf 1) (Leaf 2)`

### Complex Trees
You can compose these notations to build complex trees:
```coq
Definition example_tree := 
  ((leaf 1) ⟨ (leaf 2) ⟩) ⟨ ((leaf 3) ⟨ (leaf 4) ⟩) ⟩.
```

## Ordering Relations

### Partial Order
- `t1 ≤ₜ t2` - Tree ordering (pointwise comparison)
  - For leaves: `leaf n1 ≤ₜ leaf n2` means `n1 ≤ n2`
  - For nodes: `(l1 ⟨ r1 ⟩) ≤ₜ (l2 ⟨ r2 ⟩)` means `l1 ≤ₜ l2 ∧ r1 ≤ₜ r2`
  - Any leaf is less than any node

### Strict Order
- `t1 <ₜ t2` - Strict tree ordering
  - Defined as: `t1 ≤ₜ t2 ∧ ¬(t2 ≤ₜ t1)`

## Lattice Operations

### Meet (Infimum/Greatest Lower Bound)
- `t1 ⊓ₜ t2` - Tree meet (minimum)
  - Computes the pointwise minimum of two trees
  - Example: `(leaf 5) ⊓ₜ (leaf 3) = leaf 3`
  - Example: `((leaf 1) ⟨ (leaf 4) ⟩) ⊓ₜ ((leaf 2) ⟨ (leaf 3) ⟩) = (leaf 1) ⟨ (leaf 3) ⟩`

### Join (Supremum/Least Upper Bound)
- `t1 ⊔ₜ t2` - Tree join (maximum)
  - Computes the pointwise maximum of two trees
  - Example: `(leaf 5) ⊔ₜ (leaf 3) = leaf 5`
  - Example: `((leaf 1) ⟨ (leaf 4) ⟩) ⊔ₜ ((leaf 2) ⟨ (leaf 3) ⟩) = (leaf 2) ⟨ (leaf 4) ⟩`

## Usage Examples

```coq
(* Simple leaf comparisons *)
Example ex1 : (leaf 1) ≤ₜ (leaf 2).

(* Node comparisons *)
Example ex2 : ((leaf 0) ⟨ (leaf 1) ⟩) ≤ₜ ((leaf 1) ⟨ (leaf 2) ⟩).

(* Meet operations *)
Example ex3 : (leaf 5) ⊓ₜ (leaf 3) = leaf 3.

(* Join operations *)
Example ex4 : (leaf 5) ⊔ₜ (leaf 3) = leaf 5.

(* Complex lattice operations *)
Example ex5 : 
  let t1 := (leaf 1) ⟨ (leaf 4) ⟩ in
  let t2 := (leaf 2) ⟨ (leaf 3) ⟩ in
  (t1 ⊓ₜ t2) = (leaf 1) ⟨ (leaf 3) ⟩.
```

## Precedence Levels

The notation is designed with the following precedence (higher binds tighter):
1. `leaf` (level 10) - highest precedence
2. `⟨ ⟩` (level 55) - node construction
3. `⊓ₜ` (level 60) - meet operation
4. `⊔ₜ` (level 65) - join operation  
5. `≤ₜ`, `<ₜ` (level 70) - ordering relations

This allows you to write expressions like:
```coq
(leaf 1) ⊓ₜ (leaf 2) ≤ₜ (leaf 3) ⊔ₜ (leaf 4)
```
which is parsed as:
```coq
((leaf 1) ⊓ₜ (leaf 2)) ≤ₜ ((leaf 3) ⊔ₜ (leaf 4))
```

## Properties

The tree structure with these operations forms:
- **Poset**: Reflexive, antisymmetric, and transitive ordering
- **Meet-Semilattice**: Meet operation is associative, commutative, and idempotent
- **Join-Semilattice**: Join operation is associative, commutative, and idempotent
- **Lattice**: Both meet and join semilattices with absorption laws

See `Instances.v` for the formal proofs of these properties.

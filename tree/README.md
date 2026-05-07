# Tree Poset Module

Binary tree structure with poset and lattice instances.

## Structure

### Files

1. **Structure.v** - Tree data type and ordering relation
   - `Tree` inductive type (Leaf, Node)
   - `tree_le` ordering relation
   - Notation: `t1 ≤ₜ t2`

2. **Operations.v** - Lattice operations
   - `tree_head_val` - Extract leftmost leaf
   - `tree_meet` - Greatest lower bound (smaller head)
   - `tree_join` - Least upper bound (larger head)
   - Notation: `t1 ⊓ₜ t2`, `t1 ⊔ₜ t2`

3. **Instances.v** - Poset and lattice proofs
   - `IsPoset` instance
   - `IsMeetSemilattice` instance
   - `IsJoinSemilattice` instance
   - `IsLattice` instance

4. **Examples.v** - Usage examples
   - Example trees (leaves and nodes)
   - Ordering examples
   - Meet/join examples
   - Head value extraction

5. **Tree.v** - Main aggregator with documentation

## Usage

```coq
Require Tree.Tree.

(* Create trees *)
Definition t1 := Leaf 1.
Definition t2 := Node (Leaf 2) (Leaf 3).

(* Use ordering *)
Example ex : t1 ≤ₜ Leaf 2.

(* Use lattice operations *)
Definition meet_result := t1 ⊓ₜ t2.
```

## Notation

| Notation | Meaning |
|----------|---------|
| `t1 ≤ₜ t2` | Tree ordering |
| `t1 ⊓ₜ t2` | Tree meet (GLB) |
| `t1 ⊔ₜ t2` | Tree join (LUB) |

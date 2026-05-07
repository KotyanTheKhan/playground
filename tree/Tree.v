(* Binary tree poset and lattice - Main aggregator *)

(* Import all tree submodules *)
Require Import Structure.
Require Import Operations.
Require Import Instances.
Require Import Examples.

(* Re-export for convenience *)
Export Structure.
Export Operations.

(* ========== Summary ========== *)

(* Binary trees form a partial order and lattice structure:
   
   1. STRUCTURE: Binary trees with natural number leaves
      - Leaf n: Terminal node with value n
      - Node l r: Internal node with left and right subtrees
   
   2. ORDERING: tree_le (≤ₜ)
      - Leaves ordered by their values
      - Nodes ordered if subtrees change in compatible way
   
   3. OPERATIONS:
      - tree_head_val: Extract leftmost leaf value
      - tree_meet (⊓ₜ): Returns tree with smaller head value
      - tree_join (⊔ₜ): Returns tree with larger head value
   
   4. POSET: Partial order (reflexive, antisymmetric, transitive)
   
   5. LATTICE: Has both meet and join operations
      - Meet semilattice: associative, commutative, idempotent
      - Join semilattice: associative, commutative, idempotent
      - Absorption laws satisfied
   
   This structure is useful for representing hierarchical data
   with ordering based on tree structure. *)

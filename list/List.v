(* Custom list poset and lattice - Main aggregator *)

(* Import all list submodules *)
(* Require Import Structure.
Require Import Operations.
Require Import Instances.
Require Import Examples. *)

(* Re-export for convenience *)
(* Export Structure.
Export Operations. *)

(* ========== Summary ========== *)

(* Custom lists form a partial order and lattice structure:
   
   1. STRUCTURE: Custom list type with natural numbers
      - Nil: Empty list
      - Cons n l: List with head n and tail l
      - Notation: [], [1], [1; 2; 3]
   
   2. OPERATIONS:
      - length_List: Count elements
      - append_List (++): Concatenate lists
   
   3. ORDERING: list_le (≤ₗ)
      - Lists ordered by their length
      - Shorter lists are "less than" longer lists
   
   4. LATTICE OPERATIONS:
      - list_meet (⊓ₗ): Returns the shorter list
      - list_join (⊔ₗ): Returns the longer list
   
   5. POSET: Partial order (reflexive, antisymmetric, transitive)
      - Based on length comparison
   
   6. LATTICE: Has both meet and join operations
      - Meet semilattice: associative, commutative, idempotent
      - Join semilattice: associative, commutative, idempotent
      - Absorption laws satisfied
   
   This structure demonstrates ordering based on a derived property
   (length) rather than lexicographic or pointwise comparison. *)

(* Transformation A examples (test-only) *)
(* The synchronization square and its contraction have equal dimension (both 1) —
   the per-block equal-dimension fact that makes Transformation A dimension-preserving. *)

From Stdlib Require Import Arith.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import TransformA.

(* PosetDimension is a typeclass in Type, so the two instances live over
   different carriers (Sq vs bool) and cannot be combined with the Prop
   conjunction /\.  We therefore state them as two separate Examples —
   each is a direct witness for the literal dimension value 1. *)

Example transform_A_square_dim_1 : PosetDimension B_square_R 1 :=
  B_square_dim_1.

Example transform_A_contracted_dim_1 : PosetDimension B_contracted_R 1 :=
  B_contracted_dim_1.

(** Count-8 (8 comparable pairs) iso-class patterns for the n=5 dispatcher.

    The 6 iso-classes were extracted as canonical 8-edge shapes (up to
    relabeling) from the 450 labeled count-8 posets among the 11520 constrained
    orientation-assignments. Each pattern is a [has_edges_of_shape] of its 8
    required strict edges (index k of the canonical form -> v_{k+1}). *)

From Stdlib Require Import List.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect.

Definition is_c8_1_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4);(v5,v3);(v5,v4)]).
Definition is_c8_2_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4);(v5,v2);(v5,v3);(v5,v4)]).
Definition is_c8_3_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v4,v3);(v5,v2);(v5,v3);(v5,v4)]).
Definition is_c8_4_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4);(v2,v5);(v3,v4)]).
Definition is_c8_5_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4);(v3,v4);(v5,v4)]).
Definition is_c8_6_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4);(v3,v4);(v5,v3);(v5,v4)]).

Definition any_pattern_8_b (M : M5) : bool :=
  is_c8_1_b M || is_c8_2_b M || is_c8_3_b M ||
  is_c8_4_b M || is_c8_5_b M || is_c8_6_b M.

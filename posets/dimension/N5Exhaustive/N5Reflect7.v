(** Count-7 (7 comparable pairs) iso-class patterns for the n=5 dispatcher.

    The 9 iso-classes were extracted (N5Extract7) as canonical 7-edge shapes
    (up to relabeling) from the count-7 posets among the 15360 constrained
    orientation-assignments [enum_k_none 10 3]. Each pattern is a
    [has_edges_of_shape] of its 7 required strict edges. *)

From Stdlib Require Import List.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8.

Definition is_c7_1_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4);(v2,v5)]).
Definition is_c7_2_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4);(v5,v3);(v5,v4)]).
Definition is_c7_3_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4);(v5,v3)]).
Definition is_c7_4_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v5,v2);(v5,v3);(v5,v4)]).
Definition is_c7_5_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4);(v3,v4)]).
Definition is_c7_6_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v4,v3);(v5,v3)]).
Definition is_c7_7_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v4,v3);(v5,v2);(v5,v3)]).
Definition is_c7_8_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4);(v3,v4);(v5,v4)]).
Definition is_c7_9_b : M5 -> bool :=
  has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
    [(v1,v2);(v1,v3);(v2,v3);(v4,v2);(v4,v3);(v5,v2);(v5,v3)]).

Definition any_pattern_7_b (M : M5) : bool :=
  is_c7_1_b M || is_c7_2_b M || is_c7_3_b M || is_c7_4_b M || is_c7_5_b M ||
  is_c7_6_b M || is_c7_7_b M || is_c7_8_b M || is_c7_9_b M.

(* count-7 = 3 incomparable canonical pairs = 3 Nones in the 10-slot assignment. *)
Definition count7_assigns : list (list (option bool)) := enum_k_none 10 3.

Definition chk7 (a : list (option bool)) : bool :=
  orb (negb (is_poset_b (mat_of a))) (any_pattern_7_b (mat_of a)).

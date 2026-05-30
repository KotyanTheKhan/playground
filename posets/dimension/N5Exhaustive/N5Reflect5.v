(** Count-5 (5 comparable pairs) iso-class patterns for the n=5 dispatcher.
    10 iso-classes (N5Extract5) as canonical 5-edge shapes from the count-5
    posets among the 8064 assignments [enum_k_none 10 5]. *)

From Stdlib Require Import List.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8.

Definition is_c5_1_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v5,v2);(v5,v3)]).
Definition is_c5_2_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v5,v4)]).
Definition is_c5_3_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3)]).
Definition is_c5_4_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4)]).
Definition is_c5_5_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v4,v2);(v4,v3);(v5,v2)]).
Definition is_c5_6_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v2,v3);(v4,v3);(v4,v5)]).
Definition is_c5_7_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v5,v3)]).
Definition is_c5_8_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v4,v3)]).
Definition is_c5_9_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v2,v3);(v4,v2);(v4,v3)]).
Definition is_c5_10_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v2,v3);(v4,v3);(v5,v3)]).

Definition any_pattern_5_b (M : M5) : bool :=
  is_c5_1_b M || is_c5_2_b M || is_c5_3_b M || is_c5_4_b M || is_c5_5_b M ||
  is_c5_6_b M || is_c5_7_b M || is_c5_8_b M || is_c5_9_b M || is_c5_10_b M.

Definition count5_assigns : list (list (option bool)) := enum_k_none 10 5.

Definition chk5 (a : list (option bool)) : bool :=
  orb (negb (is_poset_b (mat_of a))) (any_pattern_5_b (mat_of a)).

(** Count-6 (6 comparable pairs) iso-class patterns for the n=5 dispatcher.
    The 12 iso-classes were extracted (N5Extract6) as canonical 6-edge shapes
    from the count-6 posets among the 13440 assignments [enum_k_none 10 4]. *)

From Stdlib Require Import List.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8.

Definition is_c6_1_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v5,v2);(v5,v3);(v5,v4)]).
Definition is_c6_2_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v4,v5)]).
Definition is_c6_3_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v2,v4)]).
Definition is_c6_4_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v4,v2);(v4,v3);(v5,v2);(v5,v3)]).
Definition is_c6_5_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v5,v3);(v5,v4)]).
Definition is_c6_6_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v1,v5);(v2,v3);(v4,v3)]).
Definition is_c6_7_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4);(v5,v3)]).
Definition is_c6_8_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v5,v2);(v5,v3)]).
Definition is_c6_9_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v2,v4);(v3,v4)]).
Definition is_c6_10_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v2,v3);(v4,v3);(v4,v5);(v5,v3)]).
Definition is_c6_11_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v1,v4);(v2,v3);(v4,v3);(v5,v3)]).
Definition is_c6_12_b : M5 -> bool := has_edges_of_shape (fun v1 v2 v3 v4 v5 =>
  [(v1,v2);(v1,v3);(v2,v3);(v4,v2);(v4,v3);(v5,v3)]).

Definition any_pattern_6_b (M : M5) : bool :=
  is_c6_1_b M || is_c6_2_b M || is_c6_3_b M || is_c6_4_b M || is_c6_5_b M ||
  is_c6_6_b M || is_c6_7_b M || is_c6_8_b M || is_c6_9_b M || is_c6_10_b M ||
  is_c6_11_b M || is_c6_12_b M.

Definition count6_assigns : list (list (option bool)) := enum_k_none 10 4.

Definition chk6 (a : list (option bool)) : bool :=
  orb (negb (is_poset_b (mat_of a))) (any_pattern_6_b (mat_of a)).

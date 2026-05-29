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

(* ---- constrained count-8 enumeration + per-candidate check (shared by chunks) ---- *)

(* length-n option-bool lists with EXACTLY k Nones (direct; no 59049 detour). *)
Fixpoint enum_k_none (n k : nat) : list (list (option bool)) :=
  match n with
  | O => match k with O => [ [] ] | S _ => [] end
  | S n' =>
      (match k with O => [] | S k' => map (cons None) (enum_k_none n' k') end)
      ++ flat_map (fun b => map (cons (Some b)) (enum_k_none n' k)) [true; false]
  end.
Definition count8_assigns : list (list (option bool)) := enum_k_none 10 2.

Definition pairs10 : list (Fin.t 5 * Fin.t 5) :=
  [ (f0,f1);(f0,f2);(f0,f3);(f0,f4);(f1,f2);(f1,f3);(f1,f4);(f2,f3);(f2,f4);(f3,f4) ].
Definition assign_edges (a : list (option bool)) : list (Fin.t 5 * Fin.t 5) :=
  flat_map (fun po => match snd po with
            | None => [] | Some true => [(fst (fst po), snd (fst po))]
            | Some false => [(snd (fst po), fst (fst po))] end) (combine pairs10 a).
Definition mat_of (a : list (option bool)) : M5 := from_edges (assign_edges a).

(* candidate is fine: not a poset, or matches a pattern. *)
Definition chk8 (a : list (option bool)) : bool :=
  orb (negb (is_poset_b (mat_of a))) (any_pattern_8_b (mat_of a)).

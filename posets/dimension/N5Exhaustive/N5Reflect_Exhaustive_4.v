(** N5Reflect_Exhaustive_4.v — exhaustiveness over sublists chunk 4/5. *)
From Stdlib Require Import Bool List Arith.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect.

Definition exhaustive_4edge_chunk_4 : list (list (Fin.t 5 * Fin.t 5)) :=
  firstn 2530 (skipn 7590 (sublists 4 all_pairs)).

Lemma exhaustive_4edge_chunk_4_holds :
  forallb (fun es =>
    let M := from_edges es in
    implb (is_poset_b M && Nat.eqb (edge_count_b M) 4)
          (any_pattern_b M))
    exhaustive_4edge_chunk_4 = true.
Proof.
  native_cast_no_check (eq_refl true).
Qed.

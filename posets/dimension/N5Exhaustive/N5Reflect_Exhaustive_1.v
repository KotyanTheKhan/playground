(** N5Reflect_Exhaustive_1.v — exhaustiveness over sublists chunk 1/5
    ([firstn 2530] of the 12650 size-4 sublists). *)
From Stdlib Require Import Bool List Arith.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect.

Definition exhaustive_4edge_chunk_1 : list (list (Fin.t 5 * Fin.t 5)) :=
  firstn 2530 (sublists 4 all_pairs).

Lemma exhaustive_4edge_chunk_1_holds :
  forallb (fun es =>
    let M := from_edges es in
    implb (is_poset_b M && Nat.eqb (edge_count_b M) 4)
          (any_pattern_b M))
    exhaustive_4edge_chunk_1 = true.
Proof.
  native_cast_no_check (eq_refl true).
Qed.

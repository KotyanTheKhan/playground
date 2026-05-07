(* Bounded iteration along an A → sum A A matching.
   chain_root_aux follows inl-edges until either fuel runs out or an inr-cell
   is reached; depth_aux counts the steps taken. Both are used by the
   chain-assignment kernel to extract a la-target and a chain-fiber for each
   element of sub. *)

From Stdlib Require Import Arith Lia.

Section Iter.
  Context {A : Type}.

  Lemma Nat_le_of_succ_le (n m : nat) : Datatypes.S n <= m -> n <= m.
  Proof. lia. Qed.

  Fixpoint chain_root_aux (m : A -> sum A A) (fuel : nat) (x : A) : A :=
    match fuel with
    | 0 => x
    | S k => match m x with
             | inr _ => x
             | inl y => chain_root_aux m k y
             end
    end.

  Fixpoint depth_aux (m : A -> sum A A) (fuel : nat) (x : A) : nat :=
    match fuel with
    | 0 => 0
    | S k => match m x with
             | inr _ => 0
             | inl y => S (depth_aux m k y)
             end
    end.

End Iter.

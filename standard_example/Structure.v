From Stdlib Require Import Arith.Arith.
From Stdlib Require Import PeanoNat.

(* Define the elements of the poset *)
Inductive Element :=
  | A (i : nat)
  | B (j : nat).

(* Equality for Element is decidable *)
Definition eq_dec_Element (x y : Element) : {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

(* 
  Standard Example S(n,k)
  Elements: {A_0, ..., A_{n-1}} U {B_0, ..., B_{n-1}}
  Order:
    - Reflexivity: x <= x
    - A_i <= B_j iff exists d, 0 <= d <= k /\ j = (i + d) mod n
*)
Inductive StandardExampleRel (n k : nat) : Element -> Element -> Prop :=
  | SER_Refl : forall x, StandardExampleRel n k x x
  | SER_Le : forall i j, 
      (exists d, d <= k /\ j = (i + d) mod n) -> 
      StandardExampleRel n k (A i) (B j).

(* Crown Poset S(n, 1) *)
Definition CrownPoset (n : nat) := StandardExampleRel n 1.

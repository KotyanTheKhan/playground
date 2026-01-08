(* List lattice operations *)
Require Import Structure.

(* ========== Helper Functions ========== *)

(* Helper: less-than-or-equal for nat *)
Fixpoint nat_leb (n m : nat) : bool :=
  match n, m with
  | 0, _ => true
  | S _, 0 => false
  | S n', S m' => nat_leb n' m'
  end.

(* ========== List Lattice Operations ========== *)

(* Lexicographic comparison (returns true if l1 <= l2 lexicographically) *)
Fixpoint list_lex_leb (l1 l2 : List) : bool :=
  match l1, l2 with
  | Nil, _ => true
  | Cons _ _, Nil => false
  | Cons x xs, Cons y ys =>
      if nat_leb x y then
        if nat_leb y x then list_lex_leb xs ys
        else true
      else false
  end.

(* List comparison: by length first, then lexicographically *)
Definition list_leb (l1 l2 : List) : bool :=
  if nat_leb (length_List l1) (length_List l2) then
    if nat_leb (length_List l2) (length_List l1) then
      list_lex_leb l1 l2
    else true
  else false.

(* List meet: returns the lesser list *)
Definition list_meet (l1 l2 : List) : List :=
  if list_leb l1 l2 then l1 else l2.

(* List join: returns the greater list *)
Definition list_join (l1 l2 : List) : List :=
  if list_leb l1 l2 then l2 else l1.

(* Notation for list lattice operations *)
Notation "l1 '⊓ₗ' l2" := (list_meet l1 l2) (at level 60).
Notation "l1 '⊔ₗ' l2" := (list_join l1 l2) (at level 65).

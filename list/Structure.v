(* Custom list structure *)

(* ========== List Data Type ========== *)

Inductive List :=
| Nil : List
| Cons : nat -> List -> List.

(* Notation for list construction *)
Notation "[]" := Nil.
Notation "[ x ]" := (Cons x Nil).
Notation "[ x ; y ; .. ; z ]" := (Cons x (Cons y .. (Cons z Nil) ..)).

(* ========== List Operations ========== *)

(* Length of a list *)
Fixpoint length_List (l : List) : nat :=
  match l with
  | Nil => 0
  | Cons _ l' => S (length_List l')
  end.

(* Append two lists *)
Fixpoint append_List (l1 l2 : List) : List :=
  match l1 with
  | Nil => l2
  | Cons x l1' => Cons x (append_List l1' l2)
  end.

(* Notation for append *)
Notation "l1 '++' l2" := (append_List l1 l2) (at level 60, right associativity).

(* ========== Ordering Relation ========== *)

(* Lexicographic comparison of lists *)
Fixpoint list_lex_le (l1 l2 : List) : Prop :=
  match l1, l2 with
  | Nil, _ => True
  | Cons _ _, Nil => False
  | Cons x xs, Cons y ys =>
      x < y \/ (x = y /\ list_lex_le xs ys)
  end.

(* List ordering: by length, then lexicographically *)
Definition list_le (l1 l2 : List) : Prop :=
  length_List l1 < length_List l2 \/
  (length_List l1 = length_List l2 /\ list_lex_le l1 l2).

(* Notation for list ordering *)
Notation "l1 '≤ₗ' l2" := (list_le l1 l2) (at level 70).

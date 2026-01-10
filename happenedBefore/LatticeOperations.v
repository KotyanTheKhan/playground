(* Lattice operations for events *)
Require Import EventStructure.

(* ========== Lexicographical Meet (Total Order) ========== *)

(* 
   The lexicographical meet of two events.
   NOTE: This defines a meet operation for a LEXICOGRAPHICAL TOTAL ORDER on events.
   It is NOT the greatest lower bound (GLB) for the happened-before partial order.
*)
Definition lex_meet (h : History) (e1 e2 : Event) : Event :=
  (* Return the event with smaller process id *)
  if nat_leb (process e1) (process e2) then e1 else e2.

(* Notation for lexicographical meet *)
Notation "e1 '⊓[' h ']' e2" := (lex_meet h e1 e2) (at level 60).
Notation "e1 '⊓' e2" := (lex_meet nil e1 e2) (at level 60).

(* ========== Lexicographical Join (Total Order) ========== *)

(* 
   The lexicographical join of two events.
   NOTE: This defines a join operation for a LEXICOGRAPHICAL TOTAL ORDER on events.
   It is NOT the least upper bound (LUB) for the happened-before partial order.
*)
Definition lex_join (h : History) (e1 e2 : Event) : Event :=
  (* Return the event with larger process id *)
  if nat_leb (process e1) (process e2) then e2 else e1.

(* Notation for lexicographical join *)
Notation "e1 '⊔[' h ']' e2" := (lex_join h e1 e2) (at level 65).
Notation "e1 '⊔' e2" := (lex_join nil e1 e2) (at level 65).

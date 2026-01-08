(* Tree lattice operations *)
Require Import Structure.
Require Import Nat.

(* ========== Tree Operations ========== *)

(* Extract the head value (leftmost leaf) from a tree *)
Fixpoint tree_head_val (t : Tree) : nat :=
  match t with
  | Leaf n => n
  | Node l r => tree_head_val l
  end.

(* Tree meet: recursively take minimum *)
Fixpoint tree_meet (t1 t2 : Tree) : Tree :=
  match t1, t2 with
  | Leaf n1, Leaf n2 => Leaf (Nat.min n1 n2)
  | Node l1 r1, Node l2 r2 => Node (tree_meet l1 l2) (tree_meet r1 r2)
  | Leaf n, Node l r => Leaf n  (* Leaf is always smaller *)
  | Node l r, Leaf n => Leaf n  (* Leaf is always smaller *)
  end.

(* Tree join: recursively take maximum *)
Fixpoint tree_join (t1 t2 : Tree) : Tree :=
  match t1, t2 with
  | Leaf n1, Leaf n2 => Leaf (Nat.max n1 n2)
  | Node l1 r1, Node l2 r2 => Node (tree_join l1 l2) (tree_join r1 r2)
  | Leaf n, Node l r => Node l r  (* Node is always larger *)
  | Node l r, Leaf n => Node l r  (* Node is always larger *)
  end.

(* Notation for tree lattice operations *)
Notation "t1 '⊓ₜ' t2" := (tree_meet t1 t2) (at level 60).
Notation "t1 '⊔ₜ' t2" := (tree_join t1 t2) (at level 65).

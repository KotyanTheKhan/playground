(* Binary tree structure *)

(* ========== Tree Data Type ========== *)

Inductive Tree :=
| Leaf : nat -> Tree
| Node : Tree -> Tree -> Tree.

(* ========== Ordering Relation ========== *)

(* Tree ordering: pointwise comparison
   - Leaves ordered by their values
   - Nodes ordered pointwise on both subtrees
   - Leaves are always less than Nodes (to make total order)
   This forms a proper lattice with meet and join operations *)
Fixpoint tree_le (t1 t2 : Tree) : Prop :=
  match t1, t2 with
  | Leaf n1, Leaf n2 => n1 <= n2
  | Leaf _, Node _ _ => True
  | Node _ _, Leaf _ => False
  | Node l1 r1, Node l2 r2 => tree_le l1 l2 /\ tree_le r1 r2
  end.

(* Notation for tree ordering *)
Notation "t1 '≤ₜ' t2" := (tree_le t1 t2) (at level 70).
Notation "t1 '<ₜ' t2" := (tree_le t1 t2 /\ ~tree_le t2 t1) (at level 70).

(* Convenient notation for tree construction *)
Notation "'leaf' n" := (Leaf n) (at level 10).
Notation "l '⟨' r '⟩'" := (Node l r) (at level 55, right associativity).

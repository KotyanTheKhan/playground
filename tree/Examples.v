(* Examples demonstrating tree poset and lattice *)
Require Import Tree.Structure.
Require Import Tree.Operations.

(* ========== Example Trees ========== *)

Definition t0 : Tree := leaf 0.
Definition t1 : Tree := leaf 1.
Definition t2 : Tree := leaf 2.
Definition t3 : Tree := (leaf 1) ⟨ (leaf 2) ⟩.
Definition t4 : Tree := (leaf 0) ⟨ (leaf 3) ⟩.

(* ========== Ordering Examples ========== *)

Example leaf_ordering_01 : t0 ≤ₜ t1.
Proof.
  unfold t0, t1, tree_le.
  repeat constructor.
Qed.

Example leaf_ordering_12 : t1 ≤ₜ t2.
Proof.
  unfold t1, t2, tree_le.
  repeat constructor.
Qed.

Example leaf_reflexive : t1 ≤ₜ t1.
Proof.
  unfold t1, tree_le.
  auto.
Qed.

(* ========== Lattice Operation Examples ========== *)

Example tree_meet_leaves : t0 ⊓ₜ t1 = t0.
Proof.
  unfold tree_meet, t0, t1; simpl.
  reflexivity.
Qed.

Example tree_join_leaves : t0 ⊔ₜ t1 = t1.
Proof.
  unfold tree_join, t0, t1; simpl.
  reflexivity.
Qed.

Example tree_meet_nodes : t3 ⊓ₜ t4 = (leaf 0) ⟨ (leaf 2) ⟩.
Proof.
  unfold tree_meet, t3, t4; simpl.
  reflexivity.
Qed.

Example tree_join_nodes : t3 ⊔ₜ t4 = (leaf 1) ⟨ (leaf 3) ⟩.
Proof.
  unfold tree_join, t3, t4; simpl.
  reflexivity.
Qed.

(* ========== Head Value Examples ========== *)

Example head_leaf : tree_head_val t1 = 1.
Proof.
  unfold tree_head_val, t1.
  reflexivity.
Qed.

Example head_node : tree_head_val t3 = 1.
Proof.
  unfold tree_head_val, t3.
  reflexivity.
Qed.

(* ========== Additional Examples with Notation ========== *)

(* Example showing direct use of notation *)
Example direct_meet : (leaf 5) ⊓ₜ (leaf 3) = leaf 3.
Proof.
  simpl. reflexivity.
Qed.

Example direct_join : (leaf 5) ⊔ₜ (leaf 3) = leaf 5.
Proof.
  simpl. reflexivity.
Qed.

Example node_meet : ((leaf 1) ⟨ (leaf 4) ⟩) ⊓ₜ ((leaf 2) ⟨ (leaf 3) ⟩) = (leaf 1) ⟨ (leaf 3) ⟩.
Proof.
  simpl. reflexivity.
Qed.

Example node_join : ((leaf 1) ⟨ (leaf 4) ⟩) ⊔ₜ ((leaf 2) ⟨ (leaf 3) ⟩) = (leaf 2) ⟨ (leaf 4) ⟩.
Proof.
  simpl. reflexivity.
Qed.

(* Example showing ordering chains *)
Example ordering_chain : (leaf 1) ≤ₜ (leaf 2) /\ (leaf 2) ≤ₜ (leaf 3).
Proof.
  split; simpl; auto.
Qed.

Example node_ordering : ((leaf 0) ⟨ (leaf 1) ⟩) ≤ₜ ((leaf 1) ⟨ (leaf 2) ⟩).
Proof.
  simpl. split; auto.
Qed.

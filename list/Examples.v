(* Examples demonstrating list poset and lattice *)
Require Import Structure.
Require Import Operations.
Require Import Instances.
Require Import Posets.PosetClasses.

(* ========== Example Lists ========== *)

Definition l0 : List := [].
Definition l1 : List := [1].
Definition l2 : List := [1; 2].
Definition l3 : List := [1; 2; 3].
Definition l4 : List := [5].
Definition l5 : List := [5; 6].

(* ========== Ordering Examples ========== *)

Example empty_le_any : l0 ≤ₗ l1.
Proof.
  unfold l0, l1, list_le, length_List, list_lex_le.
  simpl. auto.
Qed.

Example length_ordering_12 : l1 ≤ₗ l2.
Proof.
  unfold l1, l2, list_le, length_List.
  simpl. auto.
Qed.

Example length_ordering_23 : l2 ≤ₗ l3.
Proof.
  unfold l2, l3, list_le, length_List.
  simpl. auto.
Qed.

Example list_reflexive : l2 ≤ₗ l2.
Proof.
  apply poset_refl.
Qed.

(* ========== Lattice Operation Examples ========== *)

Example list_meet_empty : l0 ⊓ₗ l1 = l0.
Proof.
  unfold list_meet, l0, l1, length_List.
  reflexivity.
Qed.

Example list_join_empty : l0 ⊔ₗ l1 = l1.
Proof.
  unfold list_join, l0, l1, length_List.
  reflexivity.
Qed.

Example list_meet_12 : l1 ⊓ₗ l2 = l1.
Proof.
  unfold list_meet, l1, l2, length_List.
  reflexivity.
Qed.

Example list_join_12 : l1 ⊔ₗ l2 = l2.
Proof.
  unfold list_join, l1, l2, length_List.
  reflexivity.
Qed.

Example list_meet_same_length : l1 ⊓ₗ l4 = l1.
Proof.
  unfold list_meet, l1, l4, length_List.
  reflexivity.
Qed.

Example list_join_same_length : l1 ⊔ₗ l4 = l4.
Proof.
  unfold list_join, l1, l4, length_List.
  reflexivity.
Qed.

(* ========== Append Examples ========== *)

Example append_example : l1 ++ l1 = [1; 1].
Proof.
  unfold l1, append_List.
  reflexivity.
Qed.

Example append_nil_left : l0 ++ l2 = l2.
Proof.
  unfold l0, l2, append_List.
  reflexivity.
Qed.

(* ========== Length Examples ========== *)

Example length_empty : length_List l0 = 0.
Proof.
  unfold l0, length_List.
  reflexivity.
Qed.

Example length_three : length_List l3 = 3.
Proof.
  unfold l3, length_List.
  reflexivity.
Qed.

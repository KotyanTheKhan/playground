(* G-Counter: Grow-only Counter CRDT *)
(* A state-based CRDT that implements a monotonically increasing counter *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import EventualConsistency.StateModel.

(* ========== G-Counter Implementation ========== *)

Module GCounter.
  
  (* State: vector of natural numbers, one per replica *)
  Definition State := list nat.
  
  (* Initialize counter with n replicas, all at 0 *)
  Definition init (n : nat) : State :=
    List.repeat 0 n.
  
  (* Increment counter at replica r *)
  Fixpoint increment (state : State) (r : ReplicaId) : State :=
    match state, r with
    | [], _ => []
    | n :: rest, 0 => S n :: rest
    | n :: rest, S r' => n :: increment rest r'
    end.
  
  (* Query: sum all replica counters *)
  Fixpoint query (state : State) : nat :=
    match state with
    | [] => 0
    | n :: rest => n + query rest
    end.
  
  (* Merge: take maximum at each position *)
  Fixpoint merge (s1 s2 : State) : State :=
    match s1, s2 with
    | [], s => s
    | s, [] => s
    | n1 :: rest1, n2 :: rest2 => Nat.max n1 n2 :: merge rest1 rest2
    end.
  
  (* ========== CRDT Properties ========== *)
  
  (* Commutativity of merge *)
  Lemma merge_comm : forall s1 s2, merge s1 s2 = merge s2 s1.
  Proof.
    intros s1. induction s1 as [| n1 s1' IH]; intros s2.
    - simpl. destruct s2; reflexivity.
    - destruct s2 as [| n2 s2'].
      + simpl. reflexivity.
      + simpl. rewrite Nat.max_comm. rewrite IH. reflexivity.
  Qed.
  
  (* Associativity of merge *)
  Lemma merge_assoc : forall s1 s2 s3,
    merge (merge s1 s2) s3 = merge s1 (merge s2 s3).
  Proof.
    intros s1. induction s1 as [| n1 s1' IH]; intros s2 s3.
    - simpl. reflexivity.
    - destruct s2 as [| n2 s2']; destruct s3 as [| n3 s3'].
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. reflexivity.
      + simpl. rewrite Nat.max_assoc. rewrite IH. reflexivity.
  Qed.
  
  (* Idempotence of merge *)
  Lemma merge_idem : forall s, merge s s = s.
  Proof.
    induction s as [| n s' IH].
    - simpl. reflexivity.
    - simpl. rewrite Nat.max_id. rewrite IH. reflexivity.
  Qed.
  
  (* ========== Additional Properties ========== *)
  
  (* Monotonicity: increment increases value *)
  Lemma increment_monotonic : forall s r,
    query s <= query (increment s r).
  Proof.
    intros s. induction s as [| n s' IH]; intros r.
    - simpl. apply Nat.le_refl.
    - destruct r.
      + simpl. lia.
      + simpl. specialize (IH r). lia.
  Qed.
  
  (* Merge preserves or increases value *)
  Lemma merge_monotonic_left : forall s1 s2,
    query s1 <= query (merge s1 s2).
  Proof.
    intros s1. induction s1 as [| n1 s1' IH]; intros s2.
    - simpl. lia.
    - destruct s2 as [| n2 s2'].
      + simpl. lia.
      + simpl. specialize (IH s2'). lia.
  Qed.
  
  Lemma merge_monotonic_right : forall s1 s2,
    query s2 <= query (merge s1 s2).
  Proof.
    intros. rewrite merge_comm. apply merge_monotonic_left.
  Qed.

End GCounter.

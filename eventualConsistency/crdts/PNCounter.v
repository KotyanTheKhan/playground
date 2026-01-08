(* PN-Counter: Positive-Negative Counter CRDT *)
(* A state-based CRDT that implements a counter supporting both increment and decrement *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Require Import EventualConsistency.StateModel.
Require Import crdts.GCounter.

(* ========== PN-Counter Implementation ========== *)

Module PNCounter.
  
  (* State: pair of G-Counters (positive and negative) *)
  Record State := {
    pos : GCounter.State;
    neg : GCounter.State
  }.
  
  (* Notation for construction *)
  Notation "'⟨' p ',' n '⟩ₚₙ'" := {| pos := p; neg := n |} (at level 0).
  
  (* Initialize counter with n replicas *)
  Definition init (n : nat) : State :=
    ⟨ GCounter.init n, GCounter.init n ⟩ₚₙ.
  
  (* Increment the positive counter *)
  Definition increment (state : State) (r : ReplicaId) : State :=
    ⟨ GCounter.increment (pos state) r, neg state ⟩ₚₙ.
  
  (* Increment the negative counter (decrement) *)
  Definition decrement (state : State) (r : ReplicaId) : State :=
    ⟨ pos state, GCounter.increment (neg state) r ⟩ₚₙ.
  
  (* Query: difference between positive and negative *)
  Definition query (state : State) : nat :=
    GCounter.query (pos state) - GCounter.query (neg state).
  
  (* Merge both counters *)
  Definition merge (s1 s2 : State) : State :=
    ⟨ GCounter.merge (pos s1) (pos s2),
      GCounter.merge (neg s1) (neg s2) ⟩ₚₙ.
  
  (* ========== CRDT Properties ========== *)
  
  (* Commutativity *)
  Lemma merge_comm : forall s1 s2, merge s1 s2 = merge s2 s1.
  Proof.
    intros s1 s2.
    unfold merge.
    rewrite GCounter.merge_comm with (s1 := pos s1).
    rewrite GCounter.merge_comm with (s1 := neg s1).
    reflexivity.
  Qed.
  
  (* Associativity *)
  Lemma merge_assoc : forall s1 s2 s3,
    merge (merge s1 s2) s3 = merge s1 (merge s2 s3).
  Proof.
    intros s1 s2 s3.
    unfold merge.
    simpl.
    rewrite GCounter.merge_assoc.
    rewrite GCounter.merge_assoc.
    reflexivity.
  Qed.
  
  (* Idempotence *)
  Lemma merge_idem : forall s, merge s s = s.
  Proof.
    intros s.
    unfold merge.
    rewrite GCounter.merge_idem.
    rewrite GCounter.merge_idem.
    destruct s. reflexivity.
  Qed.

End PNCounter.

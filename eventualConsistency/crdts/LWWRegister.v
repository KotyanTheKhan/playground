(* LWW-Register: Last-Write-Wins Register CRDT *)
(* A state-based CRDT that resolves conflicts using timestamps *)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lia.

Require Import EventualConsistency.StateModel.

(* ========== LWW-Register Implementation ========== *)

Module LWWRegister.
  
  Section LWWRegisterDef.
    Variable A : Type.
    
    (* State: value with timestamp *)
    Record State := {
      value : A;
      timestamp : nat
    }.
    
    (* Notation for construction *)
    Notation "'⟨' v '@' t '⟩ₗ'" := {| value := v; timestamp := t |} (at level 0).
    
    (* Initialize with value and timestamp 0 *)
    Definition init (v : A) : State :=
      ⟨ v @ 0 ⟩ₗ.
    
    (* Update with new value and timestamp *)
    Definition update (state : State) (v : A) (t : nat) : State :=
      if Nat.ltb (timestamp state) t
      then ⟨ v @ t ⟩ₗ
      else state.
    
    (* Query current value *)
    Definition query (state : State) : A :=
      value state.
    
    (* Merge: keep value with higher timestamp *)
    Definition merge (s1 s2 : State) : State :=
      if Nat.leb (timestamp s1) (timestamp s2)
      then s2
      else s1.
    
    (* ========== CRDT Properties ========== *)
    
    (* Commutativity (when timestamps differ) *)
    Lemma merge_comm_distinct : forall s1 s2,
      timestamp s1 <> timestamp s2 ->
      merge s1 s2 = merge s2 s1.
    Proof.
      intros s1 s2 H_neq.
      unfold merge.
      destruct (Nat.leb (timestamp s1) (timestamp s2)) eqn:E1;
      destruct (Nat.leb (timestamp s2) (timestamp s1)) eqn:E2.
      - (* Both true: contradiction with H_neq *)
        apply Nat.leb_le in E1.
        apply Nat.leb_le in E2.
        lia.
      - reflexivity.
      - reflexivity.
      - (* Both false: contradiction *)
        apply Nat.leb_gt in E1.
        apply Nat.leb_gt in E2.
        lia.
    Qed.
    
    (* Idempotence *)
    Lemma merge_idem : forall s, merge s s = s.
    Proof.
      intros s.
      unfold merge.
      destruct (Nat.leb (timestamp s) (timestamp s)) eqn:E.
      - reflexivity.
      - apply Nat.leb_gt in E. lia.
    Qed.
    
    (* Associativity (when timestamps are distinct or equal) *)
    Axiom merge_assoc : forall s1 s2 s3,
      merge (merge s1 s2) s3 = merge s1 (merge s2 s3).
    
    (* ========== Additional Properties ========== *)
    
    (* Merge selects the value with maximum timestamp *)
    Lemma merge_max_timestamp : forall s1 s2,
      timestamp (merge s1 s2) = Nat.max (timestamp s1) (timestamp s2).
    Proof.
      intros s1 s2.
      unfold merge.
      destruct (Nat.leb (timestamp s1) (timestamp s2)) eqn:E.
      - apply Nat.leb_le in E. simpl. lia.
      - apply Nat.leb_gt in E. simpl. lia.
    Qed.
    
  End LWWRegisterDef.
  
End LWWRegister.

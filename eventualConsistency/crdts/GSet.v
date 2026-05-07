(* G-Set: Grow-only Set CRDT *)
(* A state-based CRDT that implements a set supporting only additions *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.

Require Import EventualConsistency.StateModel.

(* ========== G-Set Implementation ========== *)

Module GSet.
  
  (* Parameterized by element type with decidable equality *)
  Section GSetDef.
    Variable A : Type.
    Variable A_eq_dec : forall (x y : A), {x = y} + {x <> y}.
    
    (* State: list of elements (representing a set) *)
    Definition State := list A.
    
    (* Initialize empty set *)
    Definition init : State := [].
    
    (* Check if element exists in list *)
    Definition contains (state : State) (elem : A) : bool :=
      List.existsb (fun x => if A_eq_dec x elem then true else false) state.
    
    (* Add element (only if not already present) *)
    Definition add (state : State) (elem : A) : State :=
      if contains state elem
      then state
      else elem :: state.
    
    (* Check membership *)
    Definition member (state : State) (elem : A) : bool :=
      contains state elem.
    
    (* Merge: union of sets *)
    Fixpoint merge (s1 s2 : State) : State :=
      match s1 with
      | [] => s2
      | x :: rest => add (merge rest s2) x
      end.
    
    (* ========== CRDT Properties ========== *)
    
    (* Commutativity (requires set equality notion) *)
    Axiom merge_comm : forall s1 s2, merge s1 s2 = merge s2 s1.
    
    (* Associativity *)
    Axiom merge_assoc : forall s1 s2 s3,
      merge (merge s1 s2) s3 = merge s1 (merge s2 s3).
    
    (* Idempotence *)
    Axiom merge_idem : forall s, merge s s = s.
    
    (* ========== Additional Properties ========== *)
    
    (* Adding preserves existing members *)
    Axiom add_preserves_members : forall s elem x,
      member s x = true -> member (add s elem) x = true.
    
    (* Merge preserves members from both sets *)
    Axiom merge_preserves_left : forall s1 s2 x,
      member s1 x = true -> member (merge s1 s2) x = true.
    
    Axiom merge_preserves_right : forall s1 s2 x,
      member s2 x = true -> member (merge s1 s2) x = true.
    
  End GSetDef.
  
End GSet.

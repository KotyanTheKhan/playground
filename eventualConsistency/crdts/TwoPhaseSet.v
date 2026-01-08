(* 2P-Set: Two-Phase Set CRDT *)
(* A state-based CRDT that supports add and remove, but elements cannot be re-added *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.

Require Import EventualConsistency.StateModel.
Require Import crdts.GSet.

(* ========== 2P-Set Implementation ========== *)

Module TwoPhaseSet.
  
  Section TwoPhaseSetDef.
    Variable A : Type.
    Variable A_eq_dec : forall (x y : A), {x = y} + {x <> y}.
    
    (* State: pair of G-Sets (added and removed) *)
    Record State := {
      added : GSet.State A;
      removed : GSet.State A
    }.
    
    (* Notation for construction *)
    Notation "'⟨' a ',' r '⟩₂ₚ'" := {| added := a; removed := r |} (at level 0).
    
    (* Initialize empty set *)
    Definition init : State :=
      ⟨ @GSet.init A, @GSet.init A ⟩₂ₚ.
    
    (* Add element to added set *)
    Definition add (state : State) (elem : A) : State :=
      ⟨ GSet.add A A_eq_dec (added state) elem, removed state ⟩₂ₚ.
    
    (* Add element to removed set *)
    Definition remove (state : State) (elem : A) : State :=
      ⟨ added state, GSet.add A A_eq_dec (removed state) elem ⟩₂ₚ.
    
    (* Check membership: in added but not in removed *)
    Definition member (state : State) (elem : A) : bool :=
      andb (GSet.member A A_eq_dec (added state) elem)
           (negb (GSet.member A A_eq_dec (removed state) elem)).
    
    (* Merge both sets *)
    Definition merge (s1 s2 : State) : State :=
      ⟨ GSet.merge A A_eq_dec (added s1) (added s2),
        GSet.merge A A_eq_dec (removed s1) (removed s2) ⟩₂ₚ.
    
    (* ========== CRDT Properties ========== *)
    
    (* Commutativity *)
    Lemma merge_comm : forall s1 s2, merge s1 s2 = merge s2 s1.
    Proof.
      intros s1 s2.
      unfold merge.
      rewrite (GSet.merge_comm A A_eq_dec (added s1) (added s2)).
      rewrite (GSet.merge_comm A A_eq_dec (removed s1) (removed s2)).
      reflexivity.
    Qed.
    
    (* Associativity *)
    Lemma merge_assoc : forall s1 s2 s3,
      merge (merge s1 s2) s3 = merge s1 (merge s2 s3).
    Proof.
      intros s1 s2 s3.
      unfold merge.
      simpl.
      rewrite GSet.merge_assoc.
      rewrite GSet.merge_assoc.
      reflexivity.
    Qed.
    
    (* Idempotence *)
    Lemma merge_idem : forall s, merge s s = s.
    Proof.
      intros s.
      unfold merge.
      rewrite GSet.merge_idem.
      rewrite GSet.merge_idem.
      destruct s. reflexivity.
    Qed.
    
    (* ========== Semantic Properties ========== *)
    
    (* Once removed, element stays removed after merge *)
    Axiom remove_wins : forall s1 s2 elem,
      GSet.member A A_eq_dec (removed s1) elem = true ->
      member (merge s1 s2) elem = false.
    
  End TwoPhaseSetDef.
  
End TwoPhaseSet.

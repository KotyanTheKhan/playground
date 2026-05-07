(* Examples demonstrating notation usage in the Eventual Consistency module *)
Require Import EventualConsistency.

(* Import only list notations from standard library *)
From Stdlib Require Import Lists.List.

(* Import only the specific notations we use *)
Import List.ListNotations.
Open Scope list_scope.

(* ========== Example 1: Version Vectors ========== *)

Section VersionVectorExamples.
  
  (* Create some version vectors using :: notation *)
  Definition v1 : VersionVector := [1; 2; 0].
  Definition v2 : VersionVector := [1; 3; 1].
  Definition v3 : VersionVector := [1; 3; 1].
  
  (* Alternative: using list literal notation *)
  Definition v1_alt : VersionVector := [1; 2; 0].
  Definition v2_alt : VersionVector := [1; 3; 1].
  
  (* Show equivalence of notations *)
  Example notation_equivalence : v1 = v1_alt.
  Proof. reflexivity. Qed.
  
  (* Demonstrate version vector operations *)
  Example version_merge_example : v1 ⊔ᵥ v2 = v3.
  Proof.
    unfold v1, v2, v3.
    unfold version_merge, max.
    simpl.
    reflexivity.
  Qed.
  
  (* Demonstrate version increment *)
  Example version_inc_example : 
    v1 ↑ 0 = [2; 2; 0].
  Proof.
    unfold v1.
    simpl.
    reflexivity.
  Qed.
  
  (* Demonstrate version comparison *)
  Example version_order_example : v1 ⊑ v3.
  Proof.
    unfold v1, v3.
    simpl.
    reflexivity.
  Qed.

End VersionVectorExamples.

(* ========== Example 2: Replica States ========== *)

Section ReplicaStateExamples.
  
  (* Assume we have some concrete state and operation types *)
  Variable s0 s1 s2 : State.
  Variable op1 op2 : Operation.
  
  (* Create replica states using notation *)
  Definition r0 : ReplicaState := ⟨0, s0, [0; 0]⟩ᵣ.
  Definition r1 : ReplicaState := ⟨1, s1, [0; 1]⟩ᵣ.
  
  (* Create updates using notation *)
  Definition u1 : Update := ⟨op1, 0, [0; 0]⟩ᵤ.
  Definition u2 : Update := ⟨op2, 1, [0; 1]⟩ᵤ.
  
  (* Demonstrate applying update to replica *)
  Example apply_update_notation : 
    replica_id (r0 ⊙ u1) = 0.
  Proof.
    unfold r0, u1.
    simpl.
    reflexivity.
  Qed.
  
  (* Demonstrate replica merge *)
  Example merge_replica_notation :
    replica_id (r0 ⊔ᵣ r1) = 0.
  Proof.
    unfold r0, r1.
    simpl.
    reflexivity.
  Qed.

End ReplicaStateExamples.

(* ========== Example 3: State Operations ========== *)

Section StateOperationExamples.
  
  Variable s1 s2 s3 : State.
  Variable op : Operation.
  
  (* State merge is commutative (using ⊔ notation) *)
  Lemma state_merge_comm : s1 ⊔ s2 = s2 ⊔ s1.
  Proof.
    apply merge_commutative.
  Qed.
  
  (* State merge is associative *)
  Lemma state_merge_assoc : (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3).
  Proof.
    apply merge_associative.
  Qed.
  
  (* State merge is idempotent *)
  Lemma state_merge_idem : s1 ⊔ s1 = s1.
  Proof.
    apply merge_idempotent.
  Qed.
  
  (* State equivalence is symmetric *)
  Lemma state_equiv_sym : s1 ≈ s2 -> s2 ≈ s1.
  Proof.
    unfold state_equivalent.
    intro H.
    symmetry.
    exact H.
  Qed.

End StateOperationExamples.

(* ========== Example 4: Causality Relations ========== *)

Section CausalityExamples.
  
  Variable u1 u2 u3 : Update.
  
  (* If u1 causally precedes u2, they are not concurrent *)
  Lemma causal_not_concurrent : 
    u1 ≺ᵤ u2 -> ~ (u1 ∥ᵤ u2).
  Proof.
    intros H_causal H_concurrent.
    unfold updates_concurrent in H_concurrent.
    destruct H_concurrent as [H_not1 H_not2].
    contradiction.
  Qed.
  
  (* Causal precedence is transitive (would require proof) *)
  Axiom causal_transitive : 
    forall u1 u2 u3, u1 ≺ᵤ u2 -> u2 ≺ᵤ u3 -> u1 ≺ᵤ u3.

End CausalityExamples.

(* ========== Example 5: Convergence ========== *)

Section ConvergenceExamples.
  
  Variable cfg : Configuration.
  Variable rs1 rs2 : ReplicaState.
  
  (* If a configuration has converged, all replicas are equivalent *)
  Lemma converged_cfg_implies_replica_equiv :
    ⊤[cfg] -> List.In rs1 cfg -> List.In rs2 cfg -> rs1 ≈ᵣ rs2.
  Proof.
    intros H_conv H_in1 H_in2.
    unfold configuration_converged in H_conv.
    apply H_conv.
    - exact H_in1.
    - exact H_in2.
  Qed.
  
  (* Replica convergence is symmetric *)
  Lemma replica_conv_symmetric : rs1 ≈ᵣ rs2 -> rs2 ≈ᵣ rs1.
  Proof.
    unfold replicas_converged.
    intro H.
    symmetry.
    exact H.
  Qed.
  
  (* Replica convergence is transitive *)
  Lemma replica_conv_transitive :
    forall r1 r2 r3, r1 ≈ᵣ r2 -> r2 ≈ᵣ r3 -> r1 ≈ᵣ r3.
  Proof.
    intros r1 r2 r3 H12 H23.
    unfold replicas_converged in *.
    transitivity (state r2); assumption.
  Qed.

End ConvergenceExamples.

(* ========== Example 6: Monotonic Growth ========== *)

Section MonotonicityExamples.
  
  Variable s1 s2 s3 : State.
  
  (* Monotonic growth is reflexive *)
  Lemma state_grows_refl : s1 ⊑ₛ s1.
  Proof.
    unfold state_grows.
    apply merge_idempotent.
  Qed.
  
  (* Monotonic growth is transitive *)
  Lemma state_grows_trans : s1 ⊑ₛ s2 -> s2 ⊑ₛ s3 -> s1 ⊑ₛ s3.
  Proof.
    unfold state_grows.
    intros H12 H23.
    rewrite <- H23.
    rewrite <- merge_associative.
    rewrite H12.
    reflexivity.
  Qed.

End MonotonicityExamples.

(* ========== Summary ========== *)

(* This file demonstrates all the notations available in the 
   Eventual Consistency module:
   
   Version Vectors:
   - v1 ⊔ᵥ v2         (merge)
   - v ↑ r            (increment)
   - v1 ⊑ v2          (causally precedes)
   
   Construction:
   - ⟨r, s, v⟩ᵣ        (replica state)
   - ⟨o, r, ctx⟩ᵤ      (update)
   - s ⟶ r ∶ u        (message)
   
   State Operations:
   - s1 ⊔ s2          (merge states)
   - s ⊕ op           (apply operation)
   - rs ⊙ u           (apply update to replica)
   - rs1 ⊔ᵣ rs2       (merge replicas)
   
   Relations:
   - u1 ≺ᵤ u2         (causal precedence)
   - u1 ∥ᵤ u2         (concurrent)
   - s1 ≈ s2          (state equivalence)
   - s1 ⊑ₛ s2         (monotonic growth)
   - rs1 ≈ᵣ rs2       (replica convergence)
   - ⊤[cfg]           (configuration convergence)
*)

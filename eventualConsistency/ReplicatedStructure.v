(* Replicated Data Structure Properties *)
Require Import StateModel.

(* ========== Merge and Apply Operations ========== *)

(* A merge function combines two states *)
Parameter merge : State -> State -> State.

(* Notation for merge (join/LUB) *)
Notation "s1 '⊔' s2" := (merge s1 s2) (at level 50, left associativity).

(* An apply function applies an operation to a state *)
Parameter apply : Operation -> State -> State.

(* Notation for applying operations *)
Notation "s '⊕' op" := (apply op s) (at level 45, left associativity).

(* ========== Consistency Axioms ========== *)

(* These properties are required for eventual consistency *)

(* 1. Commutativity: merge order doesn't matter *)
Axiom merge_commutative : forall s1 s2 : State,
  s1 ⊔ s2 = s2 ⊔ s1.

(* 2. Associativity: grouping of merges doesn't matter *)
Axiom merge_associative : forall s1 s2 s3 : State,
  (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3).

(* 3. Idempotency: merging a state with itself gives the same state *)
Axiom merge_idempotent : forall s : State,
  s ⊔ s = s.

(* 4. Monotonicity: applying updates preserves causality *)
(* Strengthened version: applying an operation creates a state that subsumes the original *)
Axiom apply_preserves_merge : forall (op : Operation) (s : State),
  (s ⊕ op) ⊔ s = (s ⊕ op).

(* ========== Derived Properties ========== *)

(* The merge function forms a semilattice *)
Lemma merge_semilattice : forall s1 s2 s3 : State,
  (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3) /\
  s1 ⊔ s2 = s2 ⊔ s1 /\
  s1 ⊔ s1 = s1.
Proof.
  intros. split.
  - apply merge_associative.
  - split.
    + apply merge_commutative.
    + apply merge_idempotent.
Qed.

(* Merging is a least upper bound *)
Lemma merge_lub : forall s1 s2 : State,
  (s1 ⊔ s2) ⊔ s1 = s1 ⊔ s2 /\
  (s1 ⊔ s2) ⊔ s2 = s1 ⊔ s2.
Proof.
  intros s1 s2. split.
  - (* (s1 ⊔ s2) ⊔ s1 = s1 ⊔ s2 *)
    assert (H: s1 ⊔ (s1 ⊔ s2) = s1 ⊔ s2).
    { rewrite <- (merge_associative s1 s1 s2).
      rewrite merge_idempotent.
      reflexivity. }
    rewrite (merge_commutative (s1 ⊔ s2) s1).
    exact H.
  - (* (s1 ⊔ s2) ⊔ s2 = s1 ⊔ s2 *)
    (* Use merge_associative: (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) *)
    (* Here: (s1 ⊔ s2) ⊔ s2 = s1 ⊔ (s2 ⊔ s2) *)
    transitivity (s1 ⊔ (s2 ⊔ s2)).
    + apply merge_associative.
    + rewrite merge_idempotent.
      reflexivity.
Qed.

(* ========== Helper: Replica State Operations ========== *)

(* Apply an update to a replica state *)
Definition apply_update (rs : ReplicaState) (u : Update) : ReplicaState :=
  {| replica_id := replica_id rs;
     state := apply (op u) (state rs);
     version := version_merge (version rs) (causal_context u)
  |}.

(* Notation for applying update to replica *)
Notation "rs '⊙' u" := (apply_update rs u) (at level 45, left associativity).

(* Merge two replica states *)
Definition merge_replica_states (rs1 rs2 : ReplicaState) : ReplicaState :=
  {| replica_id := replica_id rs1;
     state := merge (state rs1) (state rs2);
     version := version_merge (version rs1) (version rs2)
  |}.

(* Notation for merging replica states *)
Notation "rs1 '⊔ᵣ' rs2" := (merge_replica_states rs1 rs2) (at level 50, left associativity).

(* ========== Notation Summary ========== *)

(*
   State Operations:
   - s1 ⊔ s2          : Merge (join) of states s1 and s2
   - s ⊕ op           : Apply operation op to state s
   
   Replica Operations:
   - rs ⊙ u           : Apply update u to replica state rs
   - rs1 ⊔ᵣ rs2       : Merge replica states rs1 and rs2
   
   Consistency Properties:
   - Commutativity: s1 ⊔ s2 = s2 ⊔ s1
   - Associativity: (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3)
   - Idempotency: s ⊔ s = s
*)

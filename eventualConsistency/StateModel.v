(* State and Replica Model for Eventual Consistency *)

(* Import standard library operations *)
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import PeanoNat.
Import ListNotations.

(* ========== Basic Types ========== *)

(* Replica identifier *)
Definition ReplicaId := nat.

(* State: generic type parameter for replica state *)
Parameter State : Type.

(* Operation: represents an update operation *)
Parameter Operation : Type.

(* Version Vector: logical timestamp for each replica *)
Definition VersionVector := list nat.

(* Notation for version vectors *)
Notation "'⟦' v '⟧'" := v (at level 0, only parsing).

(* State at a replica with its version vector *)
Record ReplicaState := {
  replica_id : ReplicaId;
  state : State;
  version : VersionVector
}.

(* Notation for replica state construction *)
Notation "'⟨' r ',' s ',' v '⟩ᵣ'" := 
  {| replica_id := r; state := s; version := v |} (at level 0).

(* Update: an operation with its causal context *)
Record Update := {
  op : Operation;
  origin : ReplicaId;
  causal_context : VersionVector
}.

(* Notation for update construction *)
Notation "'⟨' o ',' r ',' ctx '⟩ᵤ'" := 
  {| op := o; origin := r; causal_context := ctx |} (at level 0).

(* Message: update sent between replicas *)
Record UpdateMessage := {
  update : Update;
  sender : ReplicaId;
  receiver : ReplicaId
}.

(* Notation for message construction *)
Notation "s '⟶' r '∶' u" := 
  {| update := u; sender := s; receiver := r |} (at level 80, right associativity).

(* System state: collection of replica states *)
Definition SystemState := list ReplicaState.

(* Update history: sequence of updates delivered to the system *)
Definition UpdateHistory := list Update.

(* ========== Helper Functions ========== *)

(* Use standard library operations:
   - List.In for list membership
   - Nat.eqb for nat equality
   - Nat.leb for nat comparison
   - Nat.max for maximum
*)

(* ========== Version Vector Operations ========== *)

(* Compare version vectors: v1 ≤ v2 means v1[i] ≤ v2[i] for all i *)
Fixpoint version_leb (v1 v2 : VersionVector) : bool :=
  match v1, v2 with
  | [], _ => true
  | _, [] => false
  | n1 :: v1', n2 :: v2' => 
      if Nat.leb n1 n2 then version_leb v1' v2'
      else false
  end.

(* Notation for version vector comparison *)
Notation "v1 '⊑' v2" := (version_leb v1 v2 = true) (at level 70).

(* Merge version vectors: take max at each position *)
Fixpoint version_merge (v1 v2 : VersionVector) : VersionVector :=
  match v1, v2 with
  | [], v => v
  | v, [] => v
  | n1 :: v1', n2 :: v2' => 
      Nat.max n1 n2 :: version_merge v1' v2'
  end.

(* Notation for version vector merge (join) *)
Notation "v1 '⊔ᵥ' v2" := (version_merge v1 v2) (at level 50, left associativity).

(* Increment version at a specific replica *)
Fixpoint version_inc (v : VersionVector) (rid : ReplicaId) : VersionVector :=
  match v, rid with
  | [], _ => []
  | n :: v', 0 => S n :: v'
  | n :: v', S rid' => n :: version_inc v' rid'
  end.

(* Notation for version increment *)
Notation "v '↑' r" := (version_inc v r) (at level 40).

(* ========== Causality Relations ========== *)

(* Update u1 causally precedes u2 if u1's version ≤ u2's causal context *)
Definition causally_precedes (u1 u2 : Update) : Prop :=
  version_leb (causal_context u1) (causal_context u2) = true.

(* Two updates are concurrent if neither causally precedes the other *)
Definition updates_concurrent (u1 u2 : Update) : Prop :=
  ~ causally_precedes u1 u2 /\ ~ causally_precedes u2 u1.

(* Notation for causality *)
Notation "u1 '≺ᵤ' u2" := (causally_precedes u1 u2) (at level 70).
Notation "u1 '∥ᵤ' u2" := (updates_concurrent u1 u2) (at level 70).

(* ========== Notation Summary ========== *)

(*
   Replica States:
   - ⟨r, s, v⟩ᵣ        : Replica with id r, state s, version v
   
   Updates:
   - ⟨o, r, ctx⟩ᵤ      : Update with operation o, from replica r, with context ctx
   
   Messages:
   - s ⟶ r ∶ u        : Message from replica s to r containing update u
   
   Version Vectors:
   - v1 ⊑ v2          : Version v1 causally precedes v2 (component-wise ≤)
   - v1 ⊔ᵥ v2         : Merge (join) of version vectors v1 and v2
   - v ↑ r            : Increment version v at replica r
   
   Causality:
   - u1 ≺ᵤ u2         : Update u1 causally precedes u2
   - u1 ∥ᵤ u2         : Updates u1 and u2 are concurrent
*)

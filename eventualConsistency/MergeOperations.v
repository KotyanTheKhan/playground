(* Merge operations and system evolution *)
Require Import StateModel.
Require Import ReplicatedStructure.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ========== System Evolution ========== *)

(* A system configuration: set of replica states *)
Definition Configuration := SystemState.

(* Initial configuration: all replicas have the same initial state *)
Parameter initial_state : State.
Parameter initial_version : VersionVector.

Definition initial_configuration (n : nat) : Configuration :=
  let fix init_replicas (k : nat) : list ReplicaState :=
    match k with
    | 0 => []
    | S k' => ⟨k', initial_state, initial_version⟩ᵣ :: init_replicas k'
    end
  in init_replicas n.

(* Key property: all replicas in initial_configuration have initial_state *)
Lemma initial_configuration_all_same_state : forall n rs,
  In rs (initial_configuration n) ->
  state rs = initial_state.
Proof.
  intros n. induction n as [|n' IH]; intros rs H_in.
  - (* Base case: n = 0 *)
    simpl in H_in. contradiction.
  - (* Inductive case: n = S n' *)
    simpl in H_in.
    destruct H_in as [H_eq | H_in'].
    + (* rs is the head element *)
      subst rs. simpl. reflexivity.
    + (* rs is in the tail *)
      apply IH. exact H_in'.
Qed.

(* ========== Update Delivery ========== *)

(* A replica delivers an update *)
Definition deliver_update (cfg : Configuration) (rid : ReplicaId) (u : Update) : Configuration :=
  let fix deliver_to_replica (replicas : list ReplicaState) : list ReplicaState :=
    match replicas with
    | [] => []
    | rs :: rest =>
        if Nat.eqb (replica_id rs) rid
        then apply_update rs u :: rest
        else rs :: deliver_to_replica rest
    end
  in deliver_to_replica cfg.

(* All replicas deliver all updates (in any order) *)
Fixpoint deliver_all_updates (cfg : Configuration) (updates : list Update) : Configuration :=
  match cfg with
  | [] => []
  | rs :: rest =>
      let fix apply_all (state : ReplicaState) (us : list Update) : ReplicaState :=
        match us with
        | [] => state
        | u :: us' => apply_all (apply_update state u) us'
        end
      in apply_all rs updates :: deliver_all_updates rest updates
  end.

(* ========== System Quiescence ========== *)

(* A system is quiescent if all replicas have received all updates *)
Definition is_quiescent (cfg : Configuration) (updates : UpdateHistory) : Prop :=
  forall rs, In rs cfg ->
    forall u, In u updates ->
      u ≺ᵤ ⟨op u, origin u, version rs⟩ᵤ.

(* ========== Convergence Properties ========== *)

(* Two states are equivalent if they can merge to the same state *)
Definition state_equivalent (s1 s2 : State) : Prop :=
  s1 ⊔ s2 = s2 ⊔ s1.

(* Notation for state equivalence *)
Notation "s1 '≈' s2" := (state_equivalent s1 s2) (at level 70).

(* Two replicas have converged if they have the same state *)
Definition replicas_converged (rs1 rs2 : ReplicaState) : Prop :=
  state rs1 = state rs2.

(* Notation for replica convergence *)
Notation "rs1 '≈ᵣ' rs2" := (replicas_converged rs1 rs2) (at level 70).

(* A configuration has converged if all replicas have the same state *)
Definition configuration_converged (cfg : Configuration) : Prop :=
  forall rs1 rs2, List.In rs1 cfg -> List.In rs2 cfg -> replicas_converged rs1 rs2.

(* Notation for configuration convergence *)
Notation "'⊤[' cfg ']'" := (configuration_converged cfg) (at level 0).

(* ========== Merge Completeness ========== *)

(* Given a set of updates, compute the merged state *)
Fixpoint apply_updates_to_state (s : State) (updates : list Update) : State :=
  match updates with
  | [] => s
  | u :: us => apply_updates_to_state (s ⊕ op u) us
  end.

(* Merge all replica states in a configuration *)
Fixpoint merge_all_states (cfg : Configuration) (default : State) : State :=
  match cfg with
  | [] => default
  | rs :: rest => state rs ⊔ merge_all_states rest default
  end.

(* The merged state is independent of the order *)
Lemma merge_all_states_order_independent : forall rs1 rs2 cfg default,
  merge_all_states (rs1 :: rs2 :: cfg) default =
  merge_all_states (rs2 :: rs1 :: cfg) default.
Proof.
  intros rs1 rs2 cfg default.
  simpl.
  (* LHS: (state rs1) ⊔ ((state rs2) ⊔ merge_all_states cfg default) *)
  (* RHS: (state rs2) ⊔ ((state rs1) ⊔ merge_all_states cfg default) *)
  rewrite <- merge_associative.
  rewrite (merge_commutative (state rs1) (state rs2)).
  rewrite merge_associative.
  reflexivity.
Qed.

(* ========== Notation Summary ========== *)

(*
   Convergence:
   - s1 ≈ s2          : States s1 and s2 are equivalent
   - rs1 ≈ᵣ rs2       : Replicas rs1 and rs2 have converged
   - ⊤[cfg]           : Configuration cfg has converged (all replicas agree)
   
   System State:
   - Configuration    : Set of replica states in the system
   - UpdateHistory    : Sequence of updates delivered
*)

(* Event and Message structures for distributed systems *)
Require Import Arith.

(* ========== Basic Types ========== *)

(* Process identifier *)
Definition ProcessId := nat.

(* Logical clock (Lamport timestamp) *)
Definition LogicalClock := nat.

(* Event in a distributed system *)
Record Event := {
  process : ProcessId;
  clock : LogicalClock
}.

(* Notation for event construction *)
Notation "'⟨' p ',' c '⟩'" := {| process := p; clock := c |} (at level 0).

(* Message: sender event and receiver event *)
Record Message := {
  send_event : Event;
  recv_event : Event;
  clock_lt : clock send_event < clock recv_event
}.

(* Notation for message construction *)
(* Note: This notation now requires a proof term, so it's less convenient to use directly without automation or explicit proofs *)
Notation "e1 '→ₘ' e2" := (Build_Message e1 e2) (at level 80).

(* A history is a list of messages representing the communication pattern *)
Definition History := list Message.

(* ========== Helper Functions ========== *)

(* Helper: membership in a list *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | cons y l' => y = x \/ In x l'
  end.

(* Helper: decidable equality for nat *)
Fixpoint nat_eqb (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', S m' => nat_eqb n' m'
  | _, _ => false
  end.

(* Helper: less-than-or-equal for nat *)
Fixpoint nat_leb (n m : nat) : bool :=
  match n, m with
  | 0, _ => true
  | S _, 0 => false
  | S n', S m' => nat_leb n' m'
  end.

(* ========== Lemmas ========== *)

(* Messages connect distinct events - an event cannot send a message to itself.
   This is a fundamental property of causality in distributed systems. *)
Lemma message_connects_distinct_events : forall m,
  send_event m <> recv_event m.
Proof.
  intros m H.
  (* If send_event m = recv_event m, then their clocks must be equal *)
  assert (Hclk: clock (send_event m) = clock (recv_event m)).
  { rewrite H. reflexivity. }
  (* But we know clock (send_event m) < clock (recv_event m) *)
  pose proof (clock_lt m) as Hlt.
  (* This is a contradiction *)
  rewrite Hclk in Hlt.
  apply Nat.lt_irrefl in Hlt.
  assumption.
Qed.

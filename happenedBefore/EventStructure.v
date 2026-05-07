(* Event and Message structures for distributed systems *)
Require Import Arith.

(* ========== Basic Types ========== *)

(* Process identifier *)
Definition ProcessId := nat.

(* Event in a distributed system *)
Record Event := {
  process : ProcessId;
  index : nat
}.

(* Notation for event construction *)
Notation "'⟨' p ',' i '⟩'" := {| process := p; index := i |} (at level 0).

(* Message: sender event and receiver event *)
Record Message := {
  send_event : Event;
  recv_event : Event
}.

(* Notation for message construction *)
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



(* Happened-before relation and causality *)
Require Import EventStructure.
Require Import Lia.

(* ========== Happened-Before Relation ========== *)

(* Helper: direct message causality *)
Definition message_link (h : History) (e1 e2 : Event) : Prop :=
  exists m, In m h /\ send_event m = e1 /\ recv_event m = e2.

(* Happened-before relation: reflexive-transitive closure of
   message causality *)
Inductive happened_before (h : History) : Event -> Event -> Prop :=
  | hb_refl : forall e, happened_before h e e
  | hb_message : forall e1 e2,
      message_link h e1 e2 ->
      happened_before h e1 e2
  | hb_trans : forall e1 e2 e3,
      happened_before h e1 e2 ->
      happened_before h e2 e3 ->
      happened_before h e1 e3.

(* Strict happened-before relation: transitive closure of message causality *)
Inductive strict_happened_before (h : History) : Event -> Event -> Prop :=
  | shb_message : forall e1 e2,
      message_link h e1 e2 ->
      strict_happened_before h e1 e2
  | shb_trans : forall e1 e2 e3,
      strict_happened_before h e1 e2 ->
      strict_happened_before h e2 e3 ->
      strict_happened_before h e1 e3.

(* Notation for happened-before *)
Notation "e1 '≺[' h ']' e2" := (happened_before h e1 e2) (at level 70).
Notation "e1 '≺' e2" := (happened_before nil e1 e2) (at level 70).

(* Notation for strict happened-before *)
Notation "e1 '≺+[' h ']' e2" := (strict_happened_before h e1 e2) (at level 70).

(* Two events are concurrent if neither happened before the other *)
Definition concurrent (h : History) (e1 e2 : Event) : Prop :=
  ~ happened_before h e1 e2 /\ ~ happened_before h e2 e1.

(* Notation for concurrent events *)
Notation "e1 '∥[' h ']' e2" := (concurrent h e1 e2) (at level 70).
Notation "e1 '∥' e2" := (concurrent nil e1 e2) (at level 70).

(* IsAcyclic Definition: No event strictly happens before itself *)
Definition IsAcyclic (h : History) : Prop :=
  forall e, ~ strict_happened_before h e e.

(* ========== Lemmas for proving acyclicity ========== *)

(* Lemma 1: same_process_before is irreflexive *)
(* Lemmas for proving acyclicity relied on clocks and local ordering.
   With the removal of local clocks/indices, we cannot prove global acyclicity
   without additional constraints on the History. *)

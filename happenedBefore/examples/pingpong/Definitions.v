From HappenedBefore Require Import EventStructure.
From Stdlib Require Import Arith Lia Bool PeanoNat.

(**
  Event layout, messages, and transactions for the alternating symmetric
  ping-pong protocol parameterized by gap sizes GAP_0 and GAP_1.
*)

Section PingPongParameters.

  Variable GAP_0 : nat.
  Variable GAP_1 : nat.

  (* ── Event layout ──────────────────────────────────────────────────────── *)

  (** Each process allocates (2 + GAP) event indices per cycle:
        index 0   : first interaction event (send Ping / recv Ping)
        index 1   : second interaction event (recv Pong / send Pong)
        index 2.. : internal gap events *)
  Definition p0_events_per_cycle : nat := 2 + GAP_0.
  Definition p1_events_per_cycle : nat := 2 + GAP_1.

  (** First event index on each process for cycle i. *)
  Definition p0_base_index (i : nat) : nat := i * p0_events_per_cycle.
  Definition p1_base_index (i : nat) : nat := i * p1_events_per_cycle.

  (** k-th event of cycle i on process 0 / process 1. *)
  Definition event_0 (i k : nat) : Event := ⟨0, p0_base_index i + k⟩.
  Definition event_1 (i k : nat) : Event := ⟨1, p1_base_index i + k⟩.

  (* ── Messages ──────────────────────────────────────────────────────────── *)

  (* Even cycles: P0 initiates *)
  Definition msg_ping0 (i : nat) : Message :=
    {| send_event := event_0 i 0; recv_event := event_1 i 0 |}.
  Definition msg_pong0 (i : nat) : Message :=
    {| send_event := event_1 i 1; recv_event := event_0 i 1 |}.

  (* Odd cycles: P1 initiates *)
  Definition msg_ping1 (i : nat) : Message :=
    {| send_event := event_1 i 0; recv_event := event_0 i 0 |}.
  Definition msg_pong1 (i : nat) : Message :=
    {| send_event := event_0 i 1; recv_event := event_1 i 1 |}.

  (** Internal processing: self-message chain on process [p] after the handshake.
      msg_internal_chain p base k connects index (base+1+k) to (base+1+S k). *)
  Definition msg_internal_chain (p : ProcessId) (base k : nat) : Message :=
    {| send_event := ⟨p, base + 1 + k⟩;
       recv_event := ⟨p, base + 1 + S k⟩ |}.

  (** Local ordering: connect consecutive events on the same process. *)
  Definition msg_local_order (p : ProcessId) (base : nat) : Message :=
    {| send_event := ⟨p, base⟩; recv_event := ⟨p, base + 1⟩ |}.

  (* ── Transactions ──────────────────────────────────────────────────────── *)

  (**
    A PingPongTransaction bundles a Ping with its immediate Pong.
    The Pong sender is the Ping receiver, and the Pong send event
    immediately follows the Ping receive event (index-wise).
  *)
  Record PingPongTransaction := {
    pp_ping : Message;
    pp_pong : Message;
    pp_link_process : process (recv_event pp_ping) = process (send_event pp_pong);
    pp_link_index   : index (send_event pp_pong) = S (index (recv_event pp_ping));
  }.

  (** Build the transaction for cycle [i], dispatching on parity. *)
  Definition get_transaction (i : nat) : PingPongTransaction.
  Proof.
    destruct (Nat.even i) eqn:Heven.
    - (* Even: P0 initiates *)
      refine {| pp_ping := msg_ping0 i; pp_pong := msg_pong0 i;
                pp_link_process := _; pp_link_index := _ |}.
      + simpl. reflexivity.
      + simpl. unfold p1_base_index. lia.
    - (* Odd: P1 initiates *)
      refine {| pp_ping := msg_ping1 i; pp_pong := msg_pong1 i;
                pp_link_process := _; pp_link_index := _ |}.
      + simpl. reflexivity.
      + simpl. unfold p0_base_index. lia.
  Defined.

  (* ── Transaction lookup lemmas ─────────────────────────────────────────── *)

  Lemma get_transaction_ping_even : forall i,
    Nat.even i = true  -> (get_transaction i).(pp_ping) = msg_ping0 i.
  Proof. intros i Hi. unfold get_transaction. rewrite Hi. reflexivity. Qed.

  Lemma get_transaction_ping_odd : forall i,
    Nat.even i = false -> (get_transaction i).(pp_ping) = msg_ping1 i.
  Proof. intros i Hi. unfold get_transaction. rewrite Hi. reflexivity. Qed.

  Lemma get_transaction_pong_even : forall i,
    Nat.even i = true  -> (get_transaction i).(pp_pong) = msg_pong0 i.
  Proof. intros i Hi. unfold get_transaction. rewrite Hi. reflexivity. Qed.

  Lemma get_transaction_pong_odd : forall i,
    Nat.even i = false -> (get_transaction i).(pp_pong) = msg_pong1 i.
  Proof. intros i Hi. unfold get_transaction. rewrite Hi. reflexivity. Qed.

  (* ── Cycle event maps ──────────────────────────────────────────────────── *)

  Definition map_ping_send (i : nat) : Event := send_event (get_transaction i).(pp_ping).
  Definition map_ping_recv (i : nat) : Event := recv_event (get_transaction i).(pp_ping).
  Definition map_pong_send (i : nat) : Event := send_event (get_transaction i).(pp_pong).
  Definition map_pong_recv (i : nat) : Event := recv_event (get_transaction i).(pp_pong).

  (* ── Process membership lemmas ─────────────────────────────────────────── *)

  Lemma map_ping_send_even_process : forall i,
    Nat.even i = true -> process (map_ping_send i) = 0.
  Proof.
    intros i Hi. unfold map_ping_send. rewrite get_transaction_ping_even by assumption.
    unfold msg_ping0, event_0. simpl. reflexivity.
  Qed.

  Lemma map_ping_recv_even_process : forall i,
    Nat.even i = true -> process (map_ping_recv i) = 1.
  Proof.
    intros i Hi. unfold map_ping_recv. rewrite get_transaction_ping_even by assumption.
    unfold msg_ping0, event_1. simpl. reflexivity.
  Qed.

  Lemma map_ping_send_odd_process : forall i,
    Nat.even i = false -> process (map_ping_send i) = 1.
  Proof.
    intros i Hi. unfold map_ping_send. rewrite get_transaction_ping_odd by assumption.
    unfold msg_ping1, event_1. simpl. reflexivity.
  Qed.

  Lemma map_ping_recv_odd_process : forall i,
    Nat.even i = false -> process (map_ping_recv i) = 0.
  Proof.
    intros i Hi. unfold map_ping_recv. rewrite get_transaction_ping_odd by assumption.
    unfold msg_ping1, event_0. simpl. reflexivity.
  Qed.

End PingPongParameters.

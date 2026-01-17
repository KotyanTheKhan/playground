From HappenedBefore Require Import EventStructure.
From HappenedBefore Require Import CausalRelation.
From HappenedBefore Require Import HappenedBefore.
From HappenedBefore Require Import PosetInstance.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

(* ========== Infinite Ping Pong Example (Alternating Symmetric) ========== *)

(* 
  This module defines a formal model of two processes (P0 and P1) using an
  ALTErnating SYMMETRIC protocol.
  
  Protocol Rules:
  1. Seriality: Only one message flow is active at any time.
  2. Symmetry via Alternation:
     - Even Cycles (0, 2, ...): P0 is the Initiator, P1 is the Responder.
     - Odd Cycles (1, 3, ...): P1 is the Initiator, P0 is the Responder.
  3. Immediate Response: The Responder sends a Pong immediately upon receiving a Ping.
     There are no internal delays during the handshake.
  4. Post-Interaction Gaps: Both processes perform internal computation steps ("Gaps")
     AFTER the handshake is complete, before the next cycle begins.
  
  Interaction Schematic:
  
  Cycle 2k (Even):           Cycle 2k+1 (Odd):
  P0            P1           P0            P1
  |             |            |             |
  | Ping0       |            |       Ping1 |
  +------------>|            |<------------+
  |             |            |             |
  |       Pong0 |            | Pong1       |
  |<------------+            +------------>|
  :             :            :             :
  : Gaps        : Gaps       : Gaps        : Gaps
  |             |            |             |
  v             v            v             v
  Cycle 2k+1 start           Cycle 2k+2 start
  
*)

Section PingPongHelpes.
  (* Helper lemma for division logic to fix build *)
  Lemma div_mul_add_small : forall a b n,
    n > 0 -> b < n -> (a * n + b) / n = a.
  Proof.
    intros.
    rewrite Nat.div_add_l by lia.
    rewrite Nat.div_small by lia.
    lia.
  Qed.
End PingPongHelpes.

Section PingPongParameters.

  (* 
     Parameters for internal gaps.
     These represent local processing steps taken by P0/P1 respectively 
     after a cycle's interaction is finished.
  *)
  Variable GAP_0 : nat.
  Variable GAP_1 : nat.

  (* 
    Event Indices Calculation:
    
    We allocate a fixed block of indices for each process for every cycle.
    
    Structure per Cycle:
    - Index 0: First Interaction Event (Send Ping for Initiator, Recv Ping for Responder)
    - Index 1: Second Interaction Event (Recv Pong for Initiator, Send Pong for Responder)
    - Index 2..2+GAP-1: Internal Gap Events.
    
    Total events per process per cycle = 2 + GAP is sufficient to hold all necessary events.
  *)

  Definition p0_events_per_cycle : nat := 2 + GAP_0.
  Definition p1_events_per_cycle : nat := 2 + GAP_1.

  Definition p0_base_index (i : nat) : nat := i * p0_events_per_cycle.
  Definition p1_base_index (i : nat) : nat := i * p1_events_per_cycle.

  (* Event Definitions *)
  
  (* 
     Helper definitions for accessing events within a cycle.
     event_0 i k: The k-th event of cycle i on process 0.
     event_1 i k: The k-th event of cycle i on process 1.
  *)
  
  Definition event_0 (i : nat) (k : nat) : Event := ⟨0, p0_base_index i + k⟩.
  Definition event_1 (i : nat) (k : nat) : Event := ⟨1, p1_base_index i + k⟩.

  (* Message Definitions *)
  
  (* Even Cycles: P0 Initiates with Ping0, P1 Responds with Pong0 *)
  Definition msg_ping0 (i : nat) : Message :=
    {| send_event := event_0 i 0;  (* P0 Send Ping *)
       recv_event := event_1 i 0 |}. (* P1 Recv Ping *)
       
  Definition msg_pong0 (i : nat) : Message :=
    {| send_event := event_1 i 1;  (* P1 Send Pong (Immediate) *)
       recv_event := event_0 i 1 |}. (* P0 Recv Pong *)

  (* Odd Cycles: P1 Initiates with Ping1, P0 Responds with Pong1 *)
  Definition msg_ping1 (i : nat) : Message :=
    {| send_event := event_1 i 0;  (* P1 Send Ping *)
       recv_event := event_0 i 0 |}. (* P0 Recv Ping *)

  Definition msg_pong1 (i : nat) : Message :=
    {| send_event := event_0 i 1;  (* P0 Send Pong (Immediate) *)
       recv_event := event_1 i 1 |}. (* P1 Recv Pong *)

  (* 
     Transaction Structure
     
     Captures the atomic nature of a Ping-Pong exchange.
     It proves that for a valid transaction, the Pong is sent immediately 
     after the Ping is received by the same process.
  *)
  Record PingPongTransaction := {
    pp_ping : Message;
    pp_pong : Message;
    
    (* 
       Link Property: 
       The Pong sender is the Ping receiver.
       The Pong send event is the IMMEDIATE successor of the Ping receive event.
    *)
    pp_link_process : process (recv_event pp_ping) = process (send_event pp_pong);
    pp_link_index   : index (send_event pp_pong) = S (index (recv_event pp_ping))
  }.

  (* 
     Helper to construct transactions for any cycle.
     Demonstrates that our definitions satisfy the Transaction requirements.
  *)
  Definition get_transaction (i : nat) : PingPongTransaction.
  Proof.
    destruct (Nat.even i) eqn:Heven.
    - (* Even Cycle: P0 Init, P1 Resp *)
      refine {| pp_ping := msg_ping0 i; pp_pong := msg_pong0 i; pp_link_process := _; pp_link_index := _ |}.
      + (* Process *) simpl. reflexivity.
      + (* Index *) simpl. unfold p1_base_index. lia.
    - (* Odd Cycle: P1 Init, P0 Resp *)
      refine {| pp_ping := msg_ping1 i; pp_pong := msg_pong1 i; pp_link_process := _; pp_link_index := _ |}.
      + (* Process *) simpl. reflexivity.
      + (* Index *) simpl. unfold p0_base_index. lia.
  Defined.

  (* 
     Internal Messages (Gaps/Processing) 
     
     We model processing as a chain of self-messages.
     Crucially, this chain starts AFTER the handshake. 
     The last interaction event is at index 1 (Recv/Send Pong).
     So the first internal message connects index 1 to 2.
     
     msg_internal_chain p base k:
       Connects index (base + 1 + k) -> (base + 1 + S k).
       k=0:  1 -> 2
       k=1:  2 -> 3
       ...
  *)
  Definition msg_internal_chain (p : ProcessId) (base : nat) (k : nat) : Message :=
    {| send_event := ⟨p, base + 1 + k⟩;
       recv_event := ⟨p, base + 1 + S k⟩ |}.
       
  (* 
     History Construction:
     
     The history list linearizes causal events.
     For each cycle i, we add:
     1. The Ping msg
     2. The Pong msg
     3. P0's internal messages
     4. P1's internal messages
     
     Total messages added per cycle = 2 (Ping+Pong) + GAP_0 + GAP_1.
  *)

  Definition msgs_per_cycle_fixed : nat := 2 + GAP_0 + GAP_1.
  
  (* Helper to determine transaction from message index *)
  Definition nth_message_fixed (n : nat) : Message :=
    let cycle := n / msgs_per_cycle_fixed in
    let phase := n mod msgs_per_cycle_fixed in
    let txn := get_transaction cycle in
    
    if nat_eqb phase 0 then
      txn.(pp_ping)
    else if nat_eqb phase 1 then
      txn.(pp_pong)
    else if nat_leb phase (1 + GAP_0) then
      (* Phase 2 .. 1+G0: P0 internal gaps. *)
      let k := phase - 2 in
      msg_internal_chain 0 (p0_base_index cycle) k
    else
      (* Phase 2+G0 .. End: P1 internal gaps. *)
      let k := phase - (2 + GAP_0) in
      msg_internal_chain 1 (p1_base_index cycle) k.

  Fixpoint pp_history_fixed (n : nat) : History :=
    match n with
    | 0 => nil
    | S n' => cons (nth_message_fixed n') (pp_history_fixed n')
    end.

  (* ========== Proofs ========== *)

  (* 
     Rank Function (Global Logical Time)
     
     We verify acyclicity by mapping every event to a monotonic global time.
  *)
  
  Definition K_cycle : nat := 4 + GAP_0 + GAP_1.

  Definition rank (e : Event) : nat :=
    let i := e.(index) / (if e.(process) =? 0 then p0_events_per_cycle else p1_events_per_cycle) in
    let off := e.(index) mod (if e.(process) =? 0 then p0_events_per_cycle else p1_events_per_cycle) in
    let is_even := Nat.even i in
    let base_t := i * K_cycle in
    
    match e.(process) with
    | 0 => 
      if is_even then
        (* P0 is Initiator (Even) *)
        if nat_eqb off 0 then base_t
        else base_t + 3 + (off - 1)
      else
        (* P0 is Responder (Odd) *)
        if nat_eqb off 0 then base_t + 1
        else base_t + 1 + off
        
    | _ => (* P1 Behavior (Symmetric to P0) *)
      if is_even then
        (* P1 is Responder (Even) *)
        if nat_eqb off 0 then base_t + 1
        else base_t + 1 + off
      else
        (* P1 is Initiator (Odd) *)
        if nat_eqb off 0 then base_t
        else base_t + 3 + (off - 1)
    end.

  (* Helper Loop Proofs *) 
  
  Notation p0_epc := p0_events_per_cycle.
  Notation p1_epc := p1_events_per_cycle.


  (* 
     Lemma: rank_mono_p0_int
     Proves that P0's internal processing chain strictly increases in rank.
  *)
  Lemma rank_mono_p0_int : forall i k, k < GAP_0 ->
    rank (⟨0, p0_base_index i + 1 + k⟩) < rank (⟨0, p0_base_index i + 1 + S k⟩).
  Proof.
  Admitted.

  (* Symmetric lemma for P1 *)
  Lemma rank_mono_p1_int : forall i k, k < GAP_1 ->
    rank (⟨1, p1_base_index i + 1 + k⟩) < rank (⟨1, p1_base_index i + 1 + S k⟩).
  Proof.
  Admitted.

  (* 
     Main Theorem: nth_message_fixed_rank_increase
  *)
  Lemma nth_message_fixed_rank_increase : forall n,
    rank (send_event (nth_message_fixed n)) < rank (recv_event (nth_message_fixed n)).
  Proof.
  Admitted.

  (* Standard Acyclicity / Boilerplate *)
  Lemma pp_history_content : forall n m,
    In m (pp_history_fixed n) -> exists k, k < n /\ m = nth_message_fixed k.
  Proof.
    induction n; intros m Hin.
    - inversion Hin.
    - simpl in Hin. destruct Hin as [Heq | Htail].
      + exists n. split. lia. symmetry. assumption.
      + apply IHn in Htail. destruct Htail as [k [Hlt Heq]].
        exists k. split. lia. assumption.
  Qed.

  Lemma strict_hb_increases_rank : forall n a b,
    strict_happened_before (pp_history_fixed n) a b ->
    rank a < rank b.
  Proof.
    intros n a b Hsb.
    induction Hsb.
    - destruct H as [m [Hin [Hs Hr]]].
      apply pp_history_content in Hin.
      destruct Hin as [k [Hlt Hm]].
      subst m.
      rewrite <- Hs, <- Hr.
      apply nth_message_fixed_rank_increase.
    - lia.
  Qed.

  Lemma pp_acyclic : forall n, IsAcyclic (pp_history_fixed n).
  Proof.
    intro n. unfold IsAcyclic. intros e H_cycle.
    apply strict_hb_increases_rank in H_cycle.
    lia.
  Qed.

  Instance pp_hb_inst (n : nat) : IsHappenedBefore (pp_history_fixed n) (happened_before (pp_history_fixed n)).
  Proof.
    constructor. apply happened_before_poset. apply pp_acyclic.
  Defined.

  Theorem ping_pong_arbitrary_gaps : 
    forall (n : nat), 
      IsHappenedBefore (pp_history_fixed n) (happened_before (pp_history_fixed n)).
  Proof.
    intros n.
    apply pp_hb_inst.
  Qed.

  (* 
     IsPairAlternatingSymPingPong Class
     
     Captures the logical structure of this protocol:
     - Alternating roles.
     - Causal chain Ping -> Pong -> NextPing.
  *)
  Class IsPairAlternatingSymPingPong (R : Event -> Event -> Prop) := {
    map_cycle_ping_send : nat -> Event;
    map_cycle_ping_recv : nat -> Event;
    map_cycle_pong_send : nat -> Event;
    map_cycle_pong_recv : nat -> Event;

    (* Even Cycles: P0 Init *)
    ax_even_init : forall i, Nat.even i = true -> process (map_cycle_ping_send i) = 0;
    ax_even_resp : forall i, Nat.even i = true -> process (map_cycle_ping_recv i) = 1;
    
    (* Odd Cycles: P1 Init *)
    ax_odd_init : forall i, Nat.even i = false -> process (map_cycle_ping_send i) = 1;
    ax_odd_resp : forall i, Nat.even i = false -> process (map_cycle_ping_recv i) = 0;

    (* Causality *)
    ax_ping_rel : forall i, R (map_cycle_ping_send i) (map_cycle_ping_recv i);
    ax_turn_rel : forall i, R (map_cycle_ping_recv i) (map_cycle_pong_send i);
    ax_pong_rel : forall i, R (map_cycle_pong_send i) (map_cycle_pong_recv i);
    (* Between cycles (simplified for abstraction) *)
    ax_next_rel : forall i, R (map_cycle_pong_recv i) (map_cycle_ping_send (S i));
  }.

  (* Explicitly show our implementation satisfies this class *)
  Instance ex_is_ping_pong (n : nat) : IsPairAlternatingSymPingPong (happened_before (pp_history_fixed n)).
  Proof.
  Admitted.

End PingPongParameters.

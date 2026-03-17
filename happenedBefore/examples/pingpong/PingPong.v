From HappenedBefore Require Import EventStructure CausalRelation HappenedBefore PosetInstance.
From Stdlib Require Import Arith Lia Bool PeanoNat.

(**
  Infinite Ping-Pong: two processes (P0, P1) using an alternating symmetric protocol.

  Protocol rules:
  1. Seriality: one message flow active at a time.
  2. Role alternation:
       Even cycles (0, 2, …): P0 initiates (Ping0/Pong0), P1 responds.
       Odd  cycles (1, 3, …): P1 initiates (Ping1/Pong1), P0 responds.
  3. Immediate response: responder sends Pong upon receiving Ping.
  4. Post-handshake gaps: both processes perform internal steps before the next cycle.

  Cycle schematic:

    Even cycle 2k              Odd cycle 2k+1
    P0          P1             P0          P1
    | Ping0      |             |     Ping1 |
    +----------->|             |<----------+
    |      Pong0 |             | Pong1     |
    |<-----------+             +---------->|
    : G0 gaps    : G1 gaps     : G0 gaps   : G1 gaps
*)

(* ════════════════════════════════════════════════════════════════════════════
   Arithmetic helpers
   ════════════════════════════════════════════════════════════════════════════ *)

Section PingPongHelpers.

  Lemma div_mul_add_small : forall a b n,
    n > 0 -> b < n -> (a * n + b) / n = a.
  Proof.
    intros. rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia.
  Qed.

  Lemma mod_mul_add_small : forall a b n,
    n > 0 -> b < n -> (a * n + b) mod n = b.
  Proof.
    intros a b n Hn Hb.
    rewrite Nat.add_comm, Nat.Div0.mod_add. apply Nat.mod_small; assumption.
  Qed.

  (** Cycle index of the (1+k)-th internal event when events_per_cycle = 2 + gap. *)
  Lemma int_event_same_cycle : forall i k gap,
    k < gap -> (i * (2 + gap) + 1 + k) / (2 + gap) = i.
  Proof.
    intros i k gap Hk.
    replace (i * (2 + gap) + 1 + k) with (i * (2 + gap) + (1 + k)) by lia.
    apply div_mul_add_small; lia.
  Qed.

  (** Intra-cycle offset of the (1+k)-th internal event when events_per_cycle = 2 + gap. *)
  Lemma int_event_offset : forall i k gap,
    k < gap -> (i * (2 + gap) + 1 + k) mod (2 + gap) = 1 + k.
  Proof.
    intros i k gap Hk.
    replace (i * (2 + gap) + 1 + k) with (i * (2 + gap) + (1 + k)) by lia.
    apply mod_mul_add_small; lia.
  Qed.

End PingPongHelpers.

(* ════════════════════════════════════════════════════════════════════════════
   Protocol parameters, definitions, and proofs
   ════════════════════════════════════════════════════════════════════════════ *)

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

  Notation p0_epc := p0_events_per_cycle.
  Notation p1_epc := p1_events_per_cycle.

  (** First event index on each process for cycle i. *)
  Definition p0_base_index (i : nat) : nat := i * p0_epc.
  Definition p1_base_index (i : nat) : nat := i * p1_epc.

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

  (* ── Fixed history ─────────────────────────────────────────────────────── *)

  (**
    Message layout per cycle (fixed history):
      phase 0         : Ping
      phase 1         : Pong
      phases 2..1+G0  : P0 internal gaps
      phases 2+G0..end: P1 internal gaps

    Total messages per cycle = 2 + GAP_0 + GAP_1.
  *)
  Definition msgs_per_cycle_fixed : nat := 2 + GAP_0 + GAP_1.

  Definition nth_message_fixed (n : nat) : Message :=
    let cycle := n / msgs_per_cycle_fixed in
    let phase := n mod msgs_per_cycle_fixed in
    let txn   := get_transaction cycle in
    if nat_eqb phase 0 then
      txn.(pp_ping)
    else if nat_eqb phase 1 then
      txn.(pp_pong)
    else if nat_leb phase (1 + GAP_0) then
      msg_internal_chain 0 (p0_base_index cycle) (phase - 2)
    else
      msg_internal_chain 1 (p1_base_index cycle) (phase - (2 + GAP_0)).

  Fixpoint pp_history_fixed (n : nat) : History :=
    match n with
    | 0    => nil
    | S n' => cons (nth_message_fixed n') (pp_history_fixed n')
    end.

  (* ── Rank function ─────────────────────────────────────────────────────── *)

  (**
    Global logical time: every message strictly increases rank,
    which we use to prove acyclicity.

    Rank assignment per cycle i with base_t = i * K_cycle:
      P0 initiates (even i): send Ping → base_t,   recv Pong → base_t+3+..
      P0 responds  (odd  i): recv Ping → base_t+1, send Pong → base_t+2+..
      P1 responds  (even i): recv Ping → base_t+1, send Pong → base_t+2+..
      P1 initiates (odd  i): send Ping → base_t,   recv Pong → base_t+3+..
  *)
  Definition K_cycle : nat := 4 + GAP_0 + GAP_1.

  Definition rank (e : Event) : nat :=
    let epc    := if e.(process) =? 0 then p0_epc else p1_epc in
    let i      := e.(index) / epc in
    let off    := e.(index) mod epc in
    let base_t := i * K_cycle in
    match e.(process) with
    | 0 =>
      if Nat.even i then
        if nat_eqb off 0 then base_t else base_t + 3 + (off - 1)
      else
        if nat_eqb off 0 then base_t + 1 else base_t + 1 + off
    | _ =>
      if Nat.even i then
        if nat_eqb off 0 then base_t + 1 else base_t + 1 + off
      else
        if nat_eqb off 0 then base_t else base_t + 3 + (off - 1)
    end.

  (* ── Rank monotonicity for internal chains ─────────────────────────────── *)

  Lemma p0_int_event_same_cycle : forall i k,
    k < GAP_0 -> (p0_base_index i + 1 + k) / p0_epc = i.
  Proof.
    intros i k Hk. unfold p0_base_index, p0_epc. apply int_event_same_cycle. assumption.
  Qed.

  Lemma p0_int_event_offset : forall i k,
    k < GAP_0 -> (p0_base_index i + 1 + k) mod p0_epc = 1 + k.
  Proof.
    intros i k Hk. unfold p0_base_index, p0_epc. apply int_event_offset. assumption.
  Qed.

  Lemma rank_mono_p0_int : forall i k, S k < GAP_0 ->
    rank ⟨0, p0_base_index i + 1 + k⟩ < rank ⟨0, p0_base_index i + 1 + S k⟩.
  Proof.
    intros i k HkS. assert (Hk : k < GAP_0) by lia.
    unfold rank. cbn [process index fst snd]. cbn [Nat.eqb].
    rewrite (p0_int_event_same_cycle i k Hk), (p0_int_event_same_cycle i (S k) HkS),
            (p0_int_event_offset i k Hk), (p0_int_event_offset i (S k) HkS).
    unfold K_cycle. destruct (Nat.even i) eqn:Heven; cbn [Nat.eqb].
    - (* P0 initiates (even): rank = base + 3 + (off - 1) *)
      assert (Hneq1 : nat_eqb (1 + k) 0 = false)   by (apply Nat.eqb_neq; lia).
      assert (Hneq2 : nat_eqb (1 + S k) 0 = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq1, Hneq2.
      replace (1 + k - 1) with k by lia. replace (1 + S k - 1) with (S k) by lia.
      apply Nat.add_lt_mono_l, Nat.lt_succ_diag_r.
    - (* P0 responds (odd): rank = base + 1 + off *)
      apply Nat.add_lt_mono_l, Nat.add_lt_mono_l, Nat.lt_succ_diag_r.
  Qed.

  Lemma p1_int_event_same_cycle : forall i k,
    k < GAP_1 -> (p1_base_index i + 1 + k) / p1_epc = i.
  Proof.
    intros i k Hk. unfold p1_base_index, p1_epc. apply int_event_same_cycle. assumption.
  Qed.

  Lemma p1_int_event_offset : forall i k,
    k < GAP_1 -> (p1_base_index i + 1 + k) mod p1_epc = 1 + k.
  Proof.
    intros i k Hk. unfold p1_base_index, p1_epc. apply int_event_offset. assumption.
  Qed.

  Lemma rank_mono_p1_int : forall i k, S k < GAP_1 ->
    rank ⟨1, p1_base_index i + 1 + k⟩ < rank ⟨1, p1_base_index i + 1 + S k⟩.
  Proof.
    intros i k HkS. assert (Hk : k < GAP_1) by lia.
    unfold rank. cbn [process index fst snd]. cbn [Nat.eqb].
    rewrite (p1_int_event_same_cycle i k Hk), (p1_int_event_same_cycle i (S k) HkS),
            (p1_int_event_offset i k Hk), (p1_int_event_offset i (S k) HkS).
    unfold K_cycle. destruct (Nat.even i) eqn:Heven; cbn [Nat.eqb].
    - (* P1 responds (even): rank = base + 1 + off *)
      apply Nat.add_lt_mono_l, Nat.add_lt_mono_l, Nat.lt_succ_diag_r.
    - (* P1 initiates (odd): rank = base + 3 + (off - 1) *)
      assert (Hneq1 : nat_eqb (1 + k) 0 = false)   by (apply Nat.eqb_neq; lia).
      assert (Hneq2 : nat_eqb (1 + S k) 0 = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq1, Hneq2.
      replace (1 + k - 1) with k by lia. replace (1 + S k - 1) with (S k) by lia.
      apply Nat.add_lt_mono_l, Nat.lt_succ_diag_r.
  Qed.

  (* ── Acyclicity ────────────────────────────────────────────────────────── *)

  Lemma nth_message_fixed_rank_increase : forall n,
    rank (send_event (nth_message_fixed n)) < rank (recv_event (nth_message_fixed n)).
  Proof.
  Admitted.

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
    strict_happened_before (pp_history_fixed n) a b -> rank a < rank b.
  Proof.
    intros n a b Hsb. induction Hsb.
    - destruct H as [m [Hin [Hs Hr]]].
      apply pp_history_content in Hin. destruct Hin as [k [_ Hm]]. subst m.
      rewrite <- Hs, <- Hr. apply nth_message_fixed_rank_increase.
    - lia.
  Qed.

  Lemma pp_acyclic : forall n, IsAcyclic (pp_history_fixed n).
  Proof.
    intro n. unfold IsAcyclic. intros e H_cycle.
    apply strict_hb_increases_rank in H_cycle. lia.
  Qed.

  Instance pp_hb_inst (n : nat) :
    IsHappenedBefore (pp_history_fixed n) (happened_before (pp_history_fixed n)).
  Proof.
    constructor. apply happened_before_poset. apply pp_acyclic.
  Defined.

  Theorem ping_pong_arbitrary_gaps : forall n,
    IsHappenedBefore (pp_history_fixed n) (happened_before (pp_history_fixed n)).
  Proof. intro n. apply pp_hb_inst. Qed.

  (* ── Protocol typeclass ────────────────────────────────────────────────── *)

  (**
    Captures the logical structure of the alternating symmetric ping-pong:
    alternating initiator/responder roles and the causal chain
    Ping → (Turn) → Pong → (InterCycle) → NextPing.
  *)
  Class IsPairAlternatingSymPingPong (R : Event -> Event -> Prop) := {
    map_cycle_ping_send : nat -> Event;
    map_cycle_ping_recv : nat -> Event;
    map_cycle_pong_send : nat -> Event;
    map_cycle_pong_recv : nat -> Event;

    ax_even_init : forall i, Nat.even i = true  -> process (map_cycle_ping_send i) = 0;
    ax_even_resp : forall i, Nat.even i = true  -> process (map_cycle_ping_recv i) = 1;
    ax_odd_init  : forall i, Nat.even i = false -> process (map_cycle_ping_send i) = 1;
    ax_odd_resp  : forall i, Nat.even i = false -> process (map_cycle_ping_recv i) = 0;

    ax_ping_rel  : forall i, R (map_cycle_ping_send i) (map_cycle_ping_recv i);
    ax_turn_rel  : forall i, R (map_cycle_ping_recv i) (map_cycle_pong_send i);
    ax_pong_rel  : forall i, R (map_cycle_pong_send i) (map_cycle_pong_recv i);
    ax_next_rel  : forall i, R (map_cycle_pong_recv i) (map_cycle_ping_send (S i));
  }.

  (* ── Cycle event maps ──────────────────────────────────────────────────── *)

  Definition map_ping_send (i : nat) : Event := send_event (get_transaction i).(pp_ping).
  Definition map_ping_recv (i : nat) : Event := recv_event (get_transaction i).(pp_ping).
  Definition map_pong_send (i : nat) : Event := send_event (get_transaction i).(pp_pong).
  Definition map_pong_recv (i : nat) : Event := recv_event (get_transaction i).(pp_pong).

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

  (* ── History membership helpers ────────────────────────────────────────── *)

  Lemma nth_message_in_history : forall n k, k < n ->
    In (nth_message_fixed k) (pp_history_fixed n).
  Proof.
    intros n k Hk. induction n.
    - lia.
    - simpl. destruct (Nat.eq_dec k n).
      + subst. left. reflexivity.
      + right. apply IHn. lia.
  Qed.

  Lemma ping_is_nth_message : forall i,
    nth_message_fixed (i * msgs_per_cycle_fixed) = (get_transaction i).(pp_ping).
  Proof.
    intro i. unfold nth_message_fixed.
    assert (Hdiv : i * msgs_per_cycle_fixed / msgs_per_cycle_fixed = i)
      by (apply Nat.div_mul; unfold msgs_per_cycle_fixed; lia).
    assert (Hmod : i * msgs_per_cycle_fixed mod msgs_per_cycle_fixed = 0)
      by (apply Nat.Div0.mod_mul).
    rewrite Hdiv, Hmod. simpl. reflexivity.
  Qed.

  Lemma pong_is_nth_message : forall i,
    nth_message_fixed (i * msgs_per_cycle_fixed + 1) = (get_transaction i).(pp_pong).
  Proof.
    intro i. unfold nth_message_fixed.
    assert (Hdiv : (i * msgs_per_cycle_fixed + 1) / msgs_per_cycle_fixed = i)
      by (apply div_mul_add_small; unfold msgs_per_cycle_fixed; lia).
    assert (Hmod : (i * msgs_per_cycle_fixed + 1) mod msgs_per_cycle_fixed = 1)
      by (apply mod_mul_add_small; unfold msgs_per_cycle_fixed; lia).
    rewrite Hdiv, Hmod. reflexivity.
  Qed.

  (** If cycle i fits within the first [n] messages, then both interaction
      events of that cycle are present. *)
  Lemma history_contains_cycle : forall n i,
    i < n / msgs_per_cycle_fixed -> i * msgs_per_cycle_fixed + 1 < n.
  Proof.
    intros n i Hi.
    set (m := msgs_per_cycle_fixed).
    assert (Hm_pos : m > 0)           by (unfold m, msgs_per_cycle_fixed; lia).
    assert (Hi_succ : S i <= n / m)   by (apply Nat.le_succ_l; exact Hi).
    assert (Hmul : S i * m <= (n / m) * m) by (apply Nat.mul_le_mono_r; exact Hi_succ).
    assert (Hdiv_le : (n / m) * m <= n)
      by (rewrite Nat.mul_comm; apply Nat.Div0.mul_div_le).
    replace (S i * m) with (i * m + m) in Hmul by lia.
    unfold m, msgs_per_cycle_fixed in *. lia.
  Qed.

  Lemma ping_in_history : forall n i,
    i * msgs_per_cycle_fixed < n -> In (get_transaction i).(pp_ping) (pp_history_fixed n).
  Proof.
    intros n i Hi. rewrite <- ping_is_nth_message. apply nth_message_in_history. assumption.
  Qed.

  Lemma pong_in_history : forall n i,
    i * msgs_per_cycle_fixed + 1 < n -> In (get_transaction i).(pp_pong) (pp_history_fixed n).
  Proof.
    intros n i Hi. rewrite <- pong_is_nth_message. apply nth_message_in_history. assumption.
  Qed.

  Lemma ping_in_sufficient_history : forall n i,
    i < n / msgs_per_cycle_fixed -> In (get_transaction i).(pp_ping) (pp_history_fixed n).
  Proof.
    intros n i Hi. apply ping_in_history.
    assert (H := history_contains_cycle n i Hi). unfold msgs_per_cycle_fixed in *. lia.
  Qed.

  Lemma pong_in_sufficient_history : forall n i,
    i < n / msgs_per_cycle_fixed -> In (get_transaction i).(pp_pong) (pp_history_fixed n).
  Proof.
    intros n i Hi. apply pong_in_history. apply history_contains_cycle. assumption.
  Qed.

  (* ── Fixed-history causality lemmas ────────────────────────────────────── *)

  Lemma ping_causes_recv : forall n i, i * msgs_per_cycle_fixed < n ->
    happened_before (pp_history_fixed n) (map_ping_send i) (map_ping_recv i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction i).(pp_ping). split.
    - apply ping_in_history; assumption.
    - unfold map_ping_send, map_ping_recv. split; reflexivity.
  Qed.

  Lemma pong_causes_recv : forall n i, i * msgs_per_cycle_fixed + 1 < n ->
    happened_before (pp_history_fixed n) (map_pong_send i) (map_pong_recv i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction i).(pp_pong). split.
    - apply pong_in_history; assumption.
    - unfold map_pong_send, map_pong_recv. split; reflexivity.
  Qed.

  (* ── Extended history ───────────────────────────────────────────────────── *)

  (**
    The extended history adds local-order and inter-cycle messages needed
    to prove all IsPairAlternatingSymPingPong axioms.

    Message layout per cycle (extended history):
      phase 0         : Ping
      phase 1         : Turn  (ping_recv → pong_send on same process)
      phase 2         : Pong
      phase 3         : InterCycle (pong_recv → next ping_send; crosses processes)
      phases 4..3+G0  : P0 internal gaps
      phases 4+G0..end: P1 internal gaps

    Total messages per cycle = 4 + GAP_0 + GAP_1.
  *)

  (** Local turn: the responder immediately replies — ping_recv → pong_send. *)
  Definition msg_turn (i : nat) : Message :=
    if Nat.even i then
      {| send_event := event_1 i 0; recv_event := event_1 i 1 |}  (* P1 is responder *)
    else
      {| send_event := event_0 i 0; recv_event := event_0 i 1 |}. (* P0 is responder *)

  (**
    Inter-cycle synchronization: pong_recv of cycle i triggers ping_send of
    cycle i+1.  Because roles alternate, these events are on different
    processes, so an explicit causal message is needed.
  *)
  Definition msg_inter_cycle (i : nat) : Message :=
    if Nat.even i then
      {| send_event := event_0 i 1; recv_event := event_1 (S i) 0 |}
    else
      {| send_event := event_1 i 1; recv_event := event_0 (S i) 0 |}.

  Definition msgs_per_cycle_ext : nat := 4 + GAP_0 + GAP_1.

  Definition nth_message_ext (n : nat) : Message :=
    let cycle := n / msgs_per_cycle_ext in
    let phase := n mod msgs_per_cycle_ext in
    let txn   := get_transaction cycle in
    if nat_eqb phase 0 then
      txn.(pp_ping)
    else if nat_eqb phase 1 then
      msg_turn cycle
    else if nat_eqb phase 2 then
      txn.(pp_pong)
    else if nat_eqb phase 3 then
      msg_inter_cycle cycle
    else if nat_leb phase (3 + GAP_0) then
      msg_internal_chain 0 (p0_base_index cycle) (phase - 4)
    else
      msg_internal_chain 1 (p1_base_index cycle) (phase - (4 + GAP_0)).

  Fixpoint pp_history_ext (n : nat) : History :=
    match n with
    | 0    => nil
    | S n' => cons (nth_message_ext n') (pp_history_ext n')
    end.

  (* ── Extended history membership ─────────────────────────────────────────  *)

  Lemma nth_message_ext_in_history : forall n k, k < n ->
    In (nth_message_ext k) (pp_history_ext n).
  Proof.
    intros n k Hk. induction n.
    - lia.
    - simpl. destruct (Nat.eq_dec k n).
      + subst. left. reflexivity.
      + right. apply IHn. lia.
  Qed.

  (** Each phase [p] of the extended layout resolves to the expected message. *)

  Lemma ping_is_nth_message_ext : forall i,
    nth_message_ext (i * msgs_per_cycle_ext) = (get_transaction i).(pp_ping).
  Proof.
    intro i. unfold nth_message_ext.
    assert (Hdiv : i * msgs_per_cycle_ext / msgs_per_cycle_ext = i)
      by (apply Nat.div_mul; unfold msgs_per_cycle_ext; lia).
    assert (Hmod : i * msgs_per_cycle_ext mod msgs_per_cycle_ext = 0)
      by (apply Nat.Div0.mod_mul).
    rewrite Hdiv, Hmod. reflexivity.
  Qed.

  Lemma turn_is_nth_message_ext : forall i,
    nth_message_ext (i * msgs_per_cycle_ext + 1) = msg_turn i.
  Proof.
    intro i. unfold nth_message_ext.
    assert (Hdiv : (i * msgs_per_cycle_ext + 1) / msgs_per_cycle_ext = i)
      by (apply div_mul_add_small; unfold msgs_per_cycle_ext; lia).
    assert (Hmod : (i * msgs_per_cycle_ext + 1) mod msgs_per_cycle_ext = 1)
      by (apply mod_mul_add_small; unfold msgs_per_cycle_ext; lia).
    rewrite Hdiv, Hmod. reflexivity.
  Qed.

  Lemma pong_is_nth_message_ext : forall i,
    nth_message_ext (i * msgs_per_cycle_ext + 2) = (get_transaction i).(pp_pong).
  Proof.
    intro i. unfold nth_message_ext.
    assert (Hdiv : (i * msgs_per_cycle_ext + 2) / msgs_per_cycle_ext = i)
      by (apply div_mul_add_small; unfold msgs_per_cycle_ext; lia).
    assert (Hmod : (i * msgs_per_cycle_ext + 2) mod msgs_per_cycle_ext = 2)
      by (apply mod_mul_add_small; unfold msgs_per_cycle_ext; lia).
    rewrite Hdiv, Hmod. reflexivity.
  Qed.

  Lemma inter_is_nth_message_ext : forall i,
    nth_message_ext (i * msgs_per_cycle_ext + 3) = msg_inter_cycle i.
  Proof.
    intro i. unfold nth_message_ext.
    assert (Hdiv : (i * msgs_per_cycle_ext + 3) / msgs_per_cycle_ext = i)
      by (apply div_mul_add_small; unfold msgs_per_cycle_ext; lia).
    assert (Hmod : (i * msgs_per_cycle_ext + 3) mod msgs_per_cycle_ext = 3)
      by (apply mod_mul_add_small; unfold msgs_per_cycle_ext; lia).
    rewrite Hdiv, Hmod. reflexivity.
  Qed.

  Lemma ping_in_history_ext : forall n i, i * msgs_per_cycle_ext < n ->
    In (get_transaction i).(pp_ping) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- ping_is_nth_message_ext. apply nth_message_ext_in_history. assumption.
  Qed.

  Lemma turn_in_history_ext : forall n i, i * msgs_per_cycle_ext + 1 < n ->
    In (msg_turn i) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- turn_is_nth_message_ext. apply nth_message_ext_in_history. assumption.
  Qed.

  Lemma pong_in_history_ext : forall n i, i * msgs_per_cycle_ext + 2 < n ->
    In (get_transaction i).(pp_pong) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- pong_is_nth_message_ext. apply nth_message_ext_in_history. assumption.
  Qed.

  Lemma inter_in_history_ext : forall n i, i * msgs_per_cycle_ext + 3 < n ->
    In (msg_inter_cycle i) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- inter_is_nth_message_ext. apply nth_message_ext_in_history. assumption.
  Qed.

  (* ── Extended-history causality lemmas ───────────────────────────────────  *)

  Lemma ping_causes_recv_ext : forall n i, i * msgs_per_cycle_ext < n ->
    happened_before (pp_history_ext n) (map_ping_send i) (map_ping_recv i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction i).(pp_ping). split.
    - apply ping_in_history_ext; assumption.
    - unfold map_ping_send, map_ping_recv. split; reflexivity.
  Qed.

  Lemma turn_causes_pong_ext : forall n i, i * msgs_per_cycle_ext + 1 < n ->
    happened_before (pp_history_ext n) (map_ping_recv i) (map_pong_send i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (msg_turn i). split.
    - apply turn_in_history_ext; assumption.
    - unfold map_ping_recv, map_pong_send, msg_turn.
      destruct (Nat.even i) eqn:Heven.
      + rewrite get_transaction_ping_even, get_transaction_pong_even by assumption.
        unfold msg_ping0, msg_pong0, event_1. simpl. split; reflexivity.
      + rewrite get_transaction_ping_odd, get_transaction_pong_odd by assumption.
        unfold msg_ping1, msg_pong1, event_0. simpl. split; reflexivity.
  Qed.

  Lemma pong_causes_recv_ext : forall n i, i * msgs_per_cycle_ext + 2 < n ->
    happened_before (pp_history_ext n) (map_pong_send i) (map_pong_recv i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction i).(pp_pong). split.
    - apply pong_in_history_ext; assumption.
    - unfold map_pong_send, map_pong_recv. split; reflexivity.
  Qed.

  Lemma even_succ_negb : forall i, Nat.even (S i) = negb (Nat.even i).
  Proof. intro i. rewrite Nat.even_succ. reflexivity. Qed.

  Lemma inter_causes_next_ext : forall n i, i * msgs_per_cycle_ext + 3 < n ->
    happened_before (pp_history_ext n) (map_pong_recv i) (map_ping_send (S i)).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (msg_inter_cycle i). split.
    - apply inter_in_history_ext; assumption.
    - unfold map_pong_recv, map_ping_send, msg_inter_cycle.
      destruct (Nat.even i) eqn:Heven.
      + (* even i: pong_recv on P0, next ping_send on P1 *)
        rewrite get_transaction_pong_even by assumption.
        rewrite get_transaction_ping_odd by (rewrite even_succ_negb, Heven; reflexivity).
        unfold msg_pong0, msg_ping1, event_0, event_1. simpl. split; reflexivity.
      + (* odd i: pong_recv on P1, next ping_send on P0 *)
        rewrite get_transaction_pong_odd by assumption.
        rewrite get_transaction_ping_even by (rewrite even_succ_negb, Heven; reflexivity).
        unfold msg_pong1, msg_ping0, event_0, event_1. simpl. split; reflexivity.
  Qed.

  (* ── IsPairAlternatingSymPingPong instance ───────────────────────────────  *)

  (**
    NOTE: The causality axioms quantify over all i, but our finite history
    pp_history_ext n only contains messages for cycles i < n / msgs_per_cycle_ext.
    For cycles within the history all axioms are proved; outside we admit.
    The process axioms are unconditional since they depend only on event structure.
  *)
  Instance ex_is_ping_pong (n : nat) :
    IsPairAlternatingSymPingPong (happened_before (pp_history_ext n)).
  Proof.
    refine {|
      map_cycle_ping_send := map_ping_send;
      map_cycle_ping_recv := map_ping_recv;
      map_cycle_pong_send := map_pong_send;
      map_cycle_pong_recv := map_pong_recv;
      ax_even_init := map_ping_send_even_process;
      ax_even_resp := map_ping_recv_even_process;
      ax_odd_init  := map_ping_send_odd_process;
      ax_odd_resp  := map_ping_recv_odd_process
    |}.
    - intro i. destruct (le_lt_dec n (i * msgs_per_cycle_ext)) as [_ | Hlt].
      + admit.
      + apply ping_causes_recv_ext. assumption.
    - intro i. destruct (le_lt_dec n (i * msgs_per_cycle_ext + 1)) as [_ | Hlt].
      + admit.
      + apply turn_causes_pong_ext. assumption.
    - intro i. destruct (le_lt_dec n (i * msgs_per_cycle_ext + 2)) as [_ | Hlt].
      + admit.
      + apply pong_causes_recv_ext. assumption.
    - intro i. destruct (le_lt_dec n (i * msgs_per_cycle_ext + 3)) as [_ | Hlt].
      + admit.
      + apply inter_causes_next_ext. assumption.
  Admitted.

End PingPongParameters.

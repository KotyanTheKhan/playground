From HappenedBefore Require Import EventStructure CausalRelation HappenedBefore PosetInstance.
From Stdlib Require Import Arith Lia Bool PeanoNat.
From HappenedBeforePingPong Require Import Helpers Definitions FixedHistory.

(**
  Protocol typeclass, extended history, and IsPairAlternatingSymPingPong instance.
*)

Section PingPongParameters.

  Variable GAP_0 : nat.
  Variable GAP_1 : nat.

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

  (* ── Extended history ───────────────────────────────────────────────────── *)

  (**
    The extended history adds local-order and inter-cycle messages needed
    to prove all IsPairAlternatingSymPingPong axioms.

    Message layout per cycle:
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
      {| send_event := event_1 GAP_1 i 0; recv_event := event_1 GAP_1 i 1 |}  (* P1 is responder *)
    else
      {| send_event := event_0 GAP_0 i 0; recv_event := event_0 GAP_0 i 1 |}. (* P0 is responder *)

  (**
    Inter-cycle synchronization: pong_recv of cycle i triggers ping_send of
    cycle i+1.  Because roles alternate, these events are on different
    processes, so an explicit causal message is needed.
  *)
  Definition msg_inter_cycle (i : nat) : Message :=
    if Nat.even i then
      {| send_event := event_0 GAP_0 i 1; recv_event := event_1 GAP_1 (S i) 0 |}
    else
      {| send_event := event_1 GAP_1 i 1; recv_event := event_0 GAP_0 (S i) 0 |}.

  Definition msgs_per_cycle_ext : nat := 4 + GAP_0 + GAP_1.

  Definition nth_message_ext (n : nat) : Message :=
    let cycle := n / msgs_per_cycle_ext in
    let phase := n mod msgs_per_cycle_ext in
    let txn   := get_transaction GAP_0 GAP_1 cycle in
    if nat_eqb phase 0 then
      txn.(pp_ping)
    else if nat_eqb phase 1 then
      msg_turn cycle
    else if nat_eqb phase 2 then
      txn.(pp_pong)
    else if nat_eqb phase 3 then
      msg_inter_cycle cycle
    else if nat_leb phase (3 + GAP_0) then
      msg_internal_chain 0 (p0_base_index GAP_0 cycle) (phase - 4)
    else
      msg_internal_chain 1 (p1_base_index GAP_1 cycle) (phase - (4 + GAP_0)).

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

  Lemma ping_is_nth_message_ext : forall i,
    nth_message_ext (i * msgs_per_cycle_ext) = (get_transaction GAP_0 GAP_1 i).(pp_ping).
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
    nth_message_ext (i * msgs_per_cycle_ext + 2) = (get_transaction GAP_0 GAP_1 i).(pp_pong).
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
    In (get_transaction GAP_0 GAP_1 i).(pp_ping) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- ping_is_nth_message_ext.
    apply nth_message_ext_in_history. assumption.
  Qed.

  Lemma turn_in_history_ext : forall n i, i * msgs_per_cycle_ext + 1 < n ->
    In (msg_turn i) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- turn_is_nth_message_ext.
    apply nth_message_ext_in_history. assumption.
  Qed.

  Lemma pong_in_history_ext : forall n i, i * msgs_per_cycle_ext + 2 < n ->
    In (get_transaction GAP_0 GAP_1 i).(pp_pong) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- pong_is_nth_message_ext.
    apply nth_message_ext_in_history. assumption.
  Qed.

  Lemma inter_in_history_ext : forall n i, i * msgs_per_cycle_ext + 3 < n ->
    In (msg_inter_cycle i) (pp_history_ext n).
  Proof.
    intros n i Hi. rewrite <- inter_is_nth_message_ext.
    apply nth_message_ext_in_history. assumption.
  Qed.

  (* ── Extended-history causality lemmas ───────────────────────────────────  *)

  Lemma ping_causes_recv_ext : forall n i, i * msgs_per_cycle_ext < n ->
    happened_before (pp_history_ext n)
      (map_ping_send GAP_0 GAP_1 i) (map_ping_recv GAP_0 GAP_1 i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction GAP_0 GAP_1 i).(pp_ping). split.
    - apply ping_in_history_ext; assumption.
    - unfold map_ping_send, map_ping_recv. split; reflexivity.
  Qed.

  Lemma turn_causes_pong_ext : forall n i, i * msgs_per_cycle_ext + 1 < n ->
    happened_before (pp_history_ext n)
      (map_ping_recv GAP_0 GAP_1 i) (map_pong_send GAP_0 GAP_1 i).
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
    happened_before (pp_history_ext n)
      (map_pong_send GAP_0 GAP_1 i) (map_pong_recv GAP_0 GAP_1 i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction GAP_0 GAP_1 i).(pp_pong). split.
    - apply pong_in_history_ext; assumption.
    - unfold map_pong_send, map_pong_recv. split; reflexivity.
  Qed.

  Lemma even_succ_negb : forall i, Nat.even (S i) = negb (Nat.even i).
  Proof. intro i. rewrite Nat.even_succ. reflexivity. Qed.

  Lemma inter_causes_next_ext : forall n i, i * msgs_per_cycle_ext + 3 < n ->
    happened_before (pp_history_ext n)
      (map_pong_recv GAP_0 GAP_1 i) (map_ping_send GAP_0 GAP_1 (S i)).
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

  (* ── Colimit relation ────────────────────────────────────────────────────  *)

  Definition hb_inf (e1 e2 : Event) : Prop :=
    exists n, happened_before (pp_history_ext n) e1 e2.

  (* ── IsPairAlternatingSymPingPong instance ───────────────────────────────  *)

  (**
    The four causality axioms, each proved via [hb_inf]:
    choose a minimal [n] that places the relevant message in the history,
    then apply the corresponding in-range causality lemma.
  *)

  Lemma ax_ping : forall i,
    hb_inf (map_ping_send GAP_0 GAP_1 i) (map_ping_recv GAP_0 GAP_1 i).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 1).
    apply ping_causes_recv_ext. lia.
  Qed.

  Lemma ax_turn : forall i,
    hb_inf (map_ping_recv GAP_0 GAP_1 i) (map_pong_send GAP_0 GAP_1 i).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 2).
    apply turn_causes_pong_ext. lia.
  Qed.

  Lemma ax_pong : forall i,
    hb_inf (map_pong_send GAP_0 GAP_1 i) (map_pong_recv GAP_0 GAP_1 i).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 3).
    apply pong_causes_recv_ext. lia.
  Qed.

  Lemma ax_next : forall i,
    hb_inf (map_pong_recv GAP_0 GAP_1 i) (map_ping_send GAP_0 GAP_1 (S i)).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 4).
    apply inter_causes_next_ext. lia.
  Qed.

  Instance ex_is_ping_pong : IsPairAlternatingSymPingPong hb_inf.
  Proof.
    exact {|
      map_cycle_ping_send := map_ping_send GAP_0 GAP_1;
      map_cycle_ping_recv := map_ping_recv GAP_0 GAP_1;
      map_cycle_pong_send := map_pong_send GAP_0 GAP_1;
      map_cycle_pong_recv := map_pong_recv GAP_0 GAP_1;
      ax_even_init := map_ping_send_even_process GAP_0 GAP_1;
      ax_even_resp := map_ping_recv_even_process GAP_0 GAP_1;
      ax_odd_init  := map_ping_send_odd_process  GAP_0 GAP_1;
      ax_odd_resp  := map_ping_recv_odd_process  GAP_0 GAP_1;
      ax_ping_rel  := ax_ping;
      ax_turn_rel  := ax_turn;
      ax_pong_rel  := ax_pong;
      ax_next_rel  := ax_next
    |}.
  Defined.

End PingPongParameters.
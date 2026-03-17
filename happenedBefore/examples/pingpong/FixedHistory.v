From HappenedBefore Require Import EventStructure CausalRelation HappenedBefore PosetInstance.
From Stdlib Require Import Arith Lia Bool PeanoNat.
From HappenedBeforePingPong Require Import Helpers Definitions.

(**
  Fixed history, rank function, and acyclicity for the ping-pong protocol.
*)

Section PingPongParameters.

  Variable GAP_0 : nat.
  Variable GAP_1 : nat.

  (* Shorthand notations for events-per-cycle (both processes). *)
  Notation p0_epc := (p0_events_per_cycle GAP_0).
  Notation p1_epc := (p1_events_per_cycle GAP_1).

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
    let txn   := get_transaction GAP_0 GAP_1 cycle in
    if nat_eqb phase 0 then
      txn.(pp_ping)
    else if nat_eqb phase 1 then
      txn.(pp_pong)
    else if nat_leb phase (1 + GAP_0) then
      msg_internal_chain 0 (p0_base_index GAP_0 cycle) (phase - 2)
    else
      msg_internal_chain 1 (p1_base_index GAP_1 cycle) (phase - (2 + GAP_0)).

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
    k < GAP_0 -> (p0_base_index GAP_0 i + 1 + k) / p0_epc = i.
  Proof.
    intros i k Hk. unfold p0_base_index, p0_events_per_cycle.
    apply int_event_same_cycle. assumption.
  Qed.

  Lemma p0_int_event_offset : forall i k,
    k < GAP_0 -> (p0_base_index GAP_0 i + 1 + k) mod p0_epc = 1 + k.
  Proof.
    intros i k Hk. unfold p0_base_index, p0_events_per_cycle.
    apply int_event_offset. assumption.
  Qed.

  Lemma rank_mono_p0_int : forall i k, S k < GAP_0 ->
    rank ⟨0, p0_base_index GAP_0 i + 1 + k⟩ < rank ⟨0, p0_base_index GAP_0 i + 1 + S k⟩.
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
    k < GAP_1 -> (p1_base_index GAP_1 i + 1 + k) / p1_epc = i.
  Proof.
    intros i k Hk. unfold p1_base_index, p1_events_per_cycle.
    apply int_event_same_cycle. assumption.
  Qed.

  Lemma p1_int_event_offset : forall i k,
    k < GAP_1 -> (p1_base_index GAP_1 i + 1 + k) mod p1_epc = 1 + k.
  Proof.
    intros i k Hk. unfold p1_base_index, p1_events_per_cycle.
    apply int_event_offset. assumption.
  Qed.

  Lemma rank_mono_p1_int : forall i k, S k < GAP_1 ->
    rank ⟨1, p1_base_index GAP_1 i + 1 + k⟩ < rank ⟨1, p1_base_index GAP_1 i + 1 + S k⟩.
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

  (* ── Fixed history membership ──────────────────────────────────────────── *)

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
    nth_message_fixed (i * msgs_per_cycle_fixed) = (get_transaction GAP_0 GAP_1 i).(pp_ping).
  Proof.
    intro i. unfold nth_message_fixed.
    assert (Hdiv : i * msgs_per_cycle_fixed / msgs_per_cycle_fixed = i)
      by (apply Nat.div_mul; unfold msgs_per_cycle_fixed; lia).
    assert (Hmod : i * msgs_per_cycle_fixed mod msgs_per_cycle_fixed = 0)
      by (apply Nat.Div0.mod_mul).
    rewrite Hdiv, Hmod. simpl. reflexivity.
  Qed.

  Lemma pong_is_nth_message : forall i,
    nth_message_fixed (i * msgs_per_cycle_fixed + 1) = (get_transaction GAP_0 GAP_1 i).(pp_pong).
  Proof.
    intro i. unfold nth_message_fixed.
    assert (Hdiv : (i * msgs_per_cycle_fixed + 1) / msgs_per_cycle_fixed = i)
      by (apply div_mul_add_small; unfold msgs_per_cycle_fixed; lia).
    assert (Hmod : (i * msgs_per_cycle_fixed + 1) mod msgs_per_cycle_fixed = 1)
      by (apply mod_mul_add_small; unfold msgs_per_cycle_fixed; lia).
    rewrite Hdiv, Hmod. reflexivity.
  Qed.

  (** If cycle i fits within the first [n] messages, both interaction events are present. *)
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
    i * msgs_per_cycle_fixed < n ->
    In (get_transaction GAP_0 GAP_1 i).(pp_ping) (pp_history_fixed n).
  Proof.
    intros n i Hi. rewrite <- ping_is_nth_message. apply nth_message_in_history. assumption.
  Qed.

  Lemma pong_in_history : forall n i,
    i * msgs_per_cycle_fixed + 1 < n ->
    In (get_transaction GAP_0 GAP_1 i).(pp_pong) (pp_history_fixed n).
  Proof.
    intros n i Hi. rewrite <- pong_is_nth_message. apply nth_message_in_history. assumption.
  Qed.

  Lemma ping_in_sufficient_history : forall n i,
    i < n / msgs_per_cycle_fixed ->
    In (get_transaction GAP_0 GAP_1 i).(pp_ping) (pp_history_fixed n).
  Proof.
    intros n i Hi. apply ping_in_history.
    assert (H := history_contains_cycle n i Hi). unfold msgs_per_cycle_fixed in *. lia.
  Qed.

  Lemma pong_in_sufficient_history : forall n i,
    i < n / msgs_per_cycle_fixed ->
    In (get_transaction GAP_0 GAP_1 i).(pp_pong) (pp_history_fixed n).
  Proof.
    intros n i Hi. apply pong_in_history. apply history_contains_cycle. assumption.
  Qed.

  (* ── Fixed-history causality lemmas ────────────────────────────────────── *)

  Lemma ping_causes_recv : forall n i, i * msgs_per_cycle_fixed < n ->
    happened_before (pp_history_fixed n)
      (map_ping_send GAP_0 GAP_1 i) (map_ping_recv GAP_0 GAP_1 i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction GAP_0 GAP_1 i).(pp_ping). split.
    - apply ping_in_history; assumption.
    - unfold map_ping_send, map_ping_recv. split; reflexivity.
  Qed.

  Lemma pong_causes_recv : forall n i, i * msgs_per_cycle_fixed + 1 < n ->
    happened_before (pp_history_fixed n)
      (map_pong_send GAP_0 GAP_1 i) (map_pong_recv GAP_0 GAP_1 i).
  Proof.
    intros n i Hi. apply hb_message. unfold message_link.
    exists (get_transaction GAP_0 GAP_1 i).(pp_pong). split.
    - apply pong_in_history; assumption.
    - unfold map_pong_send, map_pong_recv. split; reflexivity.
  Qed.

End PingPongParameters.

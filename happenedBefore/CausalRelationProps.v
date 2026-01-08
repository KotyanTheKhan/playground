(* Properties of Causal Relations *)
Require Import EventStructure.
Require Import CausalRelation.
From Stdlib Require Import Lia.

(* ========== Helper Lemmas ========== *)

(* same_process_before is irreflexive *)
Lemma same_process_before_irrefl : forall e,
  ~ same_process_before e e.
Proof.
  intros e [_ H].
  lia.
Qed.

(* same_process_before is asymmetric *)
Lemma same_process_before_asymm : forall e1 e2,
  same_process_before e1 e2 ->
  ~ same_process_before e2 e1.
Proof.
  intros e1 e2 [Hproc H12] [_ H21].
  lia.
Qed.

(* If e1 and e2 are related by happened-before in both directions,
   and one direction uses only hb_refl, then e1 = e2 *)
Lemma hb_refl_antisym : forall h e1 e2,
  happened_before h e1 e2 ->
  e1 = e2 ->
  happened_before h e2 e1 ->
  e1 = e2.
Proof.
  intros h e1 e2 _ Heq _.
  exact Heq.
Qed.

(* Key lemma: if same_process_before e1 e2, then not (happened_before h e2 e1)
   unless e2 = e1, but same_process_before is irreflexive, so this is impossible *)
Lemma same_process_before_no_hb_back : forall h e1 e2,
  same_process_before e1 e2 ->
  happened_before h e2 e1 ->
  False.
Proof.
  intros h e1 e2 Hsame Hhb.
  generalize dependent Hsame.
  induction Hhb as [e | e2' e1' Hlocal | e2' e1' Hmsg | e2' e' e1' Hhb21 IH1 Hhb_e1 IH2];
    intros Hsame.
  - (* hb_refl: e2 = e1, contradiction with clock e1 < clock e2 *)
    destruct Hsame as [_ Hclk].
    lia.
  - (* hb_local: same_process_before e2 e1, i.e., clock e2 < clock e1 *)
    destruct Hsame as [_ Hclk12].
    destruct Hlocal as [_ Hclk21].
    (* We have clock e1 < clock e2 and clock e2 < clock e1, contradiction *)
    lia.
  - (* hb_message: message_link h e2 e1, and we have same_process_before e1 e2
       This means e1' and e2' are on the same process with e1' < e2',
       and there's a message from e2' to e1'. *)
    destruct Hmsg as [m [Hin [Hsend Hrecv]]].
    (* same_process_before e1' e2' -> clock e1' < clock e2' *)
    destruct Hsame as [_ Hclk12].
    (* message from e2' to e1' -> clock e2' < clock e1' (by Lamport axiom) *)
    assert (Hclk21: clock e2' < clock e1').
    { rewrite <- Hsend. rewrite <- Hrecv. apply (clock_lt m). }
    (* Contradiction *)
    lia.
  - (* hb_trans: e2 ≺ e' ≺ e1, and we have same_process_before e1 e2 (e1 < e2 locally)
       After induction, we have e2', e', e1' where e2 = e2', e1 = e1'
       We have: happened_before h e2' e1' (by transitivity: e2' ≺ e' ≺ e1')
       And:     same_process_before e1' e2', which gives happened_before h e1' e2'
       Now we have happened_before in both directions, so by acyclicity axiom: e1' = e2'
       But same_process_before e1' e2' means e1' ≠ e2' (different clocks), contradiction! *)
    exfalso.
    destruct Hsame as [Hproc Hclk].
    (* e1' and e2' have different clocks *)
    (* Apply acyclicity: happened_before h e1' e2' and happened_before h e2' e1' -> e1' = e2' *)
    assert (Heq: e1' = e2').
    { apply happened_before_acyclic with (h := h).
      - apply hb_local. split; assumption.
      - eapply hb_trans; eassumption. }
    (* But different clocks means e1' <> e2' *)
    subst e2'.
    lia.
Qed.

(* Similarly for message_link *)
Lemma message_link_no_hb_back : forall h e1 e2,
  message_link h e1 e2 ->
  happened_before h e2 e1 ->
  False.
Proof.
  intros h e1 e2 Hmsg Hhb.
  generalize dependent Hmsg.
  induction Hhb as [e | e2' e1' Hlocal | e2' e1' Hmsg' | e2' e' e1' Hhb21 IH1 Hhb_e1 IH2];
    intros Hmsg.
  - (* hb_refl: e = e2 = e1, but message_link h e1 e1
       This would mean a message from an event to itself *)
    destruct Hmsg as [m [_ [Hsend Hrecv]]].
    subst.
    (* send_event m = e and recv_event m = e *)
    (* Use the lemma message_connects_distinct_events *)
    apply message_connects_distinct_events with (m := m).
    congruence.
  - (* hb_local: e2 < e1 on same process, and message_link h e1 e2
       This represents a message from e1' to e2' where they're on the same process. *)
    destruct Hmsg as [m [Hin [Hsend Hrecv]]].
    (* same_process_before e2' e1' -> clock e2' < clock e1' *)
    destruct Hlocal as [_ Hclk21].
    (* message from e1' to e2' -> clock e1' < clock e2' (by Lamport axiom) *)
    assert (Hclk12: clock e1' < clock e2').
    { rewrite <- Hsend. rewrite <- Hrecv. apply (clock_lt m). }
    (* Contradiction *)
    lia.
  - (* hb_message: message_link h e2 e1, and we have message_link h e1 e2
       After induction: e2' = e2, e1' = e1, Hmsg' is message_link h e2' e1'
       This creates a message cycle: e1 -> e2 -> e1.
       By acyclicity, if happened_before in both directions, events are equal.
       But messages connect distinct events (by axiom), contradiction! *)
    exfalso.
    destruct Hmsg as [m1 [Hin1 [Hsend1 Hrecv1]]].
    destruct Hmsg' as [m2 [Hin2 [Hsend2 Hrecv2]]].
    (* By acyclicity: e1' = e2' *)
    assert (Heq: e1' = e2').
    { apply happened_before_acyclic with (h := h).
      - apply hb_message. exists m1. split; [|split]; assumption.
      - apply hb_message. exists m2. split; [|split]; assumption. }
    (* m1 has send_event m1 = e1' and recv_event m1 = e2' *)
    (* After substitution e1' = e2', we get send_event m1 = recv_event m1 *)
    eapply message_connects_distinct_events with (m := m1).
    subst.
    congruence.
  - (* hb_trans: e2 ≺ e' ≺ e1, and message_link h e1 e2
       We have: happened_before h e2' e1' (from trans)
       And:     message_link h e1' e2', giving happened_before h e1' e2'
       By acyclicity: e1' = e2'
       But message_link connects distinct events, contradiction! *)
    exfalso.
    destruct Hmsg as [m [Hin [Hsend Hrecv]]].
    assert (Heq: e1' = e2').
    { apply happened_before_acyclic with (h := h).
      - apply hb_message. exists m. split; [|split]; assumption.
      - eapply hb_trans; eassumption. }
    (* send_event m = e1' = e2' = recv_event m *)
    eapply message_connects_distinct_events with (m := m).
    transitivity e1'; [exact Hsend | transitivity e2'; [exact Heq | exact (eq_sym Hrecv)]].
Qed.

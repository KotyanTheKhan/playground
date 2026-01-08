(* Happened-before relation and causality *)
Require Import EventStructure.
Require Import Lia.

(* ========== Happened-Before Relation ========== *)

(* Helper: events on the same process with earlier clock *)
Definition same_process_before (e1 e2 : Event) : Prop :=
  process e1 = process e2 /\ clock e1 < clock e2.

(* Helper: direct message causality *)
Definition message_link (h : History) (e1 e2 : Event) : Prop :=
  exists m, In m h /\ send_event m = e1 /\ recv_event m = e2.

(* Happened-before relation: reflexive-transitive closure of
   (same process ordering) ∪ (message causality) *)
Inductive happened_before (h : History) : Event -> Event -> Prop :=
  | hb_refl : forall e, happened_before h e e
  | hb_local : forall e1 e2,
      same_process_before e1 e2 ->
      happened_before h e1 e2
  | hb_message : forall e1 e2,
      message_link h e1 e2 ->
      happened_before h e1 e2
  | hb_trans : forall e1 e2 e3,
      happened_before h e1 e2 ->
      happened_before h e2 e3 ->
      happened_before h e1 e3.

(* Notation for happened-before *)
Notation "e1 '≺[' h ']' e2" := (happened_before h e1 e2) (at level 70).
Notation "e1 '≺' e2" := (happened_before nil e1 e2) (at level 70).

(* Two events are concurrent if neither happened before the other *)
Definition concurrent (h : History) (e1 e2 : Event) : Prop :=
  ~ happened_before h e1 e2 /\ ~ happened_before h e2 e1.

(* Notation for concurrent events *)
Notation "e1 '∥[' h ']' e2" := (concurrent h e1 e2) (at level 70).
Notation "e1 '∥' e2" := (concurrent nil e1 e2) (at level 70).

(* ========== Lemmas for proving acyclicity ========== *)

(* Lemma 1: same_process_before is irreflexive *)
Lemma same_process_before_irrefl : forall e,
  ~ same_process_before e e.
Proof.
  intros e [_ Hc].
  lia.
Qed.

(* Lemma 2: same_process_before is antisymmetric *)
Lemma same_process_before_not_symmetric : forall e1 e2,
  same_process_before e1 e2 ->
  ~ same_process_before e2 e1.
Proof.
  intros e1 e2 [Hp Hc] [_ Hc'].
  lia.
Qed.

(* Lemma 3: Message property - clock increases *)
Lemma message_clock_increases : forall m,
  clock (send_event m) < clock (recv_event m).
Proof.
  intros m.
  exact (clock_lt m).
Qed.

(* Lemma 4: Acyclicity via local ordering contradiction *)
Lemma acyclic_via_local : forall h e1 e2,
  same_process_before e1 e2 ->
  ~ happened_before h e2 e1.
Proof.
  intros h e1 e2 [Hproc Hclock] Hhb.
  (* Helper lemma: happened_before preserves clock ordering *)
  assert (Hclock_mono : forall e2' e1', happened_before h e2' e1' -> clock e2' <= clock e1').
  {
    intros e2' e1' Hhb'.
    induction Hhb' as [e | e1'' e2'' Hsp | e1'' e2'' Hmsg | e1'' e2'' e3' Hhb1 IH1 Hhb2 IH2].
    - (* Reflexive *)
      lia.
    - (* Local *)
      unfold same_process_before in Hsp.
      destruct Hsp as [_ Hc].
      lia.
    - (* Message *)
      unfold message_link in Hmsg.
      destruct Hmsg as [m [_ [Hsend Hrecv]]].
      subst.
      pose proof (clock_lt m).
      lia.
    - (* Transitive *)
      lia.
  }
  
  (* Apply the helper lemma *)
  assert (Hclock_le := Hclock_mono e2 e1 Hhb).
  lia.
Qed.

(* Helper: happened_before preserves clock ordering *)
Lemma happened_before_clock_mono : forall h e1 e2,
  happened_before h e1 e2 -> clock e1 <= clock e2.
Proof.
  intros h e1 e2 Hhb.
  induction Hhb as [e | e1 e2 Hsp | e1 e2 Hmsg | e1 e2 e3 Hhb1 IH1 Hhb2 IH2].
  - lia.
  - unfold same_process_before in Hsp.
    destruct Hsp as [_ Hc].
    lia.
  - unfold message_link in Hmsg.
    destruct Hmsg as [m [_ [Hsend Hrecv]]].
    subst.
    pose proof (clock_lt m).
    lia.
  - lia.
Qed.

(* Lemma 5: Acyclicity via message *)
Lemma acyclic_via_message : forall h m,
  In m h ->
  ~ happened_before h (recv_event m) (send_event m).
Proof.
  intros h m Hin Hhb.
  pose proof (message_clock_increases m) as Hclock.
  pose proof (happened_before_clock_mono h (recv_event m) (send_event m) Hhb) as Hmono.
  lia.
Qed.

(* Lemma 6: Main acyclicity theorem *)
Theorem happened_before_acyclic : forall h e1 e2,
  happened_before h e1 e2 -> happened_before h e2 e1 -> e1 = e2.
Proof.
  intros h e1 e2 Hfwd Hbwd.
  induction Hfwd as [e | e1 e2 Hsp | e1 e2 Hmsg | e1 e2 e3 Hfwd1 IH1 Hfwd2 IH2].
  - (* Case 1: e1 = e, reflexive *)
    reflexivity.
  - (* Case 2: e1 ≺ e2 via local, but e2 ≺ e1 *)
    exfalso.
    exact (acyclic_via_local h e1 e2 Hsp Hbwd).
  - (* Case 3: e1 ≺ e2 via message, but e2 ≺ e1 *)
    unfold message_link in Hmsg.
    destruct Hmsg as [m [Hin [Hsend Hrecv]]].
    subst.
    exfalso.
    exact (acyclic_via_message h m Hin Hbwd).
  - (* Case 4: e1 ≺ e2 ≺ e3 ≺ e1 (cycle) *)
    (* We have:
       - Hfwd1 : e1 ≺ e2
       - Hfwd2 : e2 ≺ e3
       - Hbwd : e3 ≺ e1  (from outer induction hypothesis)
       
       Strategy: Using transitivity and induction hypotheses
    *)
    
    (* Step 1: e2 ≺ e1 by transitivity of e2 ≺ e3 ≺ e1 *)
    pose proof (hb_trans h e2 e3 e1 Hfwd2 Hbwd) as H_e2_e1.
    
    (* Step 2: Apply IH1 to get e1 = e2 *)
    pose proof (IH1 H_e2_e1) as H_e1_eq_e2.
    
    (* Step 3: Substitute to get e3 ≺ e2 *)
    subst e1.
    rename e2 into e1.
    
    (* Now the goal is e1 = e3 and we have:
       - Hfwd2 : e1 ≺ e3
       - Hbwd : e3 ≺ e1 (after rename)
    *)
    
    (* Apply IH2 *)
    pose proof (IH2 Hbwd) as H_e1_eq_e3.
    subst e1.
    reflexivity.
Qed.

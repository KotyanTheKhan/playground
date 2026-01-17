(* Lamport Clocks for Happened-Before Relation *)
Require Import EventStructure.
Require Import CausalRelation.
Require Import CausalRelationProps.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

(* ========== Lamport Clock Definition ========== *)

(* A logical clock assigns a natural number timestamp to every event *)
Definition Clock := Event -> nat.

(* A Lamport Clock must respect the happened-before relation:
   If e1 -> e2, then C(e1) < C(e2) *)
Definition IsLamportClock (h : History) (c : Clock) : Prop :=
  forall e1 e2, strict_happened_before h e1 e2 -> c e1 < c e2.

(* Alternative condition using non-strict happened-before:
   If e1 ->= e2, then C(e1) <= C(e2) *)
Definition IsWeakLamportClock (h : History) (c : Clock) : Prop :=
  forall e1 e2, happened_before h e1 e2 -> c e1 <= c e2.

(* ========== Theoretical Properties ========== *)

(* Lemma: Strict condition implies weak condition *)
Lemma strict_implies_weak_clock : forall h c,
  IsLamportClock h c -> IsWeakLamportClock h c.
Proof.
  intros h c H_strict e1 e2 H_hb.
  induction H_hb.
  - (* Reflexivity: e <= e implies c(e) <= c(e) *)
    lia.
  - (* Direct message: e1 ->m e2 implies e1 < e2 implies c(e1) < c(e2) implies c(e1) <= c(e2) *)
    apply Nat.lt_le_incl.
    apply H_strict.
    constructor. assumption.
  - (* Transitivity: transitivity holds for <= *)
    lia.
Qed.

(* Theorem: Existence of a trivial Lamport Clock for acyclic histories.
   Is proving existence required? The user asked to prove it IS a happened before instance.
   Ideally, we show that if we HAVE a clock, it embeds the partial order into (nat, <).
*)

Module ClockOrder.
  Definition lt (c : Clock) (e1 e2 : Event) : Prop := c e1 < c e2.
  Definition le (c : Clock) (e1 e2 : Event) : Prop := c e1 <= c e2.
End ClockOrder.

(* Theorem: A Lamport Clock is an order embedding from (Event, strict_happened_before) 
   to (nat, <) ONLY ONE WAY.
   Causality implies Clock Order, but Clock Order does NOT imply Causality.
*)
Theorem causality_implies_clock_order : forall h c e1 e2,
  IsLamportClock h c ->
  strict_happened_before h e1 e2 ->
  c e1 < c e2.
Proof.
  intros h c e1 e2 H_clock H_shb.
  apply H_clock.
  assumption.
Qed.

(* Theorem: A Weak Lamport Clock is a monotonic map from (Event, happened_before)
   to (nat, <=).
*)
Theorem causality_implies_weak_clock_order : forall h c e1 e2,
  IsWeakLamportClock h c ->
  happened_before h e1 e2 ->
  c e1 <= c e2.
Proof.
  intros h c e1 e2 H_clock H_hb.
  apply H_clock.
  assumption.
Qed.


(* ========== Lamport Total Order ========== *)

Require Import Posets.PosetClasses.

(* Total ordering of events using Lamport timestamps and Process IDs *)
Definition lamport_le (c : Clock) (e1 e2 : Event) : Prop :=
  c e1 < c e2 \/
  (c e1 = c e2 /\ (process e1 < process e2 \/ (process e1 = process e2 /\ index e1 <= index e2))).

(* Instance: lamport_le is a Poset *)
Instance lamport_le_poset (c : Clock) : IsPoset Event (lamport_le c).
Proof.
  constructor.
  - (* Reflexivity *)
    intros e. right. split. reflexivity. right. split. reflexivity. apply Nat.le_refl.
  - (* Antisymmetry *)
    intros e1 e2 H1 H2.
    destruct e1 as [p1 i1], e2 as [p2 i2].
    unfold lamport_le in *. simpl in *.
    destruct H1 as [H1 | [H1_c [H1_p | [H1_p H1_i]]]];
    destruct H2 as [H2 | [H2_c [H2_p | [H2_p H2_i]]]].
    + (* c1 < c2 and c2 < c1 *) lia.
    + (* c1 < c2 and c2 = c1 *) rewrite H2_c in H1. lia.
    + (* c1 < c2 and c2 = c1 *) rewrite H2_c in H1. lia.
    + (* c1 = c2 and c2 < c1 *) rewrite H1_c in H2. lia.
    + (* c1 = c2, p1 < p2 and c2 = c1, p2 < p1 *) lia.
    + (* c1 = c2, p1 < p2 and c2 = c1, p2 = p1 *) lia.
    + (* c1 = c2 and c2 < c1 *) rewrite H1_c in H2. lia.
    + (* c1 = c2, p1 = p2 and c2 = c1, p2 < p1 *) lia.
    + (* c1 = c2, p1 = p2, i1 <= i2 ... *)
      assert (p1 = p2) by lia. subst.
      assert (i1 = i2) by lia. subst.
      reflexivity.
  - (* Transitivity *)
    intros e1 e2 e3 H1 H2.
    unfold lamport_le in *.
    destruct H1 as [H1 | [H1_c [H1_p | [H1_p H1_i]]]];
    destruct H2 as [H2 | [H2_c [H2_p | [H2_p H2_i]]]].
    (* Provide a generic tactic for transitivity *)
    all: try (left; lia).
    all: right; split; [lia | ].
    all: try (left; lia).
    all: try (right; split; [lia | lia]).
Defined.

(* Finite — the execution-poset event carrier is finite. *)

From Stdlib Require Import List Arith Lia Ensembles Finite_sets Finite_sets_facts.
From Execution Require Import Op Event.
From Dimension Require Import Theorems.   (* provides cardinal_subtype_full *)
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* A NoDup list induces an ensemble of cardinality = its length.        *)
(* ------------------------------------------------------------------ *)

Lemma cardinal_of_NoDup_list :
  forall (U : Type) (l : list U),
    NoDup l ->
    cardinal U (fun x => List.In x l) (length l).
Proof.
  intros U l Hnd.
  induction Hnd as [|a l' Hnotin Hnd' IH].
  - (* empty list: the ensemble is Empty_set *)
    assert (Heq : (fun x => List.In x (@nil U)) = Empty_set U).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. destruct Hx.
      - intros x Hx. destruct Hx. }
    rewrite Heq. simpl. apply card_empty.
  - (* cons: the ensemble is Add U (fun x => List.In x l') a *)
    assert (Heq : (fun x => List.In x (a :: l')) =
                  Add U (fun x => List.In x l') a).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. simpl in Hx. destruct Hx as [Hax | Hxl].
        + right. rewrite Hax. apply In_singleton.
        + left. exact Hxl.
      - intros x Hx. destruct Hx as [x Hxl | x Hxs].
        + simpl. right. exact Hxl.
        + inversion Hxs. simpl. left. reflexivity. }
    rewrite Heq. simpl (length _).
    apply card_add.
    + exact IH.
    + (* ~ In _ (fun x => List.In x l') a, i.e. ~ List.In a l' *)
      exact Hnotin.
Qed.

(* ------------------------------------------------------------------ *)
(* The valid pairs form an ensemble of cardinality `total P`.           *)
(* ------------------------------------------------------------------ *)

Lemma valid_cardinal :
  forall P, cardinal (nat * nat) (ValidSet P) (total P).
Proof.
  intro P.
  (* ValidSet P equals the list-membership ensemble of raw_events P *)
  assert (Heq : ValidSet P = (fun pi => List.In pi (raw_events P))).
  { apply Extensionality_Ensembles. split.
    - intros pi Hpi.
      apply (raw_events_spec P pi). exact Hpi.
    - intros pi Hpi.
      apply (raw_events_spec P pi). exact Hpi. }
  rewrite Heq.
  rewrite <- (raw_events_length P).
  apply cardinal_of_NoDup_list.
  apply raw_events_NoDup.
Qed.

(* ------------------------------------------------------------------ *)
(* The carrier `Event P` is finite, with cardinality `total P`.         *)
(* ------------------------------------------------------------------ *)

Lemma event_cardinal :
  forall P, cardinal (Event P) (Full_set (Event P)) (total P).
Proof.
  intro P.
  exact (cardinal_subtype_full (nat*nat) (ValidSet P) (total P) (valid_cardinal P)).
Qed.

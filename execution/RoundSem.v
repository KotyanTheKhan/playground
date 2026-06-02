(* Barrier-round operational semantics with primitive per-process programs.
   The happened-before rhb is a barrier order; the clock (Task 3) is computed from
   nth r (prog p) -- p's own program -- with no Schedule projection (closes W-2). *)
From Stdlib Require Import List Arith Lia ProofIrrelevance.
From Posets Require Import PosetClasses.
From Execution Require Import Op OnlineClock OnlineClockLocal.
Import ListNotations.

Record RSys := { rs_nprocs : nat ; rs_nrounds : nat ; rs_prog : nat -> list Op }.

Definition rop (S : RSys) (p r : nat) : Op := nth r (rs_prog S p) Local.

Definition rvalid (S : RSys) (e : nat * nat) : Prop :=
  fst e < rs_nprocs S /\ snd e < rs_nrounds S.

Definition rwf (S : RSys) : Prop :=
  (forall p, p < rs_nprocs S -> length (rs_prog S p) = rs_nrounds S) /\
  (forall p r d t, p < rs_nprocs S -> r < rs_nrounds S -> rop S p r = Send d t ->
      d < rs_nprocs S /\ rop S d r = Recv p t) /\
  (forall p r s t, p < rs_nprocs S -> r < rs_nrounds S -> rop S p r = Recv s t ->
      s < rs_nprocs S /\ rop S s r = Send p t).

(* realized rendezvous edge: p sends to d AND d receives from p, in round r *)
Definition redge (S : RSys) (p d r : nat) : Prop :=
  (exists t, rop S p r = Send d t) /\ (exists t, rop S d r = Recv p t).

Definition rhb_same (S : RSys) (e e' : nat * nat) : Prop :=
  e = e' \/ (snd e = snd e' /\ redge S (fst e) (fst e') (snd e)).

Definition rhb (S : RSys) (e e' : nat * nat) : Prop :=
  snd e < snd e' \/ (snd e = snd e' /\ rhb_same S e e').

Definition REvent (S : RSys) : Type := { e : nat * nat | rvalid S e }.
Definition rhb_sub (S : RSys) (x y : REvent S) : Prop := rhb S (proj1_sig x) (proj1_sig y).

#[export] Instance rhb_IsPoset : forall S, IsPoset (REvent S) (rhb_sub S).
Proof.
  intro S. constructor.
  - (* refl *) intro x. unfold rhb_sub, rhb. right. split; [reflexivity | left; reflexivity].
  - (* antisym *) intros x y Hxy Hyx.
    assert (Hpe : proj1_sig x = proj1_sig y).
    { unfold rhb_sub, rhb in Hxy, Hyx.
      destruct Hxy as [Hlt1 | [He1 Hs1]]; destruct Hyx as [Hlt2 | [He2 Hs2]]; try lia.
      destruct Hs1 as [Hxy0 | [_ Hed1]]; [exact Hxy0|].
      destruct Hs2 as [Hyx0 | [_ Hed2]]; [symmetry; exact Hyx0|].
      exfalso. destruct Hed1 as [[t1 Hsend1] _]. destruct Hed2 as [_ [t2 Hrecv2]].
      rewrite <- He1 in Hrecv2. rewrite Hsend1 in Hrecv2. discriminate. }
    destruct x as [ex Hx]; destruct y as [ey Hy]; simpl in Hpe; subst ey.
    f_equal. apply proof_irrelevance.
  - (* trans *) intros x y z Hxy Hyz. unfold rhb_sub, rhb in *.
    destruct Hxy as [Hlt1 | [He1 Hs1]]; destruct Hyz as [Hlt2 | [He2 Hs2]];
      try (left; lia).
    right. split; [lia|].
    destruct Hs1 as [Hxy0 | [Hr1 Hed1]].
    + rewrite Hxy0. exact Hs2.
    + destruct Hs2 as [Hyz0 | [Hr2 Hed2]].
      * rewrite <- Hyz0. right. split; [exact Hr1 | exact Hed1].
      * exfalso. destruct Hed1 as [_ [t1 Hrecv1]]. destruct Hed2 as [[t2 Hsend2] _].
        rewrite He1 in Hrecv1. rewrite Hsend2 in Hrecv1. discriminate.
Qed.

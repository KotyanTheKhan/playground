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

(* ================================================================== *)
(* Part A — clock fields + trivial helpers                            *)
(* ================================================================== *)

Definition rlay  (S : RSys) (x : REvent S) : nat := snd (proj1_sig x).
Definition rcomp (S : RSys) (x : REvent S) : nat :=
  match rop S (fst (proj1_sig x)) (snd (proj1_sig x)) with Recv s _ => s | _ => fst (proj1_sig x) end.
Definition rstep (S : RSys) (x : REvent S) : nat :=
  match rop S (fst (proj1_sig x)) (snd (proj1_sig x)) with Recv _ _ => 1 | _ => 0 end.

Lemma revent_fst_lt : forall S (x : REvent S), fst (proj1_sig x) < rs_nprocs S.
Proof. intros S x. exact (proj1 (proj2_sig x)). Qed.
Lemma revent_snd_lt : forall S (x : REvent S), snd (proj1_sig x) < rs_nrounds S.
Proof. intros S x. exact (proj2 (proj2_sig x)). Qed.

Lemma rhb_barrier : forall S (x y : REvent S), rlay S x < rlay S y -> rhb_sub S x y.
Proof. intros S x y H. unfold rhb_sub, rhb, rlay in *. left. exact H. Qed.

Lemma rhb_resp_lay : forall S (x y : REvent S), rhb_sub S x y -> rlay S x <= rlay S y.
Proof. intros S x y [Hlt | [He _]]; unfold rlay; lia. Qed.

Lemma rcomp_lt_nprocs :
  forall S, rwf S -> forall x : REvent S, rcomp S x < rs_nprocs S.
Proof.
  intros S Hwf x. unfold rcomp.
  destruct (rop S (fst (proj1_sig x)) (snd (proj1_sig x))) as [|d t|s t] eqn:E.
  - apply revent_fst_lt.
  - apply revent_fst_lt.
  - destruct Hwf as [_ [_ Hrecv]].
    apply (Hrecv (fst (proj1_sig x)) (snd (proj1_sig x)) s t
                 (revent_fst_lt S x) (revent_snd_lt S x) E).
Qed.

(* ================================================================== *)
(* Part B — the three substantive structural lemmas                  *)
(* ================================================================== *)

(* Subtype equality from equal underlying pairs. *)
Lemma revent_eq_of_proj :
  forall S (x y : REvent S), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros S x y H. destruct x as [ex Hx]; destruct y as [ey Hy].
  simpl in H. subst ey. f_equal. apply proof_irrelevance.
Qed.

(* H1: an hb edge within a fixed layer forces equal rcomp (the sender). *)
Lemma rcomp_eq_of_rhb :
  forall S (x y : REvent S), rhb_sub S x y -> rlay S x = rlay S y -> rcomp S x = rcomp S y.
Proof.
  intros S x y Hhb Hlay. unfold rhb_sub, rhb, rlay in *.
  destruct Hhb as [Hlt | [_ Hsame]].
  - lia. (* rlay-equal contradicts snd<snd *)
  - destruct Hsame as [Heq | [Hidx Hed]].
    + apply revent_eq_of_proj in Heq. rewrite Heq. reflexivity.
    + (* redge (fst x)(fst y)(snd x) *)
      destruct Hed as [[ts Hsend] [tr Hrecv]].
      unfold rcomp.
      (* rcomp x : rop (fst x)(snd x) = Send (fst y) ts -> branch gives fst x *)
      rewrite Hsend.
      (* rcomp y : rop (fst y)(snd y) = rop (fst y)(snd x) = Recv (fst x) tr -> src = fst x *)
      rewrite <- Hlay. rewrite Hrecv. reflexivity.
Qed.

(* H2: two events in the same layer with the same rcomp are hb-comparable. *)
Lemma rhb_comparable_of_comp :
  forall S, rwf S -> forall x y : REvent S,
    rlay S x = rlay S y -> rcomp S x = rcomp S y ->
    rhb_sub S x y \/ rhb_sub S y x.
Proof.
  intros S Hwf x y Hlay Hcomp.
  destruct Hwf as [_ [_ Hrecv]].
  set (px := fst (proj1_sig x)) in *.
  set (py := fst (proj1_sig y)) in *.
  set (r  := snd (proj1_sig x)) in *.
  assert (Hry : snd (proj1_sig y) = r) by (unfold r, rlay in *; symmetry; exact Hlay).
  assert (Hpairx : proj1_sig x = (px, r)).
  { unfold px, r. rewrite (surjective_pairing (proj1_sig x)). reflexivity. }
  assert (Hpairy : proj1_sig y = (py, r)).
  { unfold py. rewrite (surjective_pairing (proj1_sig y)). rewrite Hry. reflexivity. }
  assert (Hpx : px < rs_nprocs S) by (unfold px; apply revent_fst_lt).
  assert (Hpy : py < rs_nprocs S) by (unfold py; apply revent_fst_lt).
  assert (Hrlt : r < rs_nrounds S) by (unfold r; apply revent_snd_lt).
  (* rcomp values, expressed at (px,r) / (py,r) *)
  assert (Hcx : rcomp S x = match rop S px r with Recv s _ => s | _ => px end).
  { unfold rcomp, px, r. reflexivity. }
  assert (Hcy : rcomp S y = match rop S py r with Recv s _ => s | _ => py end).
  { unfold rcomp. rewrite Hpairy. reflexivity. }
  rewrite Hcx, Hcy in Hcomp.
  destruct (rop S px r) as [|dx tx|sx tx] eqn:Ex;
  destruct (rop S py r) as [|dy ty|sy ty] eqn:Ey.
  (* px Local, py Local : px = py *)
  - assert (Hxy : x = y) by
      (apply revent_eq_of_proj; rewrite Hpairx, Hpairy, Hcomp; reflexivity).
    left. rewrite Hxy. apply poset_refl.
  (* px Local, py Send : px = py *)
  - assert (Hxy : x = y) by
      (apply revent_eq_of_proj; rewrite Hpairx, Hpairy, Hcomp; reflexivity).
    left. rewrite Hxy. apply poset_refl.
  (* px Local, py Recv sy : sy = px ; sender px sends to py *)
  - subst sy.
    (* rwf clause 3 on py: rop py r = Recv px ty -> rop px r = Send py ty.
       So x sends to y: redge px py r -> rhb x y. *)
    destruct (Hrecv py r px ty Hpy Hrlt Ey) as [_ Hsendpx].
    left. unfold rhb_sub, rhb. right. split.
    + rewrite Hpairx, Hpairy. reflexivity.
    + right. split.
      * rewrite Hpairx, Hpairy. reflexivity.
      * rewrite Hpairx, Hpairy. simpl. split.
        -- exists ty. exact Hsendpx.
        -- exists ty. exact Ey.
  (* px Send dx, py Local : px = py *)
  - assert (Hxy : x = y) by
      (apply revent_eq_of_proj; rewrite Hpairx, Hpairy, Hcomp; reflexivity).
    left. rewrite Hxy. apply poset_refl.
  (* px Send dx, py Send dy : px = py *)
  - assert (Hxy : x = y) by
      (apply revent_eq_of_proj; rewrite Hpairx, Hpairy, Hcomp; reflexivity).
    left. rewrite Hxy. apply poset_refl.
  (* px Send dx, py Recv sy : sy = px ; x sends to y -> rhb x y *)
  - subst sy.
    destruct (Hrecv py r px ty Hpy Hrlt Ey) as [_ Hsendpx].
    left. unfold rhb_sub, rhb. right. split.
    + rewrite Hpairx, Hpairy. reflexivity.
    + right. split.
      * rewrite Hpairx, Hpairy. reflexivity.
      * rewrite Hpairx, Hpairy. simpl. split.
        -- exists ty. exact Hsendpx.
        -- exists ty. exact Ey.
  (* px Recv sx, py Local : sx = py ; y sends to x -> rhb y x *)
  - subst sx.
    destruct (Hrecv px r py tx Hpx Hrlt Ex) as [_ Hsendpy].
    right. unfold rhb_sub, rhb. right. split.
    + rewrite Hpairx, Hpairy. reflexivity.
    + right. split.
      * rewrite Hpairx, Hpairy. reflexivity.
      * rewrite Hpairx, Hpairy. simpl. split.
        -- exists tx. exact Hsendpy.
        -- exists tx. exact Ex.
  (* px Recv sx, py Send dy : sx = py ; y sends to x -> rhb y x *)
  - subst sx.
    destruct (Hrecv px r py tx Hpx Hrlt Ex) as [_ Hsendpy].
    right. unfold rhb_sub, rhb. right. split.
    + rewrite Hpairx, Hpairy. reflexivity.
    + right. split.
      * rewrite Hpairx, Hpairy. reflexivity.
      * rewrite Hpairx, Hpairy. simpl. split.
        -- exists tx. exact Hsendpy.
        -- exists tx. exact Ex.
  (* px Recv sx, py Recv sy : sx = sy =: c ; c sends to both -> px = py *)
  - destruct (Hrecv px r sx tx Hpx Hrlt Ex) as [Hsxlt Hsendx].
    destruct (Hrecv py r sy ty Hpy Hrlt Ey) as [Hsylt Hsendy].
    subst sy. (* Hcomp : sx = sy was consumed by subst *)
    (* rop sx r = Send px tx and = Send px ty (since sy=sx) -> px = py *)
    rewrite Hsendx in Hsendy. injection Hsendy as Hpe _.
    assert (Hxy : x = y) by
      (apply revent_eq_of_proj; rewrite Hpairx, Hpairy, <- Hpe; reflexivity).
    left. rewrite Hxy. apply poset_refl.
Qed.

(* H3 / rank: within a fixed layer and component, the step counter linearizes hb. *)
Lemma rhb_rank :
  forall S, rwf S -> forall x y : REvent S,
    rlay S x = rlay S y -> rcomp S x = rcomp S y ->
    (rhb_sub S x y <-> rstep S x <= rstep S y).
Proof.
  intros S Hwf x y Hlay Hcomp. split.
  - (* rhb_sub x y -> rstep x <= rstep y *)
    intro Hhb. unfold rhb_sub, rhb, rlay in Hhb, Hlay.
    destruct Hhb as [Hlt | [_ Hsame]].
    + lia.
    + destruct Hsame as [Heq | [Hidx Hed]].
      * apply revent_eq_of_proj in Heq. rewrite Heq. lia.
      * (* redge (fst x)(fst y)(snd x): x is Send (rstep 0), y is Recv (rstep 1) *)
        destruct Hed as [[ts Hsend] [tr Hrecv]].
        unfold rstep. rewrite Hsend. rewrite <- Hlay. rewrite Hrecv. lia.
  - (* rstep x <= rstep y -> rhb_sub x y *)
    intro Hs.
    destruct (rhb_comparable_of_comp S Hwf x y Hlay Hcomp) as [Hxy | Hyx].
    + exact Hxy.
    + (* from rhb_sub y x: either y = x (refl) or redge (fst y)(fst x) forcing
         rstep y = 0, rstep x = 1, contradicting rstep x <= rstep y *)
      unfold rhb_sub, rhb in Hyx.
      assert (Hlayyx : rlay S y = rlay S x) by (symmetry; exact Hlay).
      unfold rlay in Hlayyx.
      destruct Hyx as [Hlt | [_ Hsame]].
      * lia.
      * destruct Hsame as [Heq | [Hidx Hed]].
        -- apply revent_eq_of_proj in Heq. rewrite Heq. apply poset_refl.
        -- exfalso.
           destruct Hed as [[ts Hsend] [tr Hrecv]].
           unfold rstep in Hs.
           (* Hsend : rop (fst y)(snd y) = Send (fst x) ts -> rstep y = 0
              Hrecv : rop (fst x)(snd y) = Recv (fst y) tr; snd y = snd x -> rstep x = 1 *)
           rewrite Hsend in Hs. rewrite Hlayyx in Hrecv. rewrite Hrecv in Hs. lia.
Qed.

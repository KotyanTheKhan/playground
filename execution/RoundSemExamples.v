(* Barrier-round model: worked instance (test-only). *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses.
From Execution Require Import Op OnlineClock OnlineClockLocal RoundSem.
Import ListNotations.

(* 3 processes, 1 round: proc0 -> proc1 (msg), proc2 idle *)
Definition Sdemo : RSys :=
  {| rs_nprocs := 3 ; rs_nrounds := 1 ;
     rs_prog := fun p => match p with
                         | 0 => [Send 1 0]
                         | 1 => [Recv 0 0]
                         | _ => [Local]
                         end |}.

Lemma wf_Sdemo : rwf Sdemo.
Proof.
  unfold rwf, Sdemo, rop. simpl. split; [| split].
  - intros pa Hpa. destruct pa as [|[|[|p']]]; simpl; lia.
  - intros pb rb db tb Hpb Hrb Hsend.
    destruct pb as [|[|[|p']]]; destruct rb as [|r']; simpl in *; try discriminate;
      try lia; injection Hsend as Hd Ht; subst db tb; split; [lia | reflexivity].
  - intros pc rc sc tc Hpc Hrc Hrecv.
    destruct pc as [|[|[|p']]]; destruct rc as [|r']; simpl in *; try discriminate;
      try lia; injection Hrecv as Hs Ht; subst sc tc; split; [lia | reflexivity].
Qed.

Lemma sdemo_pos : 0 < rs_nprocs Sdemo. Proof. vm_compute; lia. Qed.

Lemma v0 : rvalid Sdemo (0,0). Proof. unfold rvalid, Sdemo; simpl; lia. Qed.
Lemma v1 : rvalid Sdemo (1,0). Proof. unfold rvalid, Sdemo; simpl; lia. Qed.
Lemma v2 : rvalid Sdemo (2,0). Proof. unfold rvalid, Sdemo; simpl; lia. Qed.
Definition x0 : REvent Sdemo := exist _ (0,0) v0.
Definition x1 : REvent Sdemo := exist _ (1,0) v1.
Definition x2 : REvent Sdemo := exist _ (2,0) v2.

Example rclock_x0 : rclock Sdemo 0 0 = ((0,0,0),(0,2,0)). Proof. vm_compute. reflexivity. Qed.
Example rclock_x1 : rclock Sdemo 1 0 = ((0,0,1),(0,2,1)). Proof. vm_compute. reflexivity. Qed.
Example rclock_x2 : rclock Sdemo 2 0 = ((0,2,0),(0,0,0)). Proof. vm_compute. reflexivity. Qed.

Example rhb_x0_x1 : rhb_sub Sdemo x0 x1.
Proof.
  unfold rhb_sub, rhb, x0, x1. simpl. right. split; [reflexivity|].
  unfold rhb_same. right. split; [reflexivity|].
  unfold redge, rop, Sdemo. simpl. split; [exists 0; reflexivity | exists 0; reflexivity].
Qed.

Example rhb_x0_x2_incomp :
  ~ rhb_sub Sdemo x0 x2 /\ ~ rhb_sub Sdemo x2 x0.
Proof.
  split; intro H;
  [ apply (proj1 (rhb_iff_rclock Sdemo wf_Sdemo sdemo_pos x0 x2)) in H
  | apply (proj1 (rhb_iff_rclock Sdemo wf_Sdemo sdemo_pos x2 x0)) in H ];
  unfold stamp_le in H; vm_compute in H; unfold le_lex3 in H; lia.
Qed.

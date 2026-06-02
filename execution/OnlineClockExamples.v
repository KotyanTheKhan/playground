(* Online dim-2 clock: worked instances (test-only). *)
From Stdlib Require Import List Arith Lia Ensembles Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim
                             BarrierExecDimExamples OnlineClock.
Import ListNotations.

(* ================================================================= *)
(* Part A — the N=5 barrier s_bar5                                    *)
(* ================================================================= *)

Lemma bar5_blo_iff_stamp :
  forall x y,
    blo s_bar5 x y <->
    le_prod (sch_nprocs s_bar5 - 1)
      (clk_lay s_bar5 x)(clk_comp s_bar5 x)(clk_step s_bar5 x)
      (clk_lay s_bar5 y)(clk_comp s_bar5 y)(clk_step s_bar5 y).
Proof. apply (blo_iff_stamp s_bar5 wf_s_bar5). simpl. lia. Qed.

(* the two distinct layer-0 events get product-incomparable stamps *)
Example bar5_stamp_incomp :
  ~ (le_prod (sch_nprocs s_bar5 - 1)
       (clk_lay s_bar5 bar5_e0)(clk_comp s_bar5 bar5_e0)(clk_step s_bar5 bar5_e0)
       (clk_lay s_bar5 bar5_e1)(clk_comp s_bar5 bar5_e1)(clk_step s_bar5 bar5_e1))
  /\ ~ (le_prod (sch_nprocs s_bar5 - 1)
       (clk_lay s_bar5 bar5_e1)(clk_comp s_bar5 bar5_e1)(clk_step s_bar5 bar5_e1)
       (clk_lay s_bar5 bar5_e0)(clk_comp s_bar5 bar5_e0)(clk_step s_bar5 bar5_e0)).
Proof.
  pose proof bar5_incomp as Hinc. unfold Incomparable in Hinc.
  split; intro H.
  - apply (proj2 (bar5_blo_iff_stamp bar5_e0 bar5_e1)) in H. tauto.
  - apply (proj2 (bar5_blo_iff_stamp bar5_e1 bar5_e0)) in H. tauto.
Qed.

(* ================================================================= *)
(* Part B — a messaged 3-process barrier, with literal stamps         *)
(* ================================================================= *)

Definition s_msg3 : Schedule := {| sch_nprocs := 3; sch_frontiers := [ [(0,1)] ] |}.

Lemma wf_s_msg3 : wf_schedule s_msg3.
Proof.
  unfold wf_schedule, s_msg3. simpl. intros fr [<- | []].
  unfold wf_frontier, endpoints. split.
  - intros a b [E | []]; injection E as <- <-; lia.
  - simpl. repeat constructor; simpl; intuition discriminate.
Qed.

Lemma v00 : Ensembles.In _ (ValidSet (desugar s_msg3)) (0,0). Proof. vm_compute. split; lia. Qed.
Lemma v10 : Ensembles.In _ (ValidSet (desugar s_msg3)) (1,0). Proof. vm_compute. split; lia. Qed.
Lemma v20 : Ensembles.In _ (ValidSet (desugar s_msg3)) (2,0). Proof. vm_compute. split; lia. Qed.
Definition e00 : ep_carrier (exec_of_schedule s_msg3) := exist _ (0,0) v00.
Definition e10 : ep_carrier (exec_of_schedule s_msg3) := exist _ (1,0) v10.
Definition e20 : ep_carrier (exec_of_schedule s_msg3) := exist _ (2,0) v20.

(* literal computed stamps: sender(0)->receiver(1) share component 0; isolated(2) sits apart *)
Example stamp_e00 : stamp s_msg3 e00 = ((0,0,0),(0,2,0)). Proof. vm_compute. reflexivity. Qed.
Example stamp_e10 : stamp s_msg3 e10 = ((0,0,1),(0,2,1)). Proof. vm_compute. reflexivity. Qed.
Example stamp_e20 : stamp s_msg3 e20 = ((0,2,0),(0,0,0)). Proof. vm_compute. reflexivity. Qed.

(* ordering checks that don't depend on the events *)
Example msg3_sender_below_receiver : le_prod 2 0 0 0 0 0 1.
Proof. unfold le_prod, le_lex3. lia. Qed.
Example msg3_isolated_incomp : ~ le_prod 2 0 0 0 0 2 0 /\ ~ le_prod 2 0 2 0 0 0 0.
Proof. unfold le_prod, le_lex3. lia. Qed.

(* ================================================================= *)
(* Part C — abstract length-3 chain (generic stamp_iff, step in 0/1/2)*)
(* ================================================================= *)

Inductive P4 := u | v | w | z.
Definition R4 (a b : P4) : Prop :=
  match a, b with
  | u,u|v,v|w,w|z,z => True
  | u,v|u,w|v,w => True
  | _,_ => False
  end.
Definition lay4 (_ : P4) := 0.
Definition comp4 (a : P4) := match a with z => 1 | _ => 0 end.
Definition step4 (a : P4) := match a with u => 0 | v => 1 | w => 2 | z => 0 end.

#[local] Instance R4_IsPoset : IsPoset P4 R4.
Proof. constructor; [intros [] | intros [] [] | intros [] [] []]; cbv; tauto. Qed.

Example chain3_stamp_iff :
  forall a b, R4 a b <-> le_prod 1 (lay4 a)(comp4 a)(step4 a)(lay4 b)(comp4 b)(step4 b).
Proof.
  apply (stamp_iff R4 lay4 comp4 step4 1).
  - intros [] []; cbv; lia.
  - intros [] []; cbv; lia.
  - intros [] []; cbv; intuition.
  - intros [] []; cbv; intuition lia.
  - intros []; cbv; lia.
Qed.

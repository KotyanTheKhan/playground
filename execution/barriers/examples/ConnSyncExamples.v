(* s_demo is FullySynchronizing via connectivity (test-only). *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape ConnSync.
Import ListNotations.

Definition s_demo : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [(1,0)] ] |}.

Lemma wf_s_demo : wf_schedule s_demo.
Proof.
  unfold wf_schedule, s_demo. simpl. intros fr Hin.
  destruct Hin as [<- | [<- | []]]; apply wf_frontier_pair; lia.
Qed.

Lemma step_connected_s_demo : StepConnected s_demo.
Proof.
  unfold StepConnected, s_demo. simpl. intros k HSk p q Hp Hq.
  assert (Hk0 : k = 0) by lia. subst k.
  assert (Hpv : p = 0 \/ p = 1) by lia. assert (Hqv : q = 0 \/ q = 1) by lia.
  unfold step_witness. simpl.
  destruct Hpv as [Hp0|Hp1]; destruct Hqv as [Hq0|Hq1];
    subst.
  - left. reflexivity.
  - right. left. left. reflexivity.
  - right. right. left. left. reflexivity.
  - left. reflexivity.
Qed.

Example s_demo_fully_synchronizing_via_conn : FullySynchronizing s_demo.
Proof.
  apply (step_connected_fully_synchronizing s_demo wf_s_demo).
  - vm_compute. lia.
  - exact step_connected_s_demo.
Qed.

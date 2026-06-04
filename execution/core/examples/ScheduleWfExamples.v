(* Concrete well-formed schedule witnesses (test-only). *)
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Schedule ScheduleWf Examples SyncShapeExamples.
Import ListNotations.

(* a single-pair frontier with a<n, b<n, a<>b is well-formed *)
Lemma wf_frontier_one : forall n a b, a < n -> b < n -> a <> b ->
  wf_frontier n [(a, b)].
Proof.
  intros n a b Ha Hb Hab. unfold wf_frontier, endpoints. split.
  - intros x y Hin. simpl in Hin. destruct Hin as [Heq | []].
    injection Heq as <- <-. repeat split; assumption.
  - simpl. constructor.
    + simpl. intros [H | []]. apply Hab. symmetry. exact H.
    + constructor. simpl. intros []. constructor.
Qed.

Example wf_sched_n3 : wf_schedule sched_n3.
Proof.
  unfold wf_schedule, sched_n3. simpl.
  intros fr Hin.
  destruct Hin as [<- | [<- | []]].
  - apply wf_frontier_one; lia.
  - apply wf_frontier_one; lia.
Qed.

Example wf_s_demo : wf_schedule s_demo.
Proof.
  unfold wf_schedule, s_demo. simpl.
  intros fr Hin.
  destruct Hin as [<- | [<- | []]].
  - apply wf_frontier_one; lia.
  - apply wf_frontier_one; lia.
Qed.

Example wf_program_desugar_n3 : wf_program (desugar_prog sched_n3).
Proof. apply desugar_wf. exact wf_sched_n3. Qed.

Example wf_sched_m45 : wf_schedule sched_m45.
Proof.
  unfold wf_schedule, sched_m45. simpl.
  intros fr Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
    apply wf_frontier_one; lia.
Qed.

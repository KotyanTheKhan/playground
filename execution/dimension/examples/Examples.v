(* Examples — N=3 and mΨ(4,5) compile-checked example executions.
   Demonstrates the schedule and edge-set representations agree, and that
   the happened-before order behaves sensibly (ordering vs concurrency). *)

From Stdlib Require Import List Arith Lia Relation_Operators Ensembles.
From Execution Require Import Op Event Edges Rank Poset Schedule FromEdges.
Import ListNotations.

(* ================================================================== *)
(* Part 1 — N=3 example, both representations agree                    *)
(* ================================================================== *)

Definition sched_n3 : Schedule :=
  {| sch_nprocs := 3;
     sch_frontiers := [ [(0,1)] ; [(1,2)] ] |}.

(* Same execution described as an explicit edge set (derived by the formula:
   frontier 0 has pair (0,1) -> tuple (0,0,1,0,0);
   frontier 1 has pair (1,2) -> tuple (1,1,2,1,1)). *)
Definition edges_n3 : EdgeSpec :=
  {| es_nprocs := 3;
     es_lens   := [2; 2; 2];
     es_msgs   := [ (0,0,1,0,0) ; (1,1,2,1,1) ] |}.

(* The two descriptions denote the SAME program. *)
Example n3_same_program :
  desugar_prog sched_n3 = prog_of_edgespec edges_n3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Part 2 — sanity ordering / concurrency facts on N=3                 *)
(* ================================================================== *)

(* a valid event of the desugared N=3 program *)
Definition ev_n3 (p i : nat)
  (H : Ensembles.In (nat*nat) (ValidSet (desugar_prog sched_n3)) (p, i))
  : Event (desugar_prog sched_n3) := exist _ (p, i) H.

(* (0,0) -> (0,1) are program-order consecutive in process 0, hence ordered. *)
Example n3_ordered :
  exists a b : Event (desugar sched_n3), hb (desugar sched_n3) a b.
Proof.
  exists (ev_n3 0 0 ltac:(vm_compute; split; lia)).
  exists (ev_n3 0 1 ltac:(vm_compute; split; lia)).
  apply rt_step. unfold edge. simpl. left. split; reflexivity.
Qed.

(* (0,0) and (2,0): distinct events with equal rank (both 0), hence concurrent. *)
Example n3_concurrent :
  exists a b : Event (desugar sched_n3),
    ~ hb (desugar sched_n3) a b /\ ~ hb (desugar sched_n3) b a.
Proof.
  exists (ev_n3 0 0 ltac:(vm_compute; split; lia)).
  exists (ev_n3 2 0 ltac:(vm_compute; split; lia)).
  split.
  - intro Hhb.
    destruct (hb_eq_or_rank_lt _ _ _ Hhb) as [Heq | Hlt].
    + apply (f_equal (@proj1_sig _ _)) in Heq; cbn in Heq; discriminate.
    + vm_compute in Hlt. lia.
  - intro Hhb.
    destruct (hb_eq_or_rank_lt _ _ _ Hhb) as [Heq | Hlt].
    + apply (f_equal (@proj1_sig _ _)) in Heq; cbn in Heq; discriminate.
    + vm_compute in Hlt. lia.
Qed.

(* ================================================================== *)
(* Part 3 — one 4-process / 5-frontier example (mΨ(4,5)-style)         *)
(* ================================================================== *)

Definition sched_m45 : Schedule :=
  {| sch_nprocs := 4;
     sch_frontiers := [ [(0,1)] ; [(2,3)] ; [(1,2)] ; [(0,3)] ; [(1,3)] ] |}.

Definition edges_m45 : EdgeSpec :=
  {| es_nprocs := 4;
     es_lens   := [5; 5; 5; 5];
     es_msgs   := [ (0,0,1,0,0) ; (2,1,3,1,1) ; (1,2,2,2,2) ; (0,3,3,3,3) ; (1,4,3,4,4) ] |}.

Example m45_same_program :
  desugar_prog sched_m45 = prog_of_edgespec edges_m45.
Proof. vm_compute. reflexivity. Qed.

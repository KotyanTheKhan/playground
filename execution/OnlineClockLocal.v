(* Online clock maintenance: the locality theorem. local_stamp is schedule-blind
   (s is not an argument) -- the signature IS the locality of the clock. We prove
   it reproduces the global stamp for every valid event. *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim OnlineClock.
Import ListNotations.

(* The clock computed from purely local data: N = system size, p = own pid,
   i = own local index, o = own op (a Recv carries the sender id). *)
Definition local_stamp (N p i : nat) (o : Op) : (nat * nat * nat) * (nat * nat * nat) :=
  let comp := match o with Recv src _ => src | _ => p end in
  let step := match o with Recv _ _ => 1 | _ => 0 end in
  ((i, comp, step), (i, (N - 1) - comp, step)).

(* What process p observes at its index-i event: its own op. *)
Definition local_obs (s : Schedule) (p i : nat) : Op :=
  op_for (nth i (sch_frontiers s) []) p i.

(* The schedule-blind local clock reproduces the global stamp at every valid event. *)
Theorem local_stamp_correct :
  forall s (x : ep_carrier (exec_of_schedule s)),
    local_stamp (sch_nprocs s) (fst (proj1_sig x)) (snd (proj1_sig x))
                (local_obs s (fst (proj1_sig x)) (snd (proj1_sig x)))
    = stamp s x.
Proof.
  intros s x.
  unfold stamp, local_stamp, clk_lay, clk_comp, clk_step, fb_comp, local_obs.
  rewrite (block_op_for s x).
  destruct (op_for (nth (snd (proj1_sig x)) (sch_frontiers s) [])
                   (fst (proj1_sig x)) (snd (proj1_sig x)));
    reflexivity.
Qed.

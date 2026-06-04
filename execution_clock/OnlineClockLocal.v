(* Online clock maintenance: the locality theorem. local_stamp is schedule-blind
   (s is not an argument) -- the signature IS the locality of the clock. We prove
   it reproduces the global stamp for every valid event. *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim.
From ExecClock Require Import OnlineClock.
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

(* product of the two lex orders, on (triple, triple) stamp pairs *)
Definition stamp_le (st1 st2 : (nat * nat * nat) * (nat * nat * nat)) : Prop :=
  let '((a1,a2,a3),(b1,b2,b3)) := st1 in
  let '((c1,c2,c3),(d1,d2,d3)) := st2 in
  le_lex3 a1 a2 a3 c1 c2 c3 /\ le_lex3 b1 b2 b3 d1 d2 d3.

(* stamp_le on the offline stamp wrapper is exactly le_prod on the clk fields *)
Lemma stamp_le_stamp :
  forall s (x y : ep_carrier (exec_of_schedule s)),
    stamp_le (stamp s x) (stamp s y) <->
    le_prod (sch_nprocs s - 1)
      (clk_lay s x)(clk_comp s x)(clk_step s x)
      (clk_lay s y)(clk_comp s y)(clk_step s y).
Proof.
  intros s x y. unfold stamp_le, stamp, le_prod. cbn. tauto.
Qed.

(* The headline online clock: blo characterized purely via the schedule-blind local_stamp. *)
Corollary blo_iff_local_stamp :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
  forall x y : ep_carrier (exec_of_schedule s),
    blo s x y <->
    stamp_le
      (local_stamp (sch_nprocs s) (fst (proj1_sig x)) (snd (proj1_sig x))
                   (local_obs s (fst (proj1_sig x)) (snd (proj1_sig x))))
      (local_stamp (sch_nprocs s) (fst (proj1_sig y)) (snd (proj1_sig y))
                   (local_obs s (fst (proj1_sig y)) (snd (proj1_sig y)))).
Proof.
  intros s Hwf Hnp x y.
  rewrite (local_stamp_correct s x). rewrite (local_stamp_correct s y).
  rewrite stamp_le_stamp.
  exact (blo_iff_stamp s Hwf Hnp x y).
Qed.

(* A Send/Local event contributes no cross-process clock datum (comp = own pid). *)
Lemma local_stamp_send_eq_local :
  forall N p i t tg, local_stamp N p i (Send t tg) = local_stamp N p i Local.
Proof. reflexivity. Qed.

(* A Recv uses only its sender id, never the tag: the only cross-process datum is src. *)
Lemma local_stamp_recv_tag_irrel :
  forall N p i src tg tg', local_stamp N p i (Recv src tg) = local_stamp N p i (Recv src tg').
Proof. reflexivity. Qed.

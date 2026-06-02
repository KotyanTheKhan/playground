(* N=5 barrier execution has dim <= 2 (beyond the pairwise model's <=4 reach) (test-only).

   s_bar5 has 5 processes and 2 barrier layers (both frontiers empty => each layer is a
   5-event ANTICHAIN of width 5).  The barrier order `blo` orders ALL of layer 0 before
   ALL of layer 1 -- a genuine 5-way barrier, which the pairwise-message `hb` could NOT
   realize for the `FullySynchronizing` notion (a single transition reaches <= 4 processes,
   review finding 1).  `bar5_dim_le2` shows `dim (blo s_bar5) <= 2` regardless. *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                              Ordinal DisjointChainsDim BarrierExecDim.
Import ListNotations.

Definition s_bar5 : Schedule :=
  {| sch_nprocs := 5; sch_frontiers := [ [] ; [] ] |}.

Lemma wf_s_bar5 : wf_schedule s_bar5.
Proof.
  unfold wf_schedule, s_bar5. simpl. intros fr Hin.
  (* both frontiers are [] : wf_frontier n [] = (no pairs in range) /\ NoDup [] *)
  destruct Hin as [<- | [<- | []]];
    (unfold wf_frontier, endpoints; split;
     [ intros a b Hb; destruct Hb | simpl; constructor ]).
Qed.

(* the N=5 barrier execution has dimension <= 2 -- exactly the regime finding 1 excluded *)
Example bar5_dim_le2 :
  forall d, PosetDimension (blo s_bar5) d -> d <= 2.
Proof. apply (barrier_execution_dim_le2 s_bar5 wf_s_bar5). Qed.

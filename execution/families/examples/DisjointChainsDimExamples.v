(* frontier block of width > 2 still has dim <= 2 (test-only).

   The index-0 block of s_anti3 is a 3-event ANTICHAIN (3 processes, an empty
   frontier => all Local, no messages), so its width is 3.  `two_chain_cover_dim_le2`
   (Transformation B, width <= 2) does NOT apply here; `frontier_block_dim_le2`
   (disjoint union of chains => dim <= 2) does. *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                              Ordinal DisjointChainsDim.
Import ListNotations.

Definition s_anti3 : Schedule :=
  {| sch_nprocs := 3; sch_frontiers := [ [] ] |}.

Lemma wf_s_anti3 : wf_schedule s_anti3.
Proof.
  unfold wf_schedule, s_anti3. simpl. intros fr Hin.
  destruct Hin as [<- | []].
  unfold wf_frontier, endpoints. split.
  - intros a b Hb. destruct Hb.
  - simpl. constructor.
Qed.

(* the width-3 index-0 block has dim <= 2 (where the width<=2 route could not apply) *)
Example anti3_block_dim_le2 :
  forall d,
    PosetDimension (sub_order (exec_of_schedule s_anti3) (frontier_block s_anti3 0)) d ->
    d <= 2.
Proof. apply (frontier_block_dim_le2 s_anti3 wf_s_anti3 0). Qed.

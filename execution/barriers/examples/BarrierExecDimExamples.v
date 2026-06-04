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
                              Ordinal DisjointChainsDim BarrierExecDim ConnSync DimTwoGeneric.
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

(* two distinct layer-0 events of s_bar5 are blo-incomparable: same index, empty
   frontier => no message between them, and different index is excluded *)
Lemma bar5_e0_valid : 0 < sch_nprocs s_bar5. Proof. simpl; lia. Qed.
Lemma bar5_e1_valid : 1 < sch_nprocs s_bar5. Proof. simpl; lia. Qed.
Lemma bar5_k_valid  : 0 < length (sch_frontiers s_bar5). Proof. simpl; lia. Qed.

Definition bar5_e0 := mk_event s_bar5 0 0 bar5_e0_valid bar5_k_valid.
Definition bar5_e1 := mk_event s_bar5 1 0 bar5_e1_valid bar5_k_valid.

Lemma bar5_incomp : Incomparable (blo s_bar5) bar5_e0 bar5_e1.
Proof.
  unfold Incomparable. intro Hb.
  assert (Hneq : bar5_e0 <> bar5_e1).
  { intro He. assert (proj1_sig bar5_e0 = proj1_sig bar5_e1) by (rewrite He; reflexivity).
    unfold bar5_e0, bar5_e1 in *. rewrite !mk_event_proj in *. discriminate. }
  destruct Hb as [Hb | Hb]; unfold blo in Hb; unfold bar5_e0, bar5_e1 in Hb;
    rewrite !mk_event_proj in Hb; simpl in Hb;
    destruct Hb as [Hlt | [_ Hhb]]; try lia.
  - (* ep_order bar5_e0 bar5_e1 : same index 0, distinct => In (0,1) (nth 0 [[];[]] []) = In (0,1) [] *)
    pose proof (hb_same_index_msg s_bar5 wf_s_bar5 bar5_e0 bar5_e1) as Hmsg.
    unfold bar5_e0, bar5_e1 in Hmsg. rewrite !mk_event_proj in Hmsg. simpl in Hmsg.
    specialize (Hmsg eq_refl Hhb Hneq). exact Hmsg.
  - (* ep_order bar5_e1 bar5_e0 : symmetric, In (1,0) [] *)
    pose proof (hb_same_index_msg s_bar5 wf_s_bar5 bar5_e1 bar5_e0) as Hmsg.
    unfold bar5_e0, bar5_e1 in Hmsg. rewrite !mk_event_proj in Hmsg. simpl in Hmsg.
    assert (Hneq' : bar5_e1 <> bar5_e0) by (intro; apply Hneq; symmetry; assumption).
    specialize (Hmsg eq_refl Hhb Hneq'). exact Hmsg.
Qed.

Example bar5_dim_eq_2 : forall d, PosetDimension (blo s_bar5) d -> d = 2.
Proof. apply (blo_dim_eq_2 s_bar5 wf_s_bar5). exists bar5_e0, bar5_e1. exact bar5_incomp. Qed.

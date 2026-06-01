(* window-barrier example: a gather/scatter window synchronizes all processes (test-only). *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape ConnSync WindowSync.
Import ListNotations.

(* Frontier 0 is a leading no-op so that events at index 0 are strictly before the
   gather/scatter window [1,5); the gather (procs 1,2 -> coordinator 0) occupies
   frontiers 1,2 and the scatter (0 -> 1,2) occupies frontiers 3,4; frontier 5 is a
   trailing no-op so that index-5 events exist strictly after the window (making the
   barrier statement non-vacuous). *)
Definition s_gs : Schedule :=
  {| sch_nprocs := 3;
     sch_frontiers := [ [(0,1)] ; [(1,0)] ; [(2,0)] ; [(0,1)] ; [(0,2)] ; [(0,1)] ] |}.

Lemma wf_frontier_pair : forall n a b, a < n -> b < n -> a <> b -> wf_frontier n [(a,b)].
Proof.
  intros n a b Ha Hb Hab. unfold wf_frontier, endpoints. split.
  - intros x y [Heq|[]]. injection Heq as <- <-. repeat split; assumption.
  - simpl. constructor.
    + simpl. intros [H|[]]. apply Hab. symmetry. exact H.
    + constructor; [ simpl; intros [] | constructor ].
Qed.

Lemma wf_s_gs : wf_schedule s_gs.
Proof.
  unfold wf_schedule, s_gs. simpl. intros fr Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; apply wf_frontier_pair; lia.
Qed.

Lemma window_connected_s_gs : WindowConnected s_gs 1 5.
Proof.
  unfold WindowConnected, s_gs. simpl. intros p q Hp Hq.
  assert (Hp3 : p = 0 \/ p = 1 \/ p = 2) by lia.
  assert (Hq3 : q = 0 \/ q = 1 \/ q = 2) by lia.
  destruct Hp3 as [E0|[E0|E0]]; rewrite E0; clear E0;
    (destruct Hq3 as [F0|[F0|F0]]; rewrite F0; clear F0).
  (* (0,0): 0->0->0->0->0, all stay *)
  - exists 0; split; [ exists 0; split; [ exists 0; split;
      [ exists 0; split; [ reflexivity | left; reflexivity ]
      | left; reflexivity ] | left; reflexivity ] | left; reflexivity ].
  (* (0,1): r0=r1=r2=0, r3=1, q=1; cross (0,1)@lvl2, stay@lvl3 *)
  - exists 1; split; [ exists 0; split; [ exists 0; split;
      [ exists 0; split; [ reflexivity | left; reflexivity ]
      | left; reflexivity ] | right; left; reflexivity ] | left; reflexivity ].
  (* (0,2): r0=r1=r2=r3=0, q=2; cross (0,2)@lvl3 *)
  - exists 0; split; [ exists 0; split; [ exists 0; split;
      [ exists 0; split; [ reflexivity | left; reflexivity ]
      | left; reflexivity ] | left; reflexivity ] | right; left; reflexivity ].
  (* (1,0): r0=1,r1=0,r2=0,r3=0,q=0; cross (1,0)@lvl0 *)
  - exists 0; split; [ exists 0; split; [ exists 0; split;
      [ exists 1; split; [ reflexivity | right; left; reflexivity ]
      | left; reflexivity ] | left; reflexivity ] | left; reflexivity ].
  (* (1,1): r0=1,r1=0,r2=0,r3=1,q=1; cross (1,0)@lvl0, cross (0,1)@lvl2 *)
  - exists 1; split; [ exists 0; split; [ exists 0; split;
      [ exists 1; split; [ reflexivity | right; left; reflexivity ]
      | left; reflexivity ] | right; left; reflexivity ] | left; reflexivity ].
  (* (1,2): r0=1,r1=0,r2=0,r3=0,q=2; cross (1,0)@lvl0, cross (0,2)@lvl3 *)
  - exists 0; split; [ exists 0; split; [ exists 0; split;
      [ exists 1; split; [ reflexivity | right; left; reflexivity ]
      | left; reflexivity ] | left; reflexivity ] | right; left; reflexivity ].
  (* (2,0): r0=2,r1=2,r2=0,r3=0,q=0; stay@lvl0, cross (2,0)@lvl1 *)
  - exists 0; split; [ exists 0; split; [ exists 2; split;
      [ exists 2; split; [ reflexivity | left; reflexivity ]
      | right; left; reflexivity ] | left; reflexivity ] | left; reflexivity ].
  (* (2,1): r0=2,r1=2,r2=0,r3=1,q=1; cross (2,0)@lvl1, cross (0,1)@lvl2 *)
  - exists 1; split; [ exists 0; split; [ exists 2; split;
      [ exists 2; split; [ reflexivity | left; reflexivity ]
      | right; left; reflexivity ] | right; left; reflexivity ] | left; reflexivity ].
  (* (2,2): r0=2,r1=2,r2=0,r3=0,q=2; cross (2,0)@lvl1, cross (0,2)@lvl3 *)
  - exists 0; split; [ exists 0; split; [ exists 2; split;
      [ exists 2; split; [ reflexivity | left; reflexivity ]
      | right; left; reflexivity ] | left; reflexivity ] | right; left; reflexivity ].
Qed.

Example s_gs_window_barrier :
  forall x y : ep_carrier (exec_of_schedule s_gs),
    snd (proj1_sig x) < 1 -> 5 <= snd (proj1_sig y) ->
    ep_order (exec_of_schedule s_gs) x y.
Proof.
  apply (window_connected_barrier s_gs wf_s_gs).
  - vm_compute. lia.
  - lia.
  - vm_compute. lia.
  - exact window_connected_s_gs.
Qed.

(* Non-vacuous instance: process 1 at index 0 (before the window) precedes process 2
   at index 5 (after the window) — a genuine cross-process synchronization across the
   gather/scatter window that no single transition could establish (3 processes). *)
Example s_gs_cross_window_concrete :
  forall x y : ep_carrier (exec_of_schedule s_gs),
    proj1_sig x = (1, 0) -> proj1_sig y = (2, 5) ->
    ep_order (exec_of_schedule s_gs) x y.
Proof.
  intros x y Hx Hy. apply s_gs_window_barrier; rewrite ?Hx, ?Hy; simpl; lia.
Qed.

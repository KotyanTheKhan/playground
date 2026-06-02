(* A computable 2-coordinate timestamp whose product order equals blo. *)
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Compare_dec.
From Posets Require Import PosetClasses.

(* lexicographic <= on a nat triple, given as 6 scalars (no tuple destructuring) *)
Definition le_lex3 (a1 a2 a3 b1 b2 b3 : nat) : Prop :=
  a1 < b1 \/ (a1 = b1 /\ (a2 < b2 \/ (a2 = b2 /\ a3 <= b3))).

(* product of the two lex orders: T1 = (lay,comp,step); T2 = (lay, B-comp, step) *)
Definition le_prod (B lx cx sx ly cy sy : nat) : Prop :=
  le_lex3 lx cx sx ly cy sy /\ le_lex3 lx (B - cx) sx ly (B - cy) sy.

Theorem stamp_iff :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (lay comp step : A -> nat) (B : nat),
    (forall x y, lay x < lay y -> R x y) ->                                   (* 1 barrier   *)
    (forall x y, R x y -> lay x <= lay y) ->                                  (* 2 resp-lay  *)
    (forall x y, R x y -> lay x = lay y -> comp x = comp y) ->                (* 3 resp-comp *)
    (forall x y, lay x = lay y -> comp x = comp y ->
                 (R x y <-> step x <= step y)) ->                             (* 4 rank      *)
    (forall e, comp e <= B) ->                                               (* 5 bound     *)
    forall x y, R x y <-> le_prod B (lay x)(comp x)(step x)(lay y)(comp y)(step y).
Proof.
  intros A R HR lay comp step B Hbar Hlay Hcomp Hrank Hbound x y.
  unfold le_prod, le_lex3. split.
  - intro Hr. pose proof (Hlay x y Hr) as Hle.
    destruct (lt_eq_lt_dec (lay x) (lay y)) as [[Hlt | Heq] | Hgt].
    + split; left; exact Hlt.
    + pose proof (Hcomp x y Hr Heq) as Hce.
      pose proof (proj1 (Hrank x y Heq Hce) Hr) as Hsle.
      split.
      * right. split; [exact Heq|]. right. split; [exact Hce | exact Hsle].
      * right. split; [exact Heq|]. right. split; [rewrite Hce; reflexivity | exact Hsle].
    + exfalso. lia.
  - intros [H1 H2].
    destruct (lt_eq_lt_dec (lay x) (lay y)) as [[Hlt | Heq] | Hgt].
    + apply Hbar; exact Hlt.
    + pose proof (Hbound x) as Hbx. pose proof (Hbound y) as Hby.
      destruct H1 as [Hl1 | [_ Hc1]]; [lia|].
      destruct H2 as [Hl2 | [_ Hc2]]; [lia|].
      assert (Hce : comp x = comp y).
      { destruct Hc1 as [Hcl1 | [Hce1 _]]; destruct Hc2 as [Hcl2 | [Hce2 _]]; lia. }
      assert (Hsle : step x <= step y).
      { destruct Hc1 as [Hcl1 | [_ Hs]]; [lia | exact Hs]. }
      exact (proj2 (Hrank x y Heq Hce) Hsle).
    + exfalso. destruct H1 as [Hl1 | [He1 _]]; lia.
Qed.

From Stdlib Require Import List Classical.
From Posets Require Import FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf
                             SyncShape Ordinal DisjointChainsDim BarrierExecDim.
Import ListNotations.

Definition clk_lay  (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  snd (proj1_sig x).
Definition clk_comp (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  fb_comp s (proj1_sig x).
Definition clk_step (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  match op_at (desugar_prog s) (fst (proj1_sig x)) (snd (proj1_sig x)) with
  | Some (Recv _ _) => 1 | _ => 0 end.

(* fb_comp is always a valid pid, hence < sch_nprocs s *)
Lemma fb_comp_lt_nprocs :
  forall s, wf_schedule s -> forall x : ep_carrier (exec_of_schedule s),
    clk_comp s x < sch_nprocs s.
Proof.
  intros s Hwf x. unfold clk_comp, fb_comp.
  rewrite (block_op_for s x).            (* op_at = Some (op_for (nth k ..) px k) *)
  set (px := fst (proj1_sig x)). set (k := snd (proj1_sig x)).
  assert (Hpx : px < sch_nprocs s) by (unfold px; apply event_pid_lt).
  assert (Hk  : k < length (sch_frontiers s)) by (unfold k; apply event_index_lt).
  destruct (op_for (nth k (sch_frontiers s) []) px k) as [|q t|src t] eqn:Eop.
  - exact Hpx.                            (* Local : pid *)
  - exact Hpx.                            (* Send  : pid *)
  - (* Recv src t : src is an in-range frontier endpoint *)
    assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
      by (apply Hwf; apply nth_In; exact Hk).
    assert (Htk : t = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) px k src t)); exact Eop).
    subst t.
    assert (Hin : List.In (src, px) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ src px k Hfr); exact Eop).
    destruct Hfr as [Hrange _]. apply (Hrange src px) in Hin. tauto.
Qed.

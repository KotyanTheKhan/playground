(* A computable 2-coordinate timestamp whose product order equals blo. *)
(* SCOPE: this module proves the *characterization* (soundness) half -- a computable
   stamp whose product order equals blo. The "online" maintenance (each process
   updating its stamp from local state + message payloads) is future work, argued
   in prose in execution/DIM2_CLOCK.md, not proven here. *)
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Compare_dec.
From Posets Require Import PosetClasses.

(* lexicographic <= on a nat triple, given as 6 scalars (no tuple destructuring) *)
(* NOTE: le_lex3 takes 6 scalars (not two triples) -- the uncurried form is
   easier for lia; the design doc writes it tuple-style. *)
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

(* within one layer, blo reduces to the real hb order *)
Lemma blo_same_layer :
  forall s (x y : ep_carrier (exec_of_schedule s)),
    clk_lay s x = clk_lay s y ->
    (blo s x y <-> ep_order (exec_of_schedule s) x y).
Proof.
  intros s x y Hl. unfold clk_lay in Hl. unfold blo. split.
  - intros [Hlt | [_ Hhb]]; [lia | exact Hhb].
  - intro Hhb. right. split; [exact Hl | exact Hhb].
Qed.

(* within one layer, a real hb edge between distinct events runs sender(step 0) -> receiver(step 1) *)
Lemma hb_layer_step :
  forall s, wf_schedule s -> forall x y : ep_carrier (exec_of_schedule s),
    clk_lay s x = clk_lay s y ->
    ep_order (exec_of_schedule s) x y -> x <> y ->
    clk_step s x = 0 /\ clk_step s y = 1.
Proof.
  intros s Hwf x y Hl Hhb Hne. unfold clk_lay in Hl.
  pose proof (hb_same_index_msg s Hwf x y Hl Hhb Hne) as Hin.
  pose (px := fst (proj1_sig x)). pose (py := fst (proj1_sig y)).
  pose (k := snd (proj1_sig x)).
  assert (Hpx : px < sch_nprocs s) by (apply event_pid_lt).
  assert (Hpy : py < sch_nprocs s) by (apply event_pid_lt).
  assert (Hk  : k < length (sch_frontiers s)) by (apply event_index_lt).
  assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
    by (apply Hwf; apply nth_In; exact Hk).
  fold px py k in Hin.
  pose proof (proj2 (op_for_send_iff (sch_nprocs s) _ px py k Hfr) Hin) as Hsend.
  pose proof (proj2 (op_for_recv_iff (sch_nprocs s) _ px py k Hfr) Hin) as Hrecv.
  assert (Hky : snd (proj1_sig y) = k) by (symmetry; exact Hl).
  unfold clk_step.
  rewrite (block_op_for s x). fold px k. rewrite Hsend.
  split; [reflexivity|].
  rewrite (block_op_for s y). fold py. rewrite Hky. rewrite Hrecv. reflexivity.
Qed.

(* rank axiom (hyp 4 of stamp_iff) specialized to blo:
   within a fixed layer and component, the online step counter linearizes hb *)
Lemma blo_rank :
  forall s, wf_schedule s -> forall x y : ep_carrier (exec_of_schedule s),
    clk_lay s x = clk_lay s y -> clk_comp s x = clk_comp s y ->
    (blo s x y <-> clk_step s x <= clk_step s y).
Proof.
  intros s Hwf x y Hl Hc. split.
  - (* blo -> step <= step *)
    intro Hb. apply (blo_same_layer s x y Hl) in Hb.
    destruct (event_eq_dec (desugar s) x y) as [He | Hne].
    + subst y. lia.
    + destruct (hb_layer_step s Hwf x y Hl Hb Hne) as [Hsx Hsy]. rewrite Hsx, Hsy. lia.
  - (* step <= step -> blo *)
    (* backward: comparability comes from hb_or_of_fb_comp_eq, whose correctness
       rests on wf_frontier's NoDup (unique sender per frontier) -- that is what
       makes each (layer, comp) class a chain of length <= 2, so Recv?1:0 is a
       faithful rank here. *)
    intro Hs. apply (blo_same_layer s x y Hl).
    assert (Hidx : snd (proj1_sig x) = snd (proj1_sig y)) by exact Hl.
    assert (Hcc  : fb_comp s (proj1_sig x) = fb_comp s (proj1_sig y)) by exact Hc.
    destruct (hb_or_of_fb_comp_eq s Hwf x y Hidx Hcc) as [Hxy | Hyx].
    + exact Hxy.
    + destruct (event_eq_dec (desugar s) y x) as [He | Hne].
      * subst x. apply poset_refl.
      * destruct (hb_layer_step s Hwf y x (eq_sym Hl) Hyx Hne) as [Hsy Hsx].
        rewrite Hsx, Hsy in Hs. lia.
Qed.

Theorem blo_iff_stamp :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
  forall x y : ep_carrier (exec_of_schedule s),
    blo s x y <->
    le_prod (sch_nprocs s - 1)
      (clk_lay s x)(clk_comp s x)(clk_step s x)
      (clk_lay s y)(clk_comp s y)(clk_step s y).
Proof.
  intros s Hwf Hnp x y.
  apply (stamp_iff (blo s) (clk_lay s) (clk_comp s) (clk_step s) (sch_nprocs s - 1)).
  - (* 1 barrier *) intros a b Hlt. left. exact Hlt.
  - (* 2 resp-lay *) intros a b [Hlt | [He _]]; unfold clk_lay; lia.
  - (* 3 resp-comp *) intros a b Hb Hl.
    apply (blo_same_layer s a b Hl) in Hb.
    exact (fb_comp_eq_of_hb s Hwf a b Hl Hb).
  - (* 4 rank *) intros a b Hl Hc. exact (blo_rank s Hwf a b Hl Hc).
  - (* 5 bound *) intro e. pose proof (fb_comp_lt_nprocs s Hwf e). lia.
Qed.

(* Readable timestamp: a pair of nat triples, for vm_compute in examples. *)
Definition stamp (s : Schedule) (x : ep_carrier (exec_of_schedule s))
  : (nat * nat * nat) * (nat * nat * nat) :=
  let l := clk_lay s x in let c := clk_comp s x in let st := clk_step s x in
  ((l, c, st), (l, (sch_nprocs s - 1) - c, st)).

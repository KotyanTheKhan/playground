(* A disjoint union of chains has dimension <= 2; hence every frontier block of a
   well-formed schedule has dim <= 2 (closes critical-review finding 2). *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                           ProofIrrelevance Relation_Operators Operators_Properties.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape
                              ConnSync.
From Execution Require Export DisjointChainsDimAux.
Import ListNotations.
#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* ------------------------------------------------------------------ *)
(* H1/H2 of frontier_block_dim_le2, factored to the bare ep_order      *)
(* level (no block subtype).                                           *)
(* ------------------------------------------------------------------ *)

(* H1: within one frontier, an hb edge between two events forces them to
   share the same fb_comp (sender of the message). *)
Lemma fb_comp_eq_of_hb :
  forall s, wf_schedule s -> forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) = snd (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y ->
    fb_comp s (proj1_sig x) = fb_comp s (proj1_sig y).
Proof.
  intros s Hwf x y Hidx Hhb.
  destruct (event_eq_dec (desugar s) x y) as [Heq | Hne].
  - rewrite Heq. reflexivity.
  - pose proof (hb_same_index_msg s Hwf x y Hidx Hhb Hne) as Hin.
    set (k := snd (proj1_sig x)) in *.
    set (px := fst (proj1_sig x)) in *.
    set (py := fst (proj1_sig y)) in *.
    assert (Hpx : px < sch_nprocs s) by (unfold px; apply event_pid_lt).
    assert (Hpy : py < sch_nprocs s) by (unfold py; apply event_pid_lt).
    assert (Hk : k < length (sch_frontiers s)) by (unfold k; apply event_index_lt).
    assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
      by (apply Hwf; apply nth_In; exact Hk).
    pose proof (proj2 (op_for_send_iff (sch_nprocs s) _ px py k Hfr) Hin) as Hsend.
    pose proof (proj2 (op_for_recv_iff (sch_nprocs s) _ px py k Hfr) Hin) as Hrecv.
    assert (Hky : snd (proj1_sig y) = k) by (unfold k; symmetry; exact Hidx).
    assert (Hpairx : proj1_sig x = (px, k)).
    { unfold px, k. rewrite (surjective_pairing (proj1_sig x)). reflexivity. }
    assert (Hpairy : proj1_sig y = (py, k)).
    { unfold py. rewrite (surjective_pairing (proj1_sig y)). rewrite Hky. reflexivity. }
    assert (Hcx : fb_comp s (proj1_sig x) = px).
    { rewrite Hpairx. exact (fb_comp_send s px py k Hpx Hk Hsend). }
    assert (Hcy : fb_comp s (proj1_sig y) = px).
    { rewrite Hpairy. exact (fb_comp_recv s px py k Hpy Hk Hrecv). }
    rewrite Hcx, Hcy. reflexivity.
Qed.

(* H2: within one frontier, two events with the same fb_comp are hb-comparable. *)
Lemma hb_or_of_fb_comp_eq :
  forall s, wf_schedule s -> forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) = snd (proj1_sig y) ->
    fb_comp s (proj1_sig x) = fb_comp s (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y \/ ep_order (exec_of_schedule s) y x.
Proof.
  intros s Hwf x y Hidx Hcomp.
  set (k := snd (proj1_sig x)) in *.
  set (px := fst (proj1_sig x)) in *.
  set (py := fst (proj1_sig y)) in *.
  assert (Hpx : px < sch_nprocs s) by (unfold px; apply event_pid_lt).
  assert (Hpy : py < sch_nprocs s) by (unfold py; apply event_pid_lt).
  assert (Hk : k < length (sch_frontiers s)) by (unfold k; apply event_index_lt).
  assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
    by (apply Hwf; apply nth_In; exact Hk).
  assert (Hkx : snd (proj1_sig x) = k) by reflexivity.
  assert (Hky : snd (proj1_sig y) = k) by (symmetry; exact Hidx).
  assert (Hpairx : proj1_sig x = (px, k)).
  { unfold px, k. rewrite (surjective_pairing (proj1_sig x)). reflexivity. }
  assert (Hpairy : proj1_sig y = (py, k)).
  { unfold py. rewrite (surjective_pairing (proj1_sig y)). rewrite Hky. reflexivity. }
  assert (Hfx : fb_comp s (proj1_sig x)
                = match op_for (nth k (sch_frontiers s) []) px k with
                  | Recv src _ => src | _ => px end).
  { rewrite Hpairx. unfold fb_comp. simpl.
    rewrite (op_at_desugar s px k Hpx Hk). reflexivity. }
  assert (Hfy : fb_comp s (proj1_sig y)
                = match op_for (nth k (sch_frontiers s) []) py k with
                  | Recv src _ => src | _ => py end).
  { rewrite Hpairy. unfold fb_comp. simpl.
    rewrite (op_at_desugar s py k Hpy Hk). reflexivity. }
  rewrite Hfx, Hfy in Hcomp.
  destruct (op_for (nth k (sch_frontiers s) []) px k) as [|az tz|az tz] eqn:Ezop;
  destruct (op_for (nth k (sch_frontiers s) []) py k) as [|aw tw|aw tw] eqn:Ewop.
  (* x Local, y Local : px = py *)
  + assert (Hpe : px = py) by exact Hcomp.
    left. assert (Hxe : x = y)
      by (apply event_eq_of_proj; rewrite Hpairx, Hpairy, Hpe; reflexivity).
    rewrite Hxe. apply poset_refl.
  (* x Local, y Send : px = py *)
  + assert (Hpe : px = py) by exact Hcomp.
    left. assert (Hxe : x = y)
      by (apply event_eq_of_proj; rewrite Hpairx, Hpairy, Hpe; reflexivity).
    rewrite Hxe. apply poset_refl.
  (* x Local, y Recv aw : px = aw, In (px, py) *)
  + assert (Htw : tw = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) py k aw tw)); exact Ewop).
    subst tw.
    assert (Hin : List.In (aw, py) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ aw py k Hfr); exact Ewop).
    rewrite <- Hcomp in Hin.
    left. apply (msg_hb_events s Hwf k x y Hkx Hky). fold px py; exact Hin.
  (* x Send az, y Local : px = py *)
  + assert (Hpe : px = py) by exact Hcomp.
    left. assert (Hxe : x = y)
      by (apply event_eq_of_proj; rewrite Hpairx, Hpairy, Hpe; reflexivity).
    rewrite Hxe. apply poset_refl.
  (* x Send az, y Send aw : px = py *)
  + assert (Hpe : px = py) by exact Hcomp.
    left. assert (Hxe : x = y)
      by (apply event_eq_of_proj; rewrite Hpairx, Hpairy, Hpe; reflexivity).
    rewrite Hxe. apply poset_refl.
  (* x Send az, y Recv aw : px = aw, In (px, py) *)
  + assert (Htw : tw = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) py k aw tw)); exact Ewop).
    subst tw.
    assert (Hin : List.In (aw, py) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ aw py k Hfr); exact Ewop).
    rewrite <- Hcomp in Hin.
    left. apply (msg_hb_events s Hwf k x y Hkx Hky). fold px py; exact Hin.
  (* x Recv az, y Local : az = py, In (py, px) *)
  + assert (Htz : tz = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) px k az tz)); exact Ezop).
    subst tz.
    assert (Hin : List.In (az, px) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ az px k Hfr); exact Ezop).
    rewrite Hcomp in Hin.
    right. apply (msg_hb_events s Hwf k y x Hky Hkx). fold px py; exact Hin.
  (* x Recv az, y Send aw : az = py, In (py, px) *)
  + assert (Htz : tz = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) px k az tz)); exact Ezop).
    subst tz.
    assert (Hin : List.In (az, px) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ az px k Hfr); exact Ezop).
    rewrite Hcomp in Hin.
    right. apply (msg_hb_events s Hwf k y x Hky Hkx). fold px py; exact Hin.
  (* x Recv az, y Recv aw : az = aw => px = py *)
  + assert (Htz : tz = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) px k az tz)); exact Ezop).
    assert (Htw : tw = k)
      by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) py k aw tw)); exact Ewop).
    subst tz tw.
    assert (Hinz : List.In (az, px) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ az px k Hfr); exact Ezop).
    assert (Hinw : List.In (aw, py) (nth k (sch_frontiers s) []))
      by (apply (op_for_recv_iff (sch_nprocs s) _ aw py k Hfr); exact Ewop).
    subst aw.
    assert (Hpe : px = py).
    { destruct Hfr as [_ Hnd].
      pose proof (find_fst_unique (nth k (sch_frontiers s) []) az px Hnd Hinz) as Hu1.
      pose proof (find_fst_unique (nth k (sch_frontiers s) []) az py Hnd Hinw) as Hu2.
      rewrite Hu1 in Hu2. injection Hu2 as <-. reflexivity. }
    left. assert (Hxe : x = y)
      by (apply event_eq_of_proj; rewrite Hpairx, Hpairy, Hpe; reflexivity).
    rewrite Hxe. apply poset_refl.
Qed.

Lemma frontier_block_dim_le2 :
  forall s, wf_schedule s -> forall k d,
    PosetDimension (sub_order (exec_of_schedule s) (frontier_block s k)) d -> d <= 2.
Proof.
  intros s Hwf k d Hdim.
  refine (disjoint_chains_dim_le2
           (sub_order (exec_of_schedule s) (frontier_block s k))
           (fun z => fb_comp s (proj1_sig (proj1_sig z)))
           _ _ d Hdim).
  - (* H1: sub_order z w -> fb_comp = fb_comp *)
    intros z w Hzw.
    (* underlying events and index facts *)
    pose proof (proj2_sig z) as Hkz. unfold Ensembles.In, frontier_block in Hkz.
    pose proof (proj2_sig w) as Hkw. unfold Ensembles.In, frontier_block in Hkw.
    unfold sub_order in Hzw.
    (* abbreviations for the underlying events / pids *)
    remember (proj1_sig z) as xz eqn:Hxzdef.
    remember (proj1_sig w) as xw eqn:Hxwdef.
    (* Hkz : snd (proj1_sig xz) = k ; Hkw : snd (proj1_sig xw) = k *)
    assert (Hkz' : snd (proj1_sig xz) = k) by (rewrite Hxzdef; exact Hkz).
    assert (Hkw' : snd (proj1_sig xw) = k) by (rewrite Hxwdef; exact Hkw).
    cbn beta in *.
    destruct (event_eq_dec (desugar s) xz xw) as [Heq | Hne].
    + simpl. rewrite Heq. reflexivity.
    + assert (Hsidx : snd (proj1_sig xz) = snd (proj1_sig xw))
        by (transitivity k; [exact Hkz' | symmetry; exact Hkw']).
      pose proof (hb_same_index_msg s Hwf xz xw Hsidx Hzw Hne) as Hin.
      rewrite Hkz' in Hin.
      set (pz := fst (proj1_sig xz)) in *.
      set (pw := fst (proj1_sig xw)) in *.
      assert (Hpz : pz < sch_nprocs s)
        by (unfold pz; rewrite Hxzdef; apply event_pid_lt).
      assert (Hpw : pw < sch_nprocs s)
        by (unfold pw; rewrite Hxwdef; apply event_pid_lt).
      assert (Hk : k < length (sch_frontiers s)).
      { rewrite <- Hkz', Hxzdef. apply event_index_lt. }
      assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
        by (apply Hwf; apply nth_In; exact Hk).
      pose proof (proj2 (op_for_send_iff (sch_nprocs s) _ pz pw k Hfr) Hin) as Hsend.
      pose proof (proj2 (op_for_recv_iff (sch_nprocs s) _ pz pw k Hfr) Hin) as Hrecv.
      assert (Hpairz : proj1_sig xz = (pz, k)).
      { unfold pz. rewrite (surjective_pairing (proj1_sig xz)). rewrite Hkz'. reflexivity. }
      assert (Hpairw : proj1_sig xw = (pw, k)).
      { unfold pw. rewrite (surjective_pairing (proj1_sig xw)). rewrite Hkw'. reflexivity. }
      assert (Hcz : fb_comp s (proj1_sig xz) = pz).
      { rewrite Hpairz. exact (fb_comp_send s pz pw k Hpz Hk Hsend). }
      assert (Hcw : fb_comp s (proj1_sig xw) = pz).
      { rewrite Hpairw. exact (fb_comp_recv s pz pw k Hpw Hk Hrecv). }
      cbn beta. rewrite Hcz, Hcw. reflexivity.
  - (* H2: fb_comp = fb_comp -> sub_order z w \/ sub_order w z *)
    intros z w Hcomp.
    pose proof (proj2_sig z) as Hkz. unfold Ensembles.In, frontier_block in Hkz.
    pose proof (proj2_sig w) as Hkw. unfold Ensembles.In, frontier_block in Hkw.
    unfold sub_order.
    remember (proj1_sig z) as xz eqn:Hxzdef.
    remember (proj1_sig w) as xw eqn:Hxwdef.
    assert (Hkz' : snd (proj1_sig xz) = k) by (rewrite Hxzdef; exact Hkz).
    assert (Hkw' : snd (proj1_sig xw) = k) by (rewrite Hxwdef; exact Hkw).
    cbn beta in Hcomp.
    set (pz := fst (proj1_sig xz)) in *.
    set (pw := fst (proj1_sig xw)) in *.
    assert (Hpz : pz < sch_nprocs s)
      by (unfold pz; rewrite Hxzdef; apply event_pid_lt).
    assert (Hpw : pw < sch_nprocs s)
      by (unfold pw; rewrite Hxwdef; apply event_pid_lt).
    assert (Hk : k < length (sch_frontiers s)).
    { rewrite <- Hkz', Hxzdef. apply event_index_lt. }
    assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
      by (apply Hwf; apply nth_In; exact Hk).
    assert (Hpairz : proj1_sig xz = (pz, k)).
    { unfold pz. rewrite (surjective_pairing (proj1_sig xz)). rewrite Hkz'. reflexivity. }
    assert (Hpairw : proj1_sig xw = (pw, k)).
    { unfold pw. rewrite (surjective_pairing (proj1_sig xw)). rewrite Hkw'. reflexivity. }
    (* fb_comp at each event, expressed via op_for at index k *)
    assert (Hfz : fb_comp s (proj1_sig xz)
                  = match op_for (nth k (sch_frontiers s) []) pz k with
                    | Recv src _ => src | _ => pz end).
    { rewrite Hpairz. unfold fb_comp. simpl.
      rewrite (op_at_desugar s pz k Hpz Hk). reflexivity. }
    assert (Hfw : fb_comp s (proj1_sig xw)
                  = match op_for (nth k (sch_frontiers s) []) pw k with
                    | Recv src _ => src | _ => pw end).
    { rewrite Hpairw. unfold fb_comp. simpl.
      rewrite (op_at_desugar s pw k Hpw Hk). reflexivity. }
    rewrite Hfz, Hfw in Hcomp.
    (* classify both ops *)
    destruct (op_for (nth k (sch_frontiers s) []) pz k) as [|az tz|az tz] eqn:Ezop;
    destruct (op_for (nth k (sch_frontiers s) []) pw k) as [|aw tw|aw tw] eqn:Ewop.
    (* z Local, w Local : pz = pw *)
    + assert (Hpe : pz = pw) by exact Hcomp.
      left.
      assert (Hxe : xz = xw)
        by (apply event_eq_of_proj; rewrite Hpairz, Hpairw, Hpe; reflexivity).
      rewrite Hxe. apply poset_refl.
    (* z Local, w Send : pz = pw *)
    + assert (Hpe : pz = pw) by exact Hcomp.
      left.
      assert (Hxe : xz = xw)
        by (apply event_eq_of_proj; rewrite Hpairz, Hpairw, Hpe; reflexivity).
      rewrite Hxe. apply poset_refl.
    (* z Local, w Recv aw : pz = aw, w receives from aw = pz, so In (pz, pw) *)
    + assert (Htw : tw = k)
        by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) pw k aw tw)); exact Ewop).
      subst tw.
      assert (Hin : List.In (aw, pw) (nth k (sch_frontiers s) []))
        by (apply (op_for_recv_iff (sch_nprocs s) _ aw pw k Hfr); exact Ewop).
      (* aw = pz from Hcomp : pz = aw *)
      rewrite <- Hcomp in Hin.
      (* In (pz, pw) -> hb xz xw *)
      left. apply (msg_hb_events s Hwf k xz xw Hkz' Hkw').
      fold pz pw; exact Hin.
    (* z Send az, w Local : pz = pw *)
    + assert (Hpe : pz = pw) by exact Hcomp.
      left.
      assert (Hxe : xz = xw)
        by (apply event_eq_of_proj; rewrite Hpairz, Hpairw, Hpe; reflexivity).
      rewrite Hxe. apply poset_refl.
    (* z Send az, w Send aw : pz = pw *)
    + assert (Hpe : pz = pw) by exact Hcomp.
      left.
      assert (Hxe : xz = xw)
        by (apply event_eq_of_proj; rewrite Hpairz, Hpairw, Hpe; reflexivity).
      rewrite Hxe. apply poset_refl.
    (* z Send az, w Recv aw : pz = aw, In (aw, pw) = In (pz, pw) *)
    + assert (Htw : tw = k)
        by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) pw k aw tw)); exact Ewop).
      subst tw.
      assert (Hin : List.In (aw, pw) (nth k (sch_frontiers s) []))
        by (apply (op_for_recv_iff (sch_nprocs s) _ aw pw k Hfr); exact Ewop).
      rewrite <- Hcomp in Hin.
      left. apply (msg_hb_events s Hwf k xz xw Hkz' Hkw').
      fold pz pw; exact Hin.
    (* z Recv az, w Local : az = pw, w<-... actually z receives from az = pw, In (pw, pz) *)
    + assert (Htz : tz = k)
        by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) pz k az tz)); exact Ezop).
      subst tz.
      assert (Hin : List.In (az, pz) (nth k (sch_frontiers s) []))
        by (apply (op_for_recv_iff (sch_nprocs s) _ az pz k Hfr); exact Ezop).
      (* Hcomp : az = pw *)
      rewrite Hcomp in Hin.
      right. apply (msg_hb_events s Hwf k xw xz Hkw' Hkz').
      fold pz pw; exact Hin.
    (* z Recv az, w Send aw : az = pw, In (pw, pz) *)
    + assert (Htz : tz = k)
        by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) pz k az tz)); exact Ezop).
      subst tz.
      assert (Hin : List.In (az, pz) (nth k (sch_frontiers s) []))
        by (apply (op_for_recv_iff (sch_nprocs s) _ az pz k Hfr); exact Ezop).
      rewrite Hcomp in Hin.
      right. apply (msg_hb_events s Hwf k xw xz Hkw' Hkz').
      fold pz pw; exact Hin.
    (* z Recv az, w Recv aw : az = aw ; both receive from same source => pz = pw *)
    + assert (Htz : tz = k)
        by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) pz k az tz)); exact Ezop).
      assert (Htw : tw = k)
        by (apply (proj2 (op_for_tag (nth k (sch_frontiers s) []) pw k aw tw)); exact Ewop).
      subst tz tw.
      assert (Hinz : List.In (az, pz) (nth k (sch_frontiers s) []))
        by (apply (op_for_recv_iff (sch_nprocs s) _ az pz k Hfr); exact Ezop).
      assert (Hinw : List.In (aw, pw) (nth k (sch_frontiers s) []))
        by (apply (op_for_recv_iff (sch_nprocs s) _ aw pw k Hfr); exact Ewop).
      (* Hcomp : az = aw ; same sender az => same Recv endpoint => pz = pw *)
      subst aw.
      assert (Hpe : pz = pw).
      { (* az appears as a Send-source twice in the frontier; NoDup endpoints
           forces the two Recv targets to coincide. *)
        destruct Hfr as [_ Hnd].
        pose proof (find_fst_unique (nth k (sch_frontiers s) []) az pz Hnd Hinz) as Hu1.
        pose proof (find_fst_unique (nth k (sch_frontiers s) []) az pw Hnd Hinw) as Hu2.
        rewrite Hu1 in Hu2. injection Hu2 as <-. reflexivity. }
      left.
      assert (Hxe : xz = xw)
        by (apply event_eq_of_proj; rewrite Hpairz, Hpairw, Hpe; reflexivity).
      rewrite Hxe. apply poset_refl.
Qed.

(* Payoff: a fully-synchronized schedule's execution has dimension <= 2,
   because every frontier block is a disjoint union of chains. *)
Corollary fully_sync_frontier_dim_le2 :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
    IsFullySync (exec_of_schedule s) (frontier_blocks s) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
Proof.
  intros s Hwf Hnp Hfs.
  apply (fully_sync_dim_le2 (exec_of_schedule s) (frontier_blocks s) Hfs).
  intros blk Hblk.
  (* identify the block index *)
  apply in_map_iff in Hblk. destruct Hblk as [k [Hbeq Hkin]]. subst blk.
  apply in_seq in Hkin. destruct Hkin as [_ Hk]. rewrite Nat.add_0_l in Hk.
  (* a whole-execution dimension witness *)
  destruct (exec_dimension_exists (exec_of_schedule s)) as [d0 [Hd0]].
  destruct (subposet_dimension_le (ep_order (exec_of_schedule s))
              (frontier_block s k) d0 Hd0) as [dq [Hinh Hle0]].
  exists dq. split.
  - (* inhabited (PosetDimension (sub_order ... (frontier_block s k)) dq) *)
    exact Hinh.
  - destruct Hinh as [Hbare].
    exact (frontier_block_dim_le2 s Hwf k dq Hbare).
Qed.

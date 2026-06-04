(* Schedule — high-level frontier model and its desugaring into a
   RankedProgram, plus agreement of the poset order with hb. *)

From Stdlib Require Import List Arith Lia Relation_Operators.
From Execution Require Import Op Event Edges Rank Poset.
Import ListNotations.

Definition Frontier := list (Pid * Pid).

Record Schedule := {
  sch_nprocs    : nat;
  sch_frontiers : list Frontier
}.

(* op of process p at frontier k *)
Definition op_for (fr : Frontier) (p : Pid) (k : nat) : Op :=
  match find (fun pq => Nat.eqb (fst pq) p) fr with
  | Some (_, q) => Send q k
  | None =>
    match find (fun pq => Nat.eqb (snd pq) p) fr with
    | Some (s, _) => Recv s k
    | None => Local
    end
  end.

Definition desugar_prog (s : Schedule) : Program :=
  {| procs :=
       map (fun p => map (fun k => op_for (nth k (sch_frontiers s) []) p k)
                         (seq 0 (length (sch_frontiers s))))
           (seq 0 (sch_nprocs s)) |}.

Definition desugar_rank (s : Schedule) : nat * nat -> nat :=
  fun pi => 2 * snd pi
            + match op_at (desugar_prog s) (fst pi) (snd pi) with
              | Some (Recv _ _) => 1
              | _ => 0
              end.

(* ------------------------------------------------------------------ *)
(* Structural helpers                                                   *)
(* ------------------------------------------------------------------ *)

Lemma nprocs_desugar :
  forall s, nprocs (desugar_prog s) = sch_nprocs s.
Proof.
  intro s. unfold nprocs, desugar_prog. simpl.
  rewrite length_map, length_seq. reflexivity.
Qed.

(* the op-list of process p (when p is in range) *)
Lemma proc_ops_desugar :
  forall s p, p < sch_nprocs s ->
    proc_ops (desugar_prog s) p =
      map (fun k => op_for (nth k (sch_frontiers s) []) p k)
          (seq 0 (length (sch_frontiers s))).
Proof.
  intros s p Hp.
  unfold proc_ops, desugar_prog. simpl.
  rewrite (nth_indep _ _
             (map (fun k => op_for (nth k (sch_frontiers s) []) 0 k)
                  (seq 0 (length (sch_frontiers s))))).
  - rewrite (map_nth
               (fun p => map (fun k => op_for (nth k (sch_frontiers s) []) p k)
                             (seq 0 (length (sch_frontiers s))))
               (seq 0 (sch_nprocs s)) 0 p).
    rewrite seq_nth by exact Hp. reflexivity.
  - rewrite length_map, length_seq. exact Hp.
Qed.

(* every process's op-list has length S = #frontiers *)
Lemma proc_len_desugar :
  forall s p, p < sch_nprocs s ->
    proc_len (desugar_prog s) p = length (sch_frontiers s).
Proof.
  intros s p Hp.
  unfold proc_len. rewrite proc_ops_desugar by exact Hp.
  rewrite length_map, length_seq. reflexivity.
Qed.

(* op_at reads back exactly op_for, in range *)
Lemma op_at_desugar :
  forall s p k, p < sch_nprocs s -> k < length (sch_frontiers s) ->
    op_at (desugar_prog s) p k = Some (op_for (nth k (sch_frontiers s) []) p k).
Proof.
  intros s p k Hp Hk.
  unfold op_at. rewrite proc_ops_desugar by exact Hp.
  rewrite (nth_error_map (fun k => op_for (nth k (sch_frontiers s) []) p k)).
  assert (Hseq : nth_error (seq 0 (length (sch_frontiers s))) k = Some k).
  { rewrite nth_error_nth' with (d := 0).
    - rewrite seq_nth by exact Hk. reflexivity.
    - rewrite length_seq. exact Hk. }
  rewrite Hseq. reflexivity.
Qed.

(* op_for always tags a Send/Recv with the frontier index k *)
Lemma op_for_tag :
  forall fr p k q t,
    (op_for fr p k = Send q t -> t = k) /\
    (op_for fr p k = Recv q t -> t = k).
Proof.
  intros fr p k q t.
  unfold op_for.
  destruct (find (fun pq => Nat.eqb (fst pq) p) fr) as [[a b]|].
  - split.
    + intro H. injection H as _ <-. reflexivity.
    + intro H. discriminate H.
  - destruct (find (fun pq => Nat.eqb (snd pq) p) fr) as [[a b]|].
    + split.
      * intro H. discriminate H.
      * intro H. injection H as _ <-. reflexivity.
    + split; intro H; discriminate H.
Qed.

(* rank has the shape 2*i + c with c <= 1 *)
Lemma desugar_rank_form :
  forall s pi, exists c, c <= 1 /\ desugar_rank s pi = 2 * snd pi + c.
Proof.
  intros s pi. unfold desugar_rank.
  destruct (op_at (desugar_prog s) (fst pi) (snd pi)) as [o|].
  - destruct o.
    + exists 0. split; lia.
    + exists 0. split; lia.
    + exists 1. split; lia.
  - exists 0. split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The monotonicity obligation                                          *)
(* ------------------------------------------------------------------ *)

Lemma desugar_rank_mono :
  forall s (a b : Event (desugar_prog s)),
    edge (desugar_prog s) a b ->
    desugar_rank s (proj1_sig a) < desugar_rank s (proj1_sig b).
Proof.
  intros s a b Hedge.
  destruct a as [[pa ia] Ha]; destruct b as [[pb ib] Hb].
  unfold In, ValidSet, Valid in Ha, Hb. simpl in Ha, Hb.
  destruct Ha as [Hpa Hia]; destruct Hb as [Hpb Hib].
  assert (HpaN : pa < sch_nprocs s) by (rewrite <- nprocs_desugar; exact Hpa).
  assert (HpbN : pb < sch_nprocs s) by (rewrite <- nprocs_desugar; exact Hpb).
  assert (HiaF : ia < length (sch_frontiers s)).
  { rewrite <- (proc_len_desugar s pa HpaN). exact Hia. }
  assert (HibF : ib < length (sch_frontiers s)).
  { rewrite <- (proc_len_desugar s pb HpbN). exact Hib. }
  simpl proj1_sig.
  unfold edge in Hedge. simpl in Hedge.
  destruct Hedge as [[Hpeq Hseq] | [t [Hsend Hrecv]]].
  - (* program order *)
    subst pb. subst ib.
    destruct (desugar_rank_form s (pa, ia)) as [ca [Hca Ea]].
    destruct (desugar_rank_form s (pa, S ia)) as [cb [Hcb Eb]].
    simpl in Ea, Eb. rewrite Ea, Eb. lia.
  - (* message *)
    rewrite op_at_desugar in Hsend by assumption.
    rewrite op_at_desugar in Hrecv by assumption.
    injection Hsend as Hsend.
    injection Hrecv as Hrecv.
    pose proof (op_for_tag (nth ia (sch_frontiers s) []) pa ia pb t) as [Hst _].
    pose proof (op_for_tag (nth ib (sch_frontiers s) []) pb ib pa t) as [_ Hrt].
    specialize (Hst Hsend). specialize (Hrt Hrecv).
    subst t.
    assert (ia = ib) by lia. subst ib.
    unfold desugar_rank. simpl.
    rewrite (op_at_desugar s pa ia HpaN HiaF).
    rewrite (op_at_desugar s pb ia HpbN HibF).
    rewrite Hsend, Hrecv. lia.
Qed.

Definition desugar (s : Schedule) : RankedProgram :=
  {| rp_prog := desugar_prog s;
     rp_rank := desugar_rank s;
     rp_rank_mono := desugar_rank_mono s |}.

Definition exec_of_schedule (s : Schedule) : ExecPoset := exec_of (desugar s).

(* the poset order from the schedule IS hb of the desugared program *)
Theorem schedule_program_agree :
  forall s (a b : Event (desugar s)),
    ep_order (exec_of_schedule s) a b <-> hb (desugar s) a b.
Proof. intros; reflexivity. Qed.

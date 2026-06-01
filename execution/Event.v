From Stdlib Require Import List Arith Lia Ensembles Finite_sets ProofIrrelevance.
From Execution Require Import Op.
Import ListNotations.

Section Carrier.
  Context (P : Program).

  (* (p,i) is a valid event iff p is a real process and i indexes one of its ops *)
  Definition Valid (pi : nat * nat) : Prop :=
    fst pi < nprocs P /\ snd pi < proc_len P (fst pi).

  Definition ValidSet : Ensemble (nat * nat) := fun pi => Valid pi.

  (* Carrier type: dependent pair (process, index) carrying its validity proof. *)
  Definition Event : Type := { pi : nat * nat | In (nat*nat) ValidSet pi }.

  Definition ev_pid (e : Event) : Pid := fst (proj1_sig e).
  Definition ev_idx (e : Event) : nat := snd (proj1_sig e).

  (* Total number of events. *)
  Definition total : nat := list_sum (map (proc_len P) (seq 0 (nprocs P))).

  (* Explicit enumeration of every valid (p,i) as raw pairs. *)
  Definition raw_events : list (nat * nat) :=
    flat_map (fun p => map (fun i => (p, i)) (seq 0 (proc_len P p)))
             (seq 0 (nprocs P)).
End Carrier.

(* ------------------------------------------------------------------ *)
(* Proofs (P explicit)                                                  *)
(* ------------------------------------------------------------------ *)

Lemma raw_events_spec : forall P pi, List.In pi (raw_events P) <-> Valid P pi.
Proof.
  intros P [p i].
  unfold raw_events, Valid; simpl.
  rewrite in_flat_map.
  split.
  - intros [q [Hq Hpi]].
    rewrite in_seq in Hq.
    apply in_map_iff in Hpi.
    destruct Hpi as [j [Heq Hj]].
    inversion Heq; subst.
    rewrite in_seq in Hj.
    split; lia.
  - intros [Hp Hi].
    exists p.
    split.
    + rewrite in_seq. lia.
    + apply in_map_iff.
      exists i.
      split; [reflexivity|].
      rewrite in_seq. lia.
Qed.

Lemma raw_events_length : forall P, length (raw_events P) = total P.
Proof.
  intro P.
  unfold raw_events, total.
  rewrite length_flat_map.
  f_equal.
  apply map_ext.
  intro p.
  rewrite length_map, length_seq.
  reflexivity.
Qed.

(* Elements in the block for process p all have first component p *)
Lemma block_fst : forall (n k : nat) (pi : nat * nat),
  List.In pi (map (fun i => (n, i)) (seq 0 k)) ->
  fst pi = n.
Proof.
  intros n k pi Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [<- _]].
  reflexivity.
Qed.

(* Two blocks for different processes are disjoint *)
Lemma blocks_disjoint : forall P p1 p2,
  p1 <> p2 ->
  forall a,
    List.In a (map (fun i => (p1, i)) (seq 0 (proc_len P p1))) ->
    ~ List.In a (map (fun i => (p2, i)) (seq 0 (proc_len P p2))).
Proof.
  intros P p1 p2 Hne a Ha1 Ha2.
  apply block_fst in Ha1.
  apply block_fst in Ha2.
  congruence.
Qed.

(* The list of blocks indexed by l has pairwise disjoint blocks when l is NoDup *)
Lemma NoDup_blocks_FOP : forall P l,
  NoDup l ->
  ForallOrdPairs
    (fun b1 b2 => forall a, List.In a b1 -> ~ List.In a b2)
    (map (fun p => map (fun i => (p, i)) (seq 0 (proc_len P p))) l).
Proof.
  intros P l Hnd.
  induction Hnd as [|p l Hnotin Hnd IH].
  - constructor.
  - simpl. constructor.
    + rewrite Forall_forall.
      intros b2 Hb2.
      apply in_map_iff in Hb2.
      destruct Hb2 as [q [<- Hq]].
      apply blocks_disjoint.
      intro Heq; subst.
      apply Hnotin. assumption.
    + assumption.
Qed.

Lemma raw_events_NoDup : forall P, NoDup (raw_events P).
Proof.
  intro P.
  unfold raw_events.
  rewrite flat_map_concat_map.
  apply NoDup_concat.
  - (* Each inner block is NoDup *)
    rewrite Forall_forall.
    intros b Hb.
    apply in_map_iff in Hb.
    destruct Hb as [p [<- _]].
    apply NoDup_map_NoDup_ForallPairs.
    + intros x y _ _ Heq.
      inversion Heq. reflexivity.
    + apply seq_NoDup.
  - (* Blocks from distinct indices are disjoint *)
    apply NoDup_blocks_FOP.
    apply seq_NoDup.
Qed.

Lemma event_eq_dec : forall P (a b : Event P), {a = b} + {a <> b}.
Proof.
  intros P [pi1 Hpi1] [pi2 Hpi2].
  destruct (Nat.eq_dec (fst pi1) (fst pi2)) as [Hf|Hf].
  - destruct (Nat.eq_dec (snd pi1) (snd pi2)) as [Hs|Hs].
    + left.
      assert (pi1 = pi2) as Heq.
      { destruct pi1 as [p1 i1]; destruct pi2 as [p2 i2].
        simpl in *. subst. reflexivity. }
      subst.
      f_equal.
      apply proof_irrelevance.
    + right.
      intro H.
      injection H as H.
      apply Hs.
      rewrite H. reflexivity.
  - right.
    intro H.
    injection H as H.
    apply Hf.
    rewrite H. reflexivity.
Qed.

(* sync-shape operational definitions + IsFullySync bridge *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Frontier
                              FullySync FullySyncDim2 Schedule.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition synchronous_message (P : Program) (p i q j : nat) (t : Tag) : Prop :=
  matched P p i q j t /\ i = j.

Definition sync_shaped (P : Program) : Prop :=
  forall p i q j t, matched P p i q j t -> i = j.

(* a Some op_at in a desugared program pins both indices in range *)
Lemma op_at_desugar_range :
  forall s p i o,
    op_at (desugar_prog s) p i = Some o ->
    p < sch_nprocs s /\ i < length (sch_frontiers s).
Proof.
  intros s p i o Hop.
  (* op_at is a non-None nth_error, hence i < length of the op-list *)
  assert (Hi : i < length (proc_ops (desugar_prog s) p)).
  { apply nth_error_Some. unfold op_at in Hop. rewrite Hop. discriminate. }
  (* first, p < sch_nprocs s, otherwise the op-list is empty *)
  assert (Hp : p < sch_nprocs s).
  { destruct (Nat.lt_ge_cases p (sch_nprocs s)) as [Hlt | Hge]; [exact Hlt|].
    exfalso.
    assert (Hempty : proc_ops (desugar_prog s) p = []).
    { unfold proc_ops, desugar_prog. simpl.
      apply nth_overflow. rewrite length_map, length_seq. exact Hge. }
    rewrite Hempty in Hi. simpl in Hi. lia. }
  split; [exact Hp|].
  (* now i < proc_len (desugar_prog s) p = length (sch_frontiers s) *)
  change (length (proc_ops (desugar_prog s) p))
    with (proc_len (desugar_prog s) p) in Hi.
  rewrite (proc_len_desugar s p Hp) in Hi. exact Hi.
Qed.

Lemma desugar_sync_shaped : forall s, sync_shaped (desugar_prog s).
Proof.
  intros s p i q j t [Hs Hr].
  destruct (op_at_desugar_range s p i _ Hs) as [Hp Hi].
  destruct (op_at_desugar_range s q j _ Hr) as [Hq Hj].
  rewrite (op_at_desugar s p i Hp Hi) in Hs.
  injection Hs as Hs'.
  pose proof (proj1 (op_for_tag (nth i (sch_frontiers s) []) p i q t) Hs') as Hti.
  rewrite (op_at_desugar s q j Hq Hj) in Hr.
  injection Hr as Hr'.
  pose proof (proj2 (op_for_tag (nth j (sch_frontiers s) []) q j p t) Hr') as Htj.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Frontier blocks: partition the carrier by local (frontier) index.  *)
(* ------------------------------------------------------------------ *)

Definition frontier_block (s : Schedule) (k : nat)
  : Ensemble (ep_carrier (exec_of_schedule s)) :=
  fun x => snd (proj1_sig x) = k.

Definition frontier_blocks (s : Schedule)
  : list (Ensemble (ep_carrier (exec_of_schedule s))) :=
  map (frontier_block s) (seq 0 (length (sch_frontiers s))).

Definition FullySynchronizing (s : Schedule) : Prop :=
  forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) < snd (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y.

(* an event's local index is < #frontiers *)
Lemma event_index_lt :
  forall s (x : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) < length (sch_frontiers s).
Proof.
  intros s x.
  pose proof (proj2_sig x) as Hv.
  unfold Ensembles.In, ValidSet, Valid in Hv.
  destruct Hv as [Hfst Hsnd].
  (* nprocs (desugar s) = nprocs (desugar_prog s) definitionally via rp_prog;
     feed Hfst (after nprocs_desugar) to proc_len_desugar *)
  assert (Hfst' : fst (proj1_sig x) < sch_nprocs s)
    by (rewrite <- nprocs_desugar; exact Hfst).
  change (snd (proj1_sig x) < proc_len (desugar_prog s) (fst (proj1_sig x)))
    in Hsnd.
  rewrite (proc_len_desugar s (fst (proj1_sig x)) Hfst') in Hsnd.
  exact Hsnd.
Qed.

Lemma length_frontier_blocks :
  forall s, length (frontier_blocks s) = length (sch_frontiers s).
Proof.
  intros s. unfold frontier_blocks.
  rewrite length_map, length_seq. reflexivity.
Qed.

Lemma nth_frontier_blocks :
  forall s k, k < length (sch_frontiers s) ->
    nth k (frontier_blocks s) (Empty_set _) = frontier_block s k.
Proof.
  intros s k Hk. unfold frontier_blocks.
  rewrite (nth_indep _ _ (frontier_block s 0))
    by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth.
  rewrite seq_nth by exact Hk.
  reflexivity.
Qed.

Lemma union_upto_frontier_blocks :
  forall s k x,
    Ensembles.In _ (union_upto (exec_of_schedule s) (frontier_blocks s) k) x <->
    snd (proj1_sig x) < k.
Proof.
  intros s k x. unfold union_upto, Ensembles.In. split.
  - intros [i [Hik Hin]].
    (* i must be a valid index, else nth = Empty_set and Hin is False *)
    assert (Hi : i < length (sch_frontiers s)).
    { destruct (Nat.lt_ge_cases i (length (sch_frontiers s))) as [Hlt | Hge].
      - exact Hlt.
      - exfalso.
        rewrite nth_overflow in Hin
          by (rewrite length_frontier_blocks; exact Hge).
        destruct Hin. }
    rewrite (nth_frontier_blocks s i Hi) in Hin.
    unfold frontier_block, Ensembles.In in Hin.
    lia.
  - intro Hlt.
    exists (snd (proj1_sig x)). split; [exact Hlt|].
    rewrite (nth_frontier_blocks s _ (event_index_lt s x)).
    unfold frontier_block, Ensembles.In. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Bridge: a fully-synchronizing schedule's execution is IsFullySync   *)
(* by its frontier blocks.                                             *)
(* ------------------------------------------------------------------ *)

(* a valid event at (0, k) when 0 < sch_nprocs s and k < #frontiers *)
Lemma event_at_index :
  forall s, 0 < sch_nprocs s -> forall k, k < length (sch_frontiers s) ->
    { x : ep_carrier (exec_of_schedule s) | snd (proj1_sig x) = k }.
Proof.
  intros s Hnp k Hk.
  assert (Hvalid : Ensembles.In (nat * nat)
                     (ValidSet (desugar s)) (0, k)).
  { unfold Ensembles.In, ValidSet, Valid. simpl. split.
    - change (0 < nprocs (desugar_prog s)).
      rewrite nprocs_desugar. exact Hnp.
    - change (k < proc_len (desugar_prog s) 0).
      rewrite (proc_len_desugar s 0 Hnp). exact Hk. }
  exists (exist _ (0, k) Hvalid). reflexivity.
Defined.

Lemma fully_synchronizing_is_fully_sync :
  forall s, FullySynchronizing s ->
    0 < sch_nprocs s ->
    IsFullySync (exec_of_schedule s) (frontier_blocks s).
Proof.
  intros s Hfsync Hnp.
  unfold IsFullySync.
  split; [|split; [|split]].
  - (* nonempty *)
    intros blk Hblk.
    apply in_map_iff in Hblk.
    destruct Hblk as [k [Hbeq Hkin]]. subst blk.
    apply in_seq in Hkin.
    assert (Hk : k < length (sch_frontiers s)) by lia.
    destruct (event_at_index s Hnp k Hk) as [x Hx].
    exists x. unfold frontier_block, Ensembles.In. exact Hx.
  - (* cover *)
    intro x. exists (snd (proj1_sig x)).
    rewrite length_frontier_blocks.
    split; [exact (event_index_lt s x)|].
    rewrite (nth_frontier_blocks s (snd (proj1_sig x)) (event_index_lt s x)).
    unfold frontier_block, Ensembles.In. reflexivity.
  - (* disjoint *)
    intros i j x Hi Hj Hij Hin.
    rewrite length_frontier_blocks in Hi, Hj.
    rewrite (nth_frontier_blocks s i Hi) in Hin.
    unfold frontier_block, Ensembles.In in Hin.
    rewrite (nth_frontier_blocks s j Hj).
    unfold frontier_block, Ensembles.In.
    intro Hbad.
    apply Hij. rewrite <- Hin, <- Hbad. reflexivity.
  - (* prefix barrier *)
    intros k Hk0 Hk.
    rewrite length_frontier_blocks in Hk.
    assert (Hfr : 0 < length (sch_frontiers s)) by lia.
    unfold IsBarrier.
    split; [|split; [|split; [|split]]].
    + (* cover *)
      intro x. apply classic.
    + (* disjoint *)
      intros x [H1 H2]. exact (H2 H1).
    + (* inhabited L *)
      destruct (event_at_index s Hnp 0 Hfr) as [x Hx].
      exists x.
      apply (union_upto_frontier_blocks s k x).
      rewrite Hx. exact Hk0.
    + (* inhabited U *)
      destruct (event_at_index s Hnp k Hk) as [y Hy].
      exists y.
      intro Hyin.
      apply (union_upto_frontier_blocks s k y) in Hyin.
      rewrite Hy in Hyin. lia.
    + (* Hbelow *)
      intros x y Hx Hy.
      apply (union_upto_frontier_blocks s k x) in Hx.
      assert (Hyk : ~ (snd (proj1_sig y) < k)).
      { intro Hc. apply Hy.
        apply (union_upto_frontier_blocks s k y). exact Hc. }
      assert (Hlt : snd (proj1_sig x) < snd (proj1_sig y)) by lia.
      exact (Hfsync x y Hlt).
Qed.

(* ------------------------------------------------------------------ *)
(* Payoff corollary: fully-synchronizing + per-block dim≤2             *)
(*   => the whole execution has dimension ≤ 2.                         *)
(* ------------------------------------------------------------------ *)

Corollary fully_synchronizing_dim2 :
  forall s, FullySynchronizing s -> 0 < sch_nprocs s ->
    (forall blk, List.In blk (frontier_blocks s) ->
       exists d, inhabited (PosetDimension (sub_order (exec_of_schedule s) blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
Proof.
  intros s Hfsync Hnp Hblocks.
  apply (fully_sync_dim_le2 (exec_of_schedule s) (frontier_blocks s)).
  - exact (fully_synchronizing_is_fully_sync s Hfsync Hnp).
  - exact Hblocks.
Qed.

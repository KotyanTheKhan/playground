(* thick (window) barrier: a window of frontiers synchronizes all processes
   across it, for arbitrary process count. *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical
                           Relation_Operators ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Frontier
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape ConnSync.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition window_step (s : Schedule) (k p q : nat) : Prop :=
  p = q \/ List.In (p, q) (nth k (sch_frontiers s) []).

Fixpoint window_reach (s : Schedule) (a p m q : nat) : Prop :=
  match m with
  | 0 => p = q
  | S m' => exists r, window_reach s a p m' r /\ window_step s (a + m') r q
  end.

Lemma prog_chain_aux :
  forall s p d i (Hp : p < sch_nprocs s)
         (Hi : i < length (sch_frontiers s)) (Hk : i + d < length (sch_frontiers s)),
    ep_order (exec_of_schedule s) (mk_event s p i Hp Hi) (mk_event s p (i + d) Hp Hk).
Proof.
  intros s p d. induction d as [|d' IH]; intros i Hp Hi Hk.
  - replace (mk_event s p (i + 0) Hp Hk) with (mk_event s p i Hp Hi)
      by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
    apply rt_refl.
  - assert (Hid : i + d' < length (sch_frontiers s)) by lia.
    assert (HSid : S (i + d') < length (sch_frontiers s)) by lia.
    apply (hb_trans (desugar s) _ (mk_event s p (i + d') Hp Hid) _).
    + apply IH.
    + replace (mk_event s p (i + S d') Hp Hk) with (mk_event s p (S (i + d')) Hp HSid)
        by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
      apply (prog_step s p (i + d') Hp Hid HSid).
Qed.

Lemma prog_chain :
  forall s p i k (Hp : p < sch_nprocs s)
         (Hi : i < length (sch_frontiers s)) (Hk : k < length (sch_frontiers s)),
    i <= k ->
    ep_order (exec_of_schedule s) (mk_event s p i Hp Hi) (mk_event s p k Hp Hk).
Proof.
  intros s p i k Hp Hi Hk Hle.
  assert (Hk' : i + (k - i) < length (sch_frontiers s))
    by (replace (i + (k - i)) with k by lia; exact Hk).
  replace (mk_event s p k Hp Hk) with (mk_event s p (i + (k - i)) Hp Hk')
    by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
  apply prog_chain_aux.
Qed.

Lemma window_reach_hb :
  forall s, wf_schedule s -> forall m a p q
    (Hp : p < sch_nprocs s) (Hq : q < sch_nprocs s)
    (Ha : a < length (sch_frontiers s)) (Hb : a + m < length (sch_frontiers s)),
    window_reach s a p m q ->
    ep_order (exec_of_schedule s) (mk_event s p a Hp Ha) (mk_event s q (a + m) Hq Hb).
Proof.
  intros s Hwf m. induction m as [|m' IH]; intros a p q Hp Hq Ha Hb Hwr.
  - simpl in Hwr. subst q.
    replace (mk_event s p (a + 0) Hq Hb) with (mk_event s p a Hp Ha)
      by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
    apply rt_refl.
  - simpl in Hwr. destruct Hwr as [r [Hreach Hstep]].
    assert (Ham' : a + m' < length (sch_frontiers s)) by lia.
    assert (HSam' : S (a + m') < length (sch_frontiers s)) by lia.
    assert (Hr : r < sch_nprocs s).
    { destruct Hstep as [Heq | Hin].
      - subst r. exact Hq.
      - assert (Hfr : wf_frontier (sch_nprocs s) (nth (a + m') (sch_frontiers s) []))
          by (apply Hwf; apply nth_In; exact Ham').
        destruct Hfr as [Hrange _]. destruct (Hrange r q Hin) as [Hr0 _]. exact Hr0. }
    replace (mk_event s q (a + S m') Hq Hb) with (mk_event s q (S (a + m')) Hq HSam')
      by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
    apply (hb_trans (desugar s) _ (mk_event s r (a + m') Hr Ham') _).
    + apply (IH a p r Hp Hr Ha Ham' Hreach).
    + destruct Hstep as [Heq | Hin].
      * subst r.
        replace (mk_event s q (a + m') Hr Ham') with (mk_event s q (a + m') Hq Ham')
          by (apply event_eq_of_proj; rewrite !mk_event_proj; reflexivity).
        apply (prog_step s q (a + m') Hq Ham' HSam').
      * apply (hb_trans (desugar s) _ (mk_event s q (a + m') Hq Ham') _).
        -- apply (msg_step s Hwf r q (a + m') Hr Hq Ham' Hin).
        -- apply (prog_step s q (a + m') Hq Ham' HSam').
Qed.

Definition WindowConnected (s : Schedule) (a b : nat) : Prop :=
  forall p q, p < sch_nprocs s -> q < sch_nprocs s -> window_reach s a p (b - a) q.

Theorem window_connected_barrier :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
    forall a b, a < b -> b <= length (sch_frontiers s) ->
    WindowConnected s a b ->
    forall x y : ep_carrier (exec_of_schedule s),
      snd (proj1_sig x) < a -> b <= snd (proj1_sig y) ->
      ep_order (exec_of_schedule s) x y.
Proof.
  intros s Hwf Hnp a b Hab Hblen HWC x y Hxa Hyb.
  pose proof (proj2_sig x) as Hvx. pose proof (proj2_sig y) as Hvy.
  unfold Ensembles.In, ValidSet, Valid in Hvx, Hvy.
  destruct Hvx as [Hpx _]. destruct Hvy as [Hqy _].
  assert (Hpx' : fst (proj1_sig x) < sch_nprocs s) by (rewrite <- nprocs_desugar; exact Hpx).
  assert (Hqy' : fst (proj1_sig y) < sch_nprocs s) by (rewrite <- nprocs_desugar; exact Hqy).
  assert (Hiy : snd (proj1_sig y) < length (sch_frontiers s)) by (apply (event_index_lt s y)).
  assert (Halen : a < length (sch_frontiers s)) by lia.
  assert (Hblen' : b < length (sch_frontiers s)) by lia.
  assert (Hixlen : snd (proj1_sig x) < length (sch_frontiers s)) by lia.
  assert (Hxe : x = mk_event s (fst (proj1_sig x)) (snd (proj1_sig x)) Hpx' Hixlen).
  { apply event_eq_of_proj. rewrite mk_event_proj. apply surjective_pairing. }
  assert (Hye : y = mk_event s (fst (proj1_sig y)) (snd (proj1_sig y)) Hqy' Hiy).
  { apply event_eq_of_proj. rewrite mk_event_proj. apply surjective_pairing. }
  rewrite Hxe, Hye.
  apply (hb_trans (desugar s) _ (mk_event s (fst (proj1_sig x)) a Hpx' Halen) _).
  { apply (prog_chain s (fst (proj1_sig x)) (snd (proj1_sig x)) a Hpx' Hixlen Halen). lia. }
  apply (hb_trans (desugar s) _ (mk_event s (fst (proj1_sig y)) b Hqy' Hblen') _).
  { assert (Hb2 : a + (b - a) < length (sch_frontiers s)) by lia.
    pose proof (window_reach_hb s Hwf (b - a) a (fst (proj1_sig x)) (fst (proj1_sig y))
                  Hpx' Hqy' Halen Hb2 (HWC (fst (proj1_sig x)) (fst (proj1_sig y)) Hpx' Hqy')) as Hwrh.
    replace (mk_event s (fst (proj1_sig y)) b Hqy' Hblen')
       with (mk_event s (fst (proj1_sig y)) (a + (b - a)) Hqy' Hb2)
      by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
    exact Hwrh. }
  apply (prog_chain s (fst (proj1_sig y)) b (snd (proj1_sig y)) Hqy' Hblen' Hiy). lia.
Qed.

(* Remark: ConnSync.StepConnected is the per-transition (window width ~1) special case;
   window_step here is exactly the stay/single-cross core of StepConnected's witness.
   window_connected_barrier lifts the >=2-hop reach to synchronize all processes across a
   wider window -- impossible for a single transition (<=4-process reach) when n > 4. *)

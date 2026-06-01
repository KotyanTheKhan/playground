# Thick (window) barrier Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development.

**Goal:** A window of frontiers `[a,b)` synchronizes all processes across it: `WindowConnected s a b ⟹` every event before index `a` precedes every event at/after `b`, for arbitrary `n`.

**Architecture:** `execution/WindowSync.v` — `window_step`/`window_reach`/`WindowConnected`, a program-order chain lemma, the reach→hb lift, and the main `window_connected_barrier`. `execution/WindowSyncExamples.v` — a concrete gather/scatter (or `s_demo`) witness. Reuses `ConnSync` (`mk_event`, `prog_step`, `msg_step`, `event_eq_of_proj`, `mk_event_proj`).

**Tech Stack:** Rocq 9.1; `ConnSync`, `Edges.hb_trans`, `Schedule`, `ScheduleWf`. Builds via the wrapper.

---

## Task WB0: Scaffold
**Files:** create `execution/WindowSync.v`, `execution/WindowSyncExamples.v`; modify `execution/dune`, `_CoqProject`.
- [ ] **Step 1: `execution/WindowSync.v`**
```coq
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
```
- [ ] **Step 2: `execution/WindowSyncExamples.v`**
```coq
(* window-barrier example: a gather/scatter window synchronizes all processes (test-only). *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape ConnSync WindowSync.
Import ListNotations.
```
- [ ] **Step 3/4:** add `WindowSync`, `WindowSyncExamples` to `execution/dune` and `_CoqProject` (after `ConnSyncExamples`).
- [ ] **Step 5: build** `bash .claude/scripts/timed-build.sh 120 execution/WindowSyncExamples.vo 2` → EXIT=0.
- [ ] **Step 6: commit** `git add -A && git commit -m "chore(execution): scaffold WindowSync modules"`.

---

## Task WB1: definitions + chain + reach→hb (`WindowSync.v`)
Append.
```coq
Definition window_step (s : Schedule) (k p q : nat) : Prop :=
  p = q \/ List.In (p, q) (nth k (sch_frontiers s) []).

Fixpoint window_reach (s : Schedule) (a p m q : nat) : Prop :=
  match m with
  | 0 => p = q
  | S m' => exists r, window_reach s a p m' r /\ window_step s (a + m') r q
  end.

(* program-order chain over a difference d (avoids dependent-proof matching) *)
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
  assert (Hk' : i + (k - i) < length (sch_frontiers s)) by (replace (i + (k - i)) with k by lia; exact Hk).
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
    apply (hb_trans (desugar s) _ (mk_event s r (a + m') Hr Ham') _).
    + apply (IH a p r Hp Hr Ha Ham' Hreach).
    + (* (r, a+m') -> (q, a + S m') *)
      replace (mk_event s q (a + S m') Hq Hb) with (mk_event s q (S (a + m')) Hq HSam')
        by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
      destruct Hstep as [Heq | Hin].
      * subst r. apply (prog_step s q (a + m') Hq Ham' HSam').
      * apply (hb_trans (desugar s) _ (mk_event s q (a + m') Hq Ham') _).
        -- apply (msg_step s Hwf r q (a + m') Hr Hq Ham' Hin).
        -- apply (prog_step s q (a + m') Hq Ham' HSam').
Qed.
```
NOTES: `mk_event_proj : proj1_sig (mk_event s p k Hp Hk) = (p, k)`. The `replace … by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia)` discharges index-arithmetic + proof-irrelevance (`f_equal` splits `(p,a)=(p,b)` into `p=p` (auto) and `a=b` (lia); if `f_equal` leaves `p=p`, add `; try reflexivity`). `apply rt_refl` proves `ep_order … x x` (= `hb (desugar s) x x`); if it doesn't unify, `unfold ep_order, exec_of_schedule, exec_of; apply rt_refl` or `apply poset_refl`. The `hb_trans (desugar s)` calls rely on `ep_order (exec_of_schedule s) = hb (desugar s)` definitionally (as in ConnSync — worked there verbatim).
- [ ] **Build** `bash .claude/scripts/timed-build.sh 300 execution/WindowSync.vo 2` → EXIT=0.
- [ ] **Commit** `git add execution/WindowSync.v && git commit -m "feat(execution): window_reach + program-chain + reach->hb lift"`.

---

## Task WB2: WindowConnected + main theorem (`WindowSync.v`)
Append.
```coq
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
  set (px := fst (proj1_sig x)). set (py := fst (proj1_sig y)).
  set (ix := snd (proj1_sig x)). set (iy := snd (proj1_sig y)).
  assert (Hpx' : px < sch_nprocs s) by (unfold px; rewrite <- nprocs_desugar; exact Hpx).
  assert (Hqy' : py < sch_nprocs s) by (unfold py; rewrite <- nprocs_desugar; exact Hqy).
  assert (Hiy : iy < length (sch_frontiers s)) by (apply (event_index_lt s y)).
  assert (Halen : a < length (sch_frontiers s)) by lia.
  assert (Hblen' : b < length (sch_frontiers s)) by lia.
  assert (Hixlen : ix < length (sch_frontiers s)) by lia.
  (* canonicalize x, y *)
  assert (Hxe : x = mk_event s px ix Hpx' Hixlen).
  { apply event_eq_of_proj. rewrite mk_event_proj. unfold px, ix. symmetry. apply surjective_pairing. }
  assert (Hye : y = mk_event s py iy Hqy' Hiy).
  { apply event_eq_of_proj. rewrite mk_event_proj. unfold py, iy. symmetry. apply surjective_pairing. }
  rewrite Hxe, Hye.
  (* leg 1: (px, ix) -> (px, a) *)
  apply (hb_trans (desugar s) _ (mk_event s px a Hpx' Halen) _).
  { apply (prog_chain s px ix a Hpx' Hixlen Halen). unfold ix in *. lia. }
  (* leg 2: (px, a) -> (py, b) via window_reach *)
  assert (Hbeq : a + (b - a) = b) by lia.
  apply (hb_trans (desugar s) _ (mk_event s py b Hqy' Hblen') _).
  { (* window_reach_hb needs the target index a + (b-a); rewrite to b *)
    pose proof (window_reach_hb s Hwf (b - a) a px py Hpx' Hqy' Halen) as Hwrh.
    assert (Hb2 : a + (b - a) < length (sch_frontiers s)) by lia.
    specialize (Hwrh Hb2 (HWC px py Hpx' Hqy')).
    replace (mk_event s py b Hqy' Hblen') with (mk_event s py (a + (b - a)) Hqy' Hb2)
      by (apply event_eq_of_proj; rewrite !mk_event_proj; f_equal; lia).
    exact Hwrh. }
  (* leg 3: (py, b) -> (py, iy) *)
  apply (prog_chain s py b iy Hqy' Hblen' Hiy). unfold iy in *. lia.
Qed.
```
NOTES: the three `lia`s for the legs use `Hxa : ix < a`, `Hbeq`, `Hyb : b <= iy`. If `unfold ix in *` / `unfold iy in *` causes trouble, the hypotheses `Hxa`/`Hyb` are already about `snd (proj1_sig x)`/`snd (proj1_sig y)` = `ix`/`iy` after `set`; `lia` should close `ix <= a`/`b <= iy` directly (drop the `unfold` if it errors). `surjective_pairing : p = (fst p, snd p)` — the `symmetry` turns `(fst …, snd …) = proj1_sig` into the needed direction; if the orientation is already right, drop `symmetry` (as happened in ConnSync's CS3).

Also add a short remark relating to `ConnSync` (no proof obligation needed beyond a comment):
```coq
(* Remark: ConnSync.StepConnected is the per-transition (window width ~1) special case;
   window_step here is exactly the stay/single-cross core of StepConnected's witness.
   window_connected_barrier lifts the >=2-hop reach to synchronize all processes across a
   wider window — impossible for a single transition (<=4-process reach) when n > 4. *)
```
- [ ] **Build** `bash .claude/scripts/timed-build.sh 300 execution/WindowSync.vo 2` → EXIT=0.
- [ ] **Commit** `git add execution/WindowSync.v && git commit -m "feat(execution): window_connected_barrier (thick barrier, arbitrary n)"`.

---

## Task WB3: example + wiring + audit
**Files:** `execution/WindowSyncExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.
- [ ] **Step 1: a concrete window witness** (append). Target a 3-process gather/scatter window so it demonstrably exceeds the single-transition ≤2-pair reach. If the all-pairs `window_reach` proof is fiddly, FALL BACK to `s_demo` window `[0,2)`.
```coq
(* gather to coordinator 0 then scatter: frontiers 0,1 gather (1->0, 2->0); 2,3 scatter (0->1, 0->2) *)
Definition s_gs : Schedule :=
  {| sch_nprocs := 3; sch_frontiers := [ [(1,0)] ; [(2,0)] ; [(0,1)] ; [(0,2)] ] |}.

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
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; apply wf_frontier_pair; lia.
Qed.

(* every ordered pair p,q in {0,1,2} reaches across window [0,4): p ->* 0 (gather) ->* q (scatter) *)
Lemma window_connected_s_gs : WindowConnected s_gs 0 4.
Proof.
  unfold WindowConnected, s_gs. simpl. intros p q Hp Hq.
  (* b - a = 4; window_reach s 0 p 4 q : choose a path through coordinator 0.
     window_step at level k: stay (r=r) or cross In (r,r') (nth k frontiers).
     Build the explicit 4-step witness for each (p,q). *)
  (* p in {0,1,2}, q in {0,1,2} *)
  assert (p = 0 \/ p = 1 \/ p = 2) as Hp3 by lia.
  assert (q = 0 \/ q = 1 \/ q = 2) as Hq3 by lia.
  (* unfold window_reach to a 4-fold existential and supply intermediates.
     For (p,q): levels 0,1 bring p to 0 (cross at level p-1 if p>0, else stay);
     levels 2,3 bring 0 to q (cross at level q+1 if q>0, else stay). *)
  destruct Hp3 as [->|[->|->]]; destruct Hq3 as [->|[->|->]];
    simpl; unfold window_step; simpl.
  (* 9 goals: each is exists r3, (exists r2, (exists r1, (exists r0, r0=0/start) /\ step) /\ step) /\ step.
     Provide the coordinator-routing intermediates explicitly with eexists / exists. *)
  all: repeat (eexists; split); try (left; reflexivity); try (right; left; reflexivity).
Qed.

Example s_gs_window_barrier :
  forall x y : ep_carrier (exec_of_schedule s_gs),
    snd (proj1_sig x) < 1 -> 4 <= snd (proj1_sig y) ->
    ep_order (exec_of_schedule s_gs) x y.
Proof.
  apply (window_connected_barrier s_gs wf_s_gs).
  - vm_compute. lia.
  - lia.
  - vm_compute. lia.
  - exact window_connected_s_gs.
Qed.
```
NOTES on `window_connected_s_gs`: this is the crux of the example. `window_reach s_gs 0 p 4 q` unfolds (by `simpl`) to a 4-nested existential `exists r, (exists r', (exists r'', (exists r''', p = r''' /\ window_step 0 r''' r'') /\ window_step 1 r'' r') /\ window_step 2 r' r) /\ window_step 3 r q` (check the exact nesting/`a+m'` levels: levels are `0+0=0,0+1=1,0+2=2,0+3=3`). For each `(p,q)` supply the route through `0`: e.g. `(1,2)`: `1 →[lvl0 cross (1,0)] 0 →[lvl1 stay] 0 →[lvl2 stay] 0 →[lvl3 cross (0,2)] 2`. The `repeat (eexists; split)` + `left`/`right` blast may not discharge cleanly — if so, prove the 9 cases EXPLICITLY: `exists <r3>, <r2>, <r1>; simpl; repeat split; [ reflexivity | (left;reflexivity) or (right;left;reflexivity) | … ]`, choosing intermediates `0` for the coordinator legs. Membership `In (1,0) (nth 0 …)` = `In (1,0) [(1,0)]` = `right? no: left; reflexivity` (it's the head). If `simpl`/`nth` doesn't reduce, use `cbn`. Verify each of the 9 routes. If this overruns, replace `s_gs` with `s_demo` (`{2; [[(0,1)];[(1,0)]]}`) and prove `WindowConnected s_demo 0 2` (4 pairs) + the `[0,2)` barrier — still a genuine instantiation, just width-2/2-proc.
- [ ] **Step 2: build** `bash .claude/scripts/timed-build.sh 240 execution/WindowSyncExamples.vo 2` → EXIT=0.
- [ ] **Step 3: export** append `WindowSync` to `execution/Execution.v`'s `Require Export` list.
- [ ] **Step 4: whole-project** `bash .claude/scripts/timed-build.sh 1800 @all 4` → EXIT=0.
- [ ] **Step 5: audit** scratch `execution/WindowSyncAudit.v` (`From Execution Require Import WindowSync. Print Assumptions window_connected_barrier.`), register, build, capture (expected standard classical/proof-irrelevance axioms; no `admit`), then REMOVE + revert registration.
- [ ] **Step 6: INDEX** add a `#### execution/WindowSync.v — thick (window) barrier` subsection: `window_step`/`window_reach`/`WindowConnected`, `prog_chain`, `window_reach_hb`, `window_connected_barrier`; **record the consecutive-cut impossibility** (a single transition reaches ≤4 processes, so `FullySynchronizing` is unattainable for `n>4` with matching frontiers; a window of `b−a` frontiers lifts the cap).
- [ ] **Step 7: commit** `git add execution/WindowSyncExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): window-barrier example + export + INDEX (thick barrier, arbitrary n)"`.

---

## Self-Review (vs the spec)
- **Coverage:** defs + chain + reach→hb (WB1); `WindowConnected` + main theorem + ConnSync remark (WB2); example/wiring/audit incl. impossibility note (WB3). Mapped.
- **Reuse:** `mk_event`/`prog_step`/`msg_step`/`event_eq_of_proj`/`mk_event_proj` from `ConnSync`; `event_index_lt`/`nprocs_desugar`; `wf_frontier`/`nth_In` from `ScheduleWf`.
- **Name consistency:** `window_step`/`window_reach`/`WindowConnected`/`prog_chain_aux`/`prog_chain`/`window_reach_hb`/`window_connected_barrier` across WB1–WB3.
- **Honest scope:** impossibility documented (prose, not a universal Coq proof — out of scope); no dimension payoff attempted.

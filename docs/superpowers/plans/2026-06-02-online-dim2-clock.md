# Online dim-2 clock Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A computable timestamp `stamp : event → (nat³ × nat³)` whose
product-of-lexicographic order equals the barrier order `blo`, proven for any N —
the soundness half of a 2-coordinate logical clock.

**Architecture:** One generic theorem `stamp_iff` over an abstract poset with
`lay`/`comp`/`step` fields + a bound `B`, then a barrier instance `blo_iff_stamp`
discharging its 5 hypotheses via the existing `DisjointChainsDim` lemmas, then a
readable `stamp` wrapper and three examples (incl. an abstract length-3 chain).

**Tech Stack:** Coq/Rocq 9.1, Stdlib `Arith`/`Lia`, the `Execution` library
(`BarrierExecDim`, `DisjointChainsDim`, `ScheduleWf`). Builds go through
`bash .claude/scripts/timed-build.sh <secs> <target> 2`.

**Spec:** `docs/superpowers/specs/2026-06-02-online-dim2-clock-design.md`.

**Branch:** `online-clock` (already created off `dev`).

**Signature note (refinement of spec):** `le_lex3` takes **six scalar args**, not
two triples — strictly easier to prove with `lia`, no tuple-destructuring. The
spec explicitly left exact signatures to the plan. The `stamp` wrapper still
returns tuples for readable `vm_compute`.

---

### Task 1: Generic core — `le_lex3`, `le_prod`, `stamp_iff`

**Files:**
- Create: `execution/OnlineClock.v`

- [ ] **Step 1: Write the file header, the order definitions, and the generic theorem (full proof)**

```coq
(* A computable 2-coordinate timestamp whose product order equals blo. *)
From Stdlib Require Import Arith Lia.
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
```

- [ ] **Step 2: Build to verify it compiles (and the generic theorem closes)**

Run: `bash .claude/scripts/timed-build.sh 180 execution/OnlineClock.vo 2`
Expected: exit 0, `✅ Build successful: execution/OnlineClock.vo`.
(If `lt_eq_lt_dec` is not in scope, add `From Stdlib Require Import Compare_dec.`)

- [ ] **Step 3: Commit**

```bash
git add execution/OnlineClock.v
git commit -m "feat(online-clock): generic stamp_iff (R <-> product of two lex orders)"
```

---

### Task 2: Barrier fields + the bound lemma `fb_comp_lt_nprocs`

**Files:**
- Modify: `execution/OnlineClock.v`

- [ ] **Step 1: Add imports and the three field definitions + the bound lemma**

Append to `execution/OnlineClock.v` (after Task 1 content):

```coq
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
  set (px := fst (proj1_sig x)). set (k := snd (proj1_sig x)).
  assert (Hpx : px < sch_nprocs s) by (unfold px; apply event_pid_lt).
  assert (Hk  : k < length (sch_frontiers s)) by (unfold k; apply event_index_lt).
  rewrite (block_op_for s x).            (* op_at = Some (op_for (nth k ..) px k) *)
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
```

Notes for the implementer:
- `block_op_for`, `event_pid_lt`, `event_index_lt`, `op_for_tag`, `op_for_recv_iff`,
  `wf_frontier` all live in `DisjointChainsDim.v` / `ScheduleWf.v` / `SyncShape.v`.
- `wf_frontier n fr` unfolds to `(forall a b, In (a,b) fr -> a < n /\ b < n) /\ NoDup (endpoints fr)`
  (see `wf_s_bar5` in `BarrierExecDimExamples.v`); `Hrange src px Hin : src < n /\ px < n`.
  If the exact shape differs, `unfold wf_frontier in Hfr` and read off the range conjunct.

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/OnlineClock.vo 2`
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add execution/OnlineClock.v
git commit -m "feat(online-clock): clk_lay/comp/step fields + fb_comp_lt_nprocs bound"
```

---

### Task 3: Within-layer helpers — `blo_same_layer`, `hb_layer_step`

**Files:**
- Modify: `execution/OnlineClock.v`

- [ ] **Step 1: Add the two helper lemmas**

```coq
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
  set (px := fst (proj1_sig x)) in *. set (py := fst (proj1_sig y)) in *.
  set (k := snd (proj1_sig x)) in *.
  assert (Hpx : px < sch_nprocs s) by (unfold px; apply event_pid_lt).
  assert (Hpy : py < sch_nprocs s) by (unfold py; apply event_pid_lt).
  assert (Hk  : k < length (sch_frontiers s)) by (unfold k; apply event_index_lt).
  assert (Hfr : wf_frontier (sch_nprocs s) (nth k (sch_frontiers s) []))
    by (apply Hwf; apply nth_In; exact Hk).
  pose proof (proj2 (op_for_send_iff (sch_nprocs s) _ px py k Hfr) Hin) as Hsend.
  pose proof (proj2 (op_for_recv_iff (sch_nprocs s) _ px py k Hfr) Hin) as Hrecv.
  (* clk_step reads op_at = op_for; rewrite both *)
  unfold clk_step. fold px k. rewrite (block_op_for s x). fold px k. rewrite Hsend.
  assert (Hky : snd (proj1_sig y) = k) by (symmetry; exact Hl).
  split; [reflexivity|].
  rewrite (block_op_for s y).
  (* op_for at (py, k) = Recv px k  by Hrecv (after aligning index to k) *)
  replace (snd (proj1_sig y)) with k by (symmetry; exact Hl). rewrite Hrecv. reflexivity.
Qed.
```

Notes: `op_for_send_iff`/`op_for_recv_iff` are in `ScheduleWf.v` and already used by
`fb_comp_eq_of_hb` (`DisjointChainsDim.v:282-283`). The `In (px,py)` from
`hb_same_index_msg` is `In (fst x, fst y) (nth (snd x) …)`; align `snd x = k`. If
`fold`/`replace` plumbing fights you, mirror the exact rewriting chain in
`fb_comp_eq_of_hb` (same lemmas, same shape) — it sets `px py k`, derives
`Hpairx`/`Hpairy`, and rewrites `op_at_desugar`.

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/OnlineClock.vo 2`
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add execution/OnlineClock.v
git commit -m "feat(online-clock): blo_same_layer + hb_layer_step helpers"
```

---

### Task 4: The rank axiom for `blo` — `blo_rank`

**Files:**
- Modify: `execution/OnlineClock.v`

- [ ] **Step 1: Add the rank lemma (hypothesis 4 of stamp_iff, for blo)**

```coq
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
    intro Hs. apply (blo_same_layer s x y Hl).
    (* comparability from same layer + same fb_comp *)
    assert (Hidx : snd (proj1_sig x) = snd (proj1_sig y)) by exact Hl.
    assert (Hcc  : fb_comp s (proj1_sig x) = fb_comp s (proj1_sig y)) by exact Hc.
    destruct (hb_or_of_fb_comp_eq s Hwf x y Hidx Hcc) as [Hxy | Hyx].
    + exact Hxy.
    + (* ep_order y x : if y<>x then step y=0, step x=1, contradicting step x <= step y *)
      destruct (event_eq_dec (desugar s) y x) as [He | Hne].
      * subst x. apply poset_refl.
      * destruct (hb_layer_step s Hwf y x (eq_sym Hl) Hyx Hne) as [Hsy Hsx].
        rewrite Hsx, Hsy in Hs. lia.
Qed.
```

Notes: `event_eq_dec`, `hb_or_of_fb_comp_eq` are in `DisjointChainsDim.v`/`Poset.v`.
`clk_comp s x = fb_comp s (proj1_sig x)` is definitional (so `Hc`/`Hcc` align by
`exact` or `unfold clk_comp in Hc`). `poset_refl` from the `blo`/`hb` IsPoset
instance (the goal after `blo_same_layer` is `ep_order … x x`).

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 300 execution/OnlineClock.vo 2`
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add execution/OnlineClock.v
git commit -m "feat(online-clock): blo_rank (within-layer step ordering = hb)"
```

---

### Task 5: The instance theorem `blo_iff_stamp` + `stamp` wrapper

**Files:**
- Modify: `execution/OnlineClock.v`

- [ ] **Step 1: Add the instantiation and the readable wrapper**

```coq
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
```

Notes: hypothesis 3 needs `fb_comp_eq_of_hb : … snd-eq → ep_order → fb_comp =
fb_comp`; its first arg is `snd x = snd y`, which is exactly `Hl : clk_lay x =
clk_lay y` (definitional). `blo_same_layer` turns the `blo` hyp into `ep_order`.

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 300 execution/OnlineClock.vo 2`
Expected: exit 0.

- [ ] **Step 3: `Print Assumptions` sanity check (no admits)**

Add temporarily at end of file, build, then read output, then remove:
```coq
Print Assumptions blo_iff_stamp.
```
Run: `bash .claude/scripts/timed-build.sh 300 execution/OnlineClock.vo 2`
Expected: only standard axioms (`classic`, `proof_irrelevance`, maybe
`Extensionality_Ensembles`/choice) — **no `admit`/`Admitted`**. Remove the
`Print Assumptions` line afterward.

- [ ] **Step 4: Commit**

```bash
git add execution/OnlineClock.v
git commit -m "feat(online-clock): blo_iff_stamp (blo = product order, any N) + stamp wrapper"
```

---

### Task 6: Wire `OnlineClock` into the build

**Files:**
- Modify: `execution/dune` (add `OnlineClock` to `(modules …)`)
- Modify: `_CoqProject` (add `execution/OnlineClock.v`)
- Modify: `execution/Execution.v` (add `OnlineClock` to the `Require Export`)

- [ ] **Step 1: Add module to `execution/dune`**

In the `(modules …)` list, after `BarrierExecDimExamples` add a new line `  OnlineClock`
(keep it inside the closing `))`). Result tail:
```
  BarrierExecDim
  BarrierExecDimExamples
  OnlineClock))
```

- [ ] **Step 2: Add file to `_CoqProject`**

After the line `execution/BarrierExecDimExamples.v` add:
```
execution/OnlineClock.v
```

- [ ] **Step 3: Export from `execution/Execution.v`**

Append ` OnlineClock` to the end of the `From Execution Require Export … BarrierExecDim.`
line (before the final `.`).

- [ ] **Step 4: Build the public surface**

Run: `bash .claude/scripts/timed-build.sh 300 execution/Execution.vo 2`
Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add execution/dune _CoqProject execution/Execution.v
git commit -m "build(online-clock): register OnlineClock in dune/_CoqProject/Execution"
```

---

### Task 7: Examples — `OnlineClockExamples.v`

**Files:**
- Create: `execution/OnlineClockExamples.v`

- [ ] **Step 1: Example 1 — the N=5 barrier (`s_bar5`)**

```coq
(* Online dim-2 clock: worked instances (test-only). *)
From Stdlib Require Import List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim
                             BarrierExecDimExamples OnlineClock.
Import ListNotations.

(* s_bar5, wf_s_bar5, bar5_e0, bar5_e1 come from BarrierExecDimExamples *)

(* the iff specialized to s_bar5 *)
Lemma bar5_blo_iff_stamp :
  forall x y,
    blo s_bar5 x y <->
    le_prod (sch_nprocs s_bar5 - 1)
      (clk_lay s_bar5 x)(clk_comp s_bar5 x)(clk_step s_bar5 x)
      (clk_lay s_bar5 y)(clk_comp s_bar5 y)(clk_step s_bar5 y).
Proof. apply (blo_iff_stamp s_bar5 wf_s_bar5). simpl. lia. Qed.

(* two distinct layer-0 events get incomparable stamps (mirrors bar5_incomp) *)
Example bar5_stamp_incomp :
  ~ (le_prod (sch_nprocs s_bar5 - 1)
       (clk_lay s_bar5 bar5_e0)(clk_comp s_bar5 bar5_e0)(clk_step s_bar5 bar5_e0)
       (clk_lay s_bar5 bar5_e1)(clk_comp s_bar5 bar5_e1)(clk_step s_bar5 bar5_e1))
  /\ ~ (le_prod (sch_nprocs s_bar5 - 1)
       (clk_lay s_bar5 bar5_e1)(clk_comp s_bar5 bar5_e1)(clk_step s_bar5 bar5_e1)
       (clk_lay s_bar5 bar5_e0)(clk_comp s_bar5 bar5_e0)(clk_step s_bar5 bar5_e0)).
Proof.
  split; intro H; [ apply (proj1 (bar5_blo_iff_stamp bar5_e0 bar5_e1)) in H
                  | apply (proj1 (bar5_blo_iff_stamp bar5_e1 bar5_e0)) in H ];
  revert H; [ generalize (proj1 bar5_incomp) | generalize (fun h => proj1 bar5_incomp (or_intror h)) ];
  (* bar5_incomp : Incomparable (blo s_bar5) bar5_e0 bar5_e1 *)
  unfold Incomparable in bar5_incomp; tauto.
Qed.
```

Implementer note: the cleanest discharge is `pose proof bar5_incomp as Hinc;
unfold Incomparable in Hinc` (it is `~ (blo .. \/ blo ..)`), then from each
`le_prod` recover `blo` via `bar5_blo_iff_stamp` and close with `tauto`. Adjust
the script above to that shape if the `generalize` form is awkward.

- [ ] **Step 2: Build, then commit**

Run: `bash .claude/scripts/timed-build.sh 240 execution/OnlineClockExamples.vo 2`
(after Step 4 wiring; for now build will fail on missing module — see Step 4).
Defer the build to Step 4; write Steps 1–3 first.

- [ ] **Step 3: Example 2 — a messaged 3-process barrier, with a literal `vm_compute`**

```coq
Definition s_msg3 : Schedule := {| sch_nprocs := 3; sch_frontiers := [ [(0,1)] ] |}.

Lemma wf_s_msg3 : wf_schedule s_msg3.
Proof.
  unfold wf_schedule, s_msg3. simpl. intros fr [<- | []].
  unfold wf_frontier, endpoints. split.
  - intros a b [E | []]; injection E as <- <-; lia.
  - simpl. repeat constructor; simpl; intuition discriminate.
Qed.

(* events (0,0) sender [step 0], (1,0) receiver [step 1], (2,0) isolated *)
Lemma v00 : Ensembles.In _ (ValidSet (desugar s_msg3)) (0,0). Proof. vm_compute. split; lia. Qed.
Lemma v10 : Ensembles.In _ (ValidSet (desugar s_msg3)) (1,0). Proof. vm_compute. split; lia. Qed.
Lemma v20 : Ensembles.In _ (ValidSet (desugar s_msg3)) (2,0). Proof. vm_compute. split; lia. Qed.
Definition e00 : ep_carrier (exec_of_schedule s_msg3) := exist _ (0,0) v00.
Definition e10 : ep_carrier (exec_of_schedule s_msg3) := exist _ (1,0) v10.
Definition e20 : ep_carrier (exec_of_schedule s_msg3) := exist _ (2,0) v20.

(* literal timestamps: sender (0,0,0)/(0,2,0); receiver (0,0,1)/(0,2,1); isolated (0,2,0)/(0,0,0) *)
Example stamp_e00 : stamp s_msg3 e00 = ((0,0,0),(0,2,0)). Proof. vm_compute. reflexivity. Qed.
Example stamp_e10 : stamp s_msg3 e10 = ((0,0,1),(0,2,1)). Proof. vm_compute. reflexivity. Qed.
Example stamp_e20 : stamp s_msg3 e20 = ((0,2,0),(0,0,0)). Proof. vm_compute. reflexivity. Qed.
```

Implementer note: the exact triple values depend on `fb_comp`/`clk_step`
evaluating under `vm_compute`; if a value differs, **read the computed value from
the error and use it** — the point is that `stamp` is a closed computable
function, not the specific constant. Then add one ordering check, e.g.
`Example msg3_sender_below_receiver : le_prod 2 0 0 0 0 0 1.` proved by
`vm_compute; lia` or `unfold le_prod, le_lex3; lia`, and one incomparability
`Example msg3_isolated_incomp : ~ le_prod 2 0 0 0 0 2 0 /\ ~ le_prod 2 0 2 0 0 0 0.`
proved by `unfold le_prod, le_lex3; lia`. (Values 0/2 = comp of sender(0) vs
isolated(2); `B = nprocs-1 = 2`.)

- [ ] **Step 4: Wire `OnlineClockExamples` into the build (dune + _CoqProject)**

- `execution/dune`: add `  OnlineClockExamples` after `  OnlineClock` inside `(modules …)`.
- `_CoqProject`: add `execution/OnlineClockExamples.v` after `execution/OnlineClock.v`.
- (Not exported from `Execution.v` — it is test-only, like the other `*Examples`.)

Run: `bash .claude/scripts/timed-build.sh 300 execution/OnlineClockExamples.vo 2`
Expected: exit 0.

- [ ] **Step 5: Example 3 — abstract length-3 chain (generic `stamp_iff`, step ∈ {0,1,2})**

```coq
(* A 4-point poset in ONE layer: a 3-chain u<v<w in component 0, isolated z in component 1.
   Exercises stamp_iff with step ranks 0,1,2 — beyond any frontier Schedule. *)
Inductive P4 := u | v | w | z.
Definition R4 (a b : P4) : Prop :=
  match a, b with
  | u,u|v,v|w,w|z,z => True
  | u,v|u,w|v,w => True
  | _,_ => False
  end.
Definition lay4 (_ : P4) := 0.
Definition comp4 (a : P4) := match a with z => 1 | _ => 0 end.
Definition step4 (a : P4) := match a with u => 0 | v => 1 | w => 2 | z => 0 end.

#[local] Instance R4_IsPoset : IsPoset P4 R4.
Proof. constructor; [intros [] | intros [] [] | intros [] [] []]; cbv; tauto. Qed.

Example chain3_stamp_iff :
  forall a b, R4 a b <-> le_prod 1 (lay4 a)(comp4 a)(step4 a)(lay4 b)(comp4 b)(step4 b).
Proof.
  apply (stamp_iff R4 lay4 comp4 step4 1).
  - intros [] []; cbv; lia.                 (* barrier (lay all equal: vacuous) *)
  - intros [] []; cbv; lia.                 (* resp-lay *)
  - intros [] []; cbv; intuition.           (* resp-comp *)
  - intros [] []; cbv; intuition lia.       (* rank: R <-> step<=step in component 0 *)
  - intros []; cbv; lia.                     (* bound: comp <= 1 *)
Qed.
```

Implementer note: the five obligations are finite case-splits on `P4`; `cbv`
then `lia`/`tauto`/`intuition` should close each. If `intuition lia` is slow,
enumerate the 16 `a,b` cases with `destruct a, b` first. This is the example that
justifies the *general* rank field.

- [ ] **Step 6: Build the examples file**

Run: `bash .claude/scripts/timed-build.sh 300 execution/OnlineClockExamples.vo 2`
Expected: exit 0.

- [ ] **Step 7: Commit**

```bash
git add execution/OnlineClockExamples.v execution/dune _CoqProject
git commit -m "test(online-clock): s_bar5, messaged-3 (literal stamps), abstract 3-chain"
```

---

### Task 8: Docs + whole-project green

**Files:**
- Modify: `docs/INDEX.md`
- Modify: `execution/DIM2_CLOCK.md`

- [ ] **Step 1: Add an INDEX.md subsection**

Under the execution dimension entries (after the `BarrierExecDim.v` subsection,
before the `TransformB.v` subsection), add:

```markdown
#### `execution/OnlineClock.v` — computable 2-coordinate clock (`blo` = product order)

Turns the abstract `L1`/`L2` realizer into a concrete computable timestamp. A
generic theorem `stamp_iff` (any poset with integer `lay`/`comp`/`step` + bound
`B` satisfying barrier/resp-lay/resp-comp/rank/bound ⟹ `R x y ↔ stamp x ≤_prod
stamp y`, the product of two lexicographic orders, comparison on emitted integers
only), instantiated for `blo` as `blo_iff_stamp` (**any N**). The "online dim-2
clock" soundness half; online *locality* is argued in `DIM2_CLOCK.md`, not Coq.

| Name | Meaning |
|------|---------|
| `le_lex3` / `le_prod` | lexicographic ≤ on a nat triple (6-scalar form); product of the two lex orders (`T2` uses `B - comp`) |
| `stamp_iff` | generic: 5 structural hypotheses ⟹ `R x y ↔ le_prod …` (no finiteness; integer-only test) |
| `clk_lay` / `clk_comp` / `clk_step` | barrier index `snd`; `fb_comp`; `Recv?1:0` |
| `fb_comp_lt_nprocs` | `clk_comp < sch_nprocs` (the bound `B = nprocs-1`) |
| `blo_same_layer` / `hb_layer_step` / `blo_rank` | within-layer reductions discharging the rank hypothesis |
| `blo_iff_stamp` | `wf_schedule` ⟹ `blo s x y ↔ le_prod (nprocs-1) …`, for any process count |
| `stamp` | readable `(nat³ × nat³)` timestamp for `vm_compute` |
```

- [ ] **Step 2: Update `execution/DIM2_CLOCK.md` §6**

Replace the "Online (the next research step)" paragraph's framing of the
characterization as open: the **characterization** `blo ⟺ stamp ≤` is now proven
(`OnlineClock.v`, `blo_iff_stamp`); what remains open is only the **online
locality / operational maintenance** proof. Add a row to the lemma-map table:
`| barrier order = computable product-of-lex clock (any N) | blo_iff_stamp (OnlineClock.v) |`.

- [ ] **Step 3: Whole-project build via the wrapper**

Run: `bash .claude/scripts/timed-build.sh 1800 @all 4`
Expected: exit 0 (whole project green, including the new files).

- [ ] **Step 4: Commit**

```bash
git add docs/INDEX.md execution/DIM2_CLOCK.md
git commit -m "docs(online-clock): INDEX subsection + DIM2_CLOCK characterization now proven"
```

---

## Self-Review

**Spec coverage:**
- Generic `stamp_iff` (5 hypotheses, integer-only) → Task 1. ✓
- `blo_iff_stamp` any N + `fb_comp_lt_nprocs` → Tasks 2–5. ✓
- `stamp` wrapper → Task 5. ✓
- Examples (`s_bar5`, messaged-3 with literal `vm_compute`, abstract 3-chain) → Task 7. ✓
- Wiring (dune/_CoqProject/Execution.v), INDEX, DIM2_CLOCK, whole-project green,
  `Print Assumptions`, zero admits → Tasks 6, 8 (+ Task 5 Step 3). ✓

**Type consistency:** `le_lex3`/`le_prod` use 6 scalar args everywhere; `clk_lay`/
`clk_comp`/`clk_step`/`stamp`/`blo_iff_stamp` names match across tasks; `clk_comp =
fb_comp ∘ proj1_sig` is the only definitional bridge and is used consistently in
the rank/resp-comp/bound discharges.

**Honest deviations from spec:** (1) `le_lex3` is 6-scalar, not triple-typed
(easier proofs; spec permitted pinning signatures here). (2) `0 < sch_nprocs s`
is kept as a hypothesis of `blo_iff_stamp` though likely removable — left in for
a clean `nprocs - 1` bound discharge.

**Risk notes for the executor:** the fiddliest proofs are `hb_layer_step` (Task 3)
and `blo_rank` (Task 4); both directly mirror existing lemmas in
`DisjointChainsDim.v` (`fb_comp_eq_of_hb`, `hb_or_of_fb_comp_eq`) — when tactic
plumbing fights, copy those lemmas' `set px py k` / `Hpairx`/`Hpairy` rewriting
chain. If a `vm_compute`'d stamp constant in Task 7 differs, use the value the
prover reports (the theorem, not the constant, is the deliverable).

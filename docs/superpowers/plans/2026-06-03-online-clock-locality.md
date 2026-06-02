# Online clock locality Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A schedule-blind `local_stamp (N p i : nat) (o : Op)` proven equal to the
global `stamp` for every valid event, restating the causality characterization
`blo ⟺ stamp ≤` in terms of purely local data — closing the "online" item.

**Architecture:** One new leaf file `execution/OnlineClockLocal.v` on top of
`OnlineClock.v`: the local function + its `local_obs` view, a near-definitional
correctness theorem (`local_stamp … = stamp`), a `stamp_le` bridge to the causality
corollary, and two `reflexivity` interface lemmas pinning the minimal cross-process
datum. Plus a test-only examples file.

**Tech Stack:** Coq/Rocq 9.1, Stdlib `Arith`, the `Execution` library
(`OnlineClock`, `DisjointChainsDim`, `BarrierExecDim`, `Op`). All builds via
`bash .claude/scripts/timed-build.sh <secs> <target> 2`.

**Spec:** `docs/superpowers/specs/2026-06-03-online-clock-locality-design.md`.
**Branch:** `online-maintenance` (already created off `dev`).

**Key facts the implementer needs (verified against source):**
- `Op` (in `execution/Op.v`): `Local | Send (tgt:nat) (tag:nat) | Recv (src:nat) (tag:nat)`.
- `clk_comp s x = fb_comp s (proj1_sig x)`, and `fb_comp s pi = match op_at (desugar_prog s) (fst pi) (snd pi) with Some (Recv src _) => src | _ => fst pi end` (`DisjointChainsDim.v:180`).
- `clk_step s x = match op_at (desugar_prog s) (fst (proj1_sig x)) (snd (proj1_sig x)) with Some (Recv _ _) => 1 | _ => 0 end` (`OnlineClock.v`).
- `clk_lay s x = snd (proj1_sig x)` (`OnlineClock.v`).
- `stamp s x = ((clk_lay s x, clk_comp s x, clk_step s x), (clk_lay s x, (sch_nprocs s - 1) - clk_comp s x, clk_step s x))` (`OnlineClock.v`).
- `block_op_for s x : op_at (desugar_prog s) (fst (proj1_sig x)) (snd (proj1_sig x)) = Some (op_for (nth (snd (proj1_sig x)) (sch_frontiers s) []) (fst (proj1_sig x)) (snd (proj1_sig x)))` (`DisjointChainsDim.v:225`).
- `le_prod B lx cx sx ly cy sy := le_lex3 lx cx sx ly cy sy /\ le_lex3 lx (B-cx) sx ly (B-cy) sy` (`OnlineClock.v`).
- `blo_iff_stamp s (Hwf:wf_schedule s) (Hnp:0<sch_nprocs s) x y : blo s x y <-> le_prod (sch_nprocs s - 1) (clk_lay s x)(clk_comp s x)(clk_step s x)(clk_lay s y)(clk_comp s y)(clk_step s y)` (`OnlineClock.v`).
- In `OnlineClockExamples.v`: `s_msg3 := {| sch_nprocs := 3; sch_frontiers := [ [(0,1)] ] |}`, `wf_s_msg3`, `msg3_pos : 0 < sch_nprocs s_msg3`, `e00`/`e10`/`e20` (events `(0,0)`/`(1,0)`/`(2,0)`), `msg3_blo_e00_e10 : blo s_msg3 e00 e10`.

---

### Task 1: `local_stamp`, `local_obs`, `local_stamp_correct` + register module

**Files:**
- Create: `execution/OnlineClockLocal.v`
- Modify: `execution/dune` (add `OnlineClockLocal` to `(modules …)`)
- Modify: `_CoqProject` (add `execution/OnlineClockLocal.v`)

- [ ] **Step 1: Create `execution/OnlineClockLocal.v`**

```coq
(* Online clock maintenance: the locality theorem. local_stamp is schedule-blind
   (s is not an argument) -- the signature IS the locality of the clock. We prove
   it reproduces the global stamp for every valid event. *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim OnlineClock.
Import ListNotations.

(* The clock computed from purely local data: N = system size, p = own pid,
   i = own local index, o = own op (a Recv carries the sender id). *)
Definition local_stamp (N p i : nat) (o : Op) : (nat * nat * nat) * (nat * nat * nat) :=
  let comp := match o with Recv src _ => src | _ => p end in
  let step := match o with Recv _ _ => 1 | _ => 0 end in
  ((i, comp, step), (i, (N - 1) - comp, step)).

(* What process p observes at its index-i event: its own op. *)
Definition local_obs (s : Schedule) (p i : nat) : Op :=
  op_for (nth i (sch_frontiers s) []) p i.

(* The schedule-blind local clock reproduces the global stamp at every valid event. *)
Theorem local_stamp_correct :
  forall s (x : ep_carrier (exec_of_schedule s)),
    local_stamp (sch_nprocs s) (fst (proj1_sig x)) (snd (proj1_sig x))
                (local_obs s (fst (proj1_sig x)) (snd (proj1_sig x)))
    = stamp s x.
Proof.
  intros s x.
  unfold stamp, local_stamp, clk_lay, clk_comp, clk_step, fb_comp, local_obs.
  rewrite (block_op_for s x).
  destruct (op_for (nth (snd (proj1_sig x)) (sch_frontiers s) [])
                   (fst (proj1_sig x)) (snd (proj1_sig x)));
    reflexivity.
Qed.
```

- [ ] **Step 2: Register the module**

In `execution/dune`, inside `(modules …)`, after the line `  OnlineClockExamples`
add a line `  OnlineClockLocal`. In `_CoqProject`, after the line
`execution/OnlineClockExamples.v` add `execution/OnlineClockLocal.v`.

(Note: `OnlineClockLocal` must come BEFORE `OnlineClockExamples` is NOT required —
dune orders by dependency automatically — but keep the lists tidy by appending.)

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/OnlineClockLocal.vo 2`
Expected: exit 0, `✅ Build successful: execution/OnlineClockLocal.vo`.

Likely fixes if `local_stamp_correct` doesn't close:
- If `rewrite (block_op_for s x)` reports "no subterm": the `op_at` occurrences may
  be hidden under the `fb_comp`/`clk_step` folds — make sure `unfold … fb_comp …`
  is in the `unfold` list (it is). If still stuck, `cbn` after the unfolds, or
  `rewrite block_op_for in *`.
- If `reflexivity` fails on a branch, `cbn` before `destruct`, or `destruct … as
  [|tgt tg|src tg]; cbn; reflexivity`. Do NOT change the theorem statement.

- [ ] **Step 4: Commit**

```bash
git add execution/OnlineClockLocal.v execution/dune _CoqProject
git commit -m "feat(online-maint): local_stamp + local_obs + local_stamp_correct (schedule-blind clock = stamp)"
```

---

### Task 2: `stamp_le`, `stamp_le_stamp`, `blo_iff_local_stamp`

**Files:**
- Modify: `execution/OnlineClockLocal.v` (append)

- [ ] **Step 1: Append the product order on stamp pairs, the bridge, and the corollary**

```coq
(* product of the two lex orders, on (triple, triple) stamp pairs *)
Definition stamp_le (st1 st2 : (nat * nat * nat) * (nat * nat * nat)) : Prop :=
  let '((a1,a2,a3),(b1,b2,b3)) := st1 in
  let '((c1,c2,c3),(d1,d2,d3)) := st2 in
  le_lex3 a1 a2 a3 c1 c2 c3 /\ le_lex3 b1 b2 b3 d1 d2 d3.

(* stamp_le on the offline stamp wrapper is exactly le_prod on the clk fields *)
Lemma stamp_le_stamp :
  forall s (x y : ep_carrier (exec_of_schedule s)),
    stamp_le (stamp s x) (stamp s y) <->
    le_prod (sch_nprocs s - 1)
      (clk_lay s x)(clk_comp s x)(clk_step s x)
      (clk_lay s y)(clk_comp s y)(clk_step s y).
Proof.
  intros s x y. unfold stamp_le, stamp, le_prod. cbn. tauto.
Qed.

(* The headline online clock: blo characterized purely via the schedule-blind local_stamp. *)
Corollary blo_iff_local_stamp :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
  forall x y : ep_carrier (exec_of_schedule s),
    blo s x y <->
    stamp_le
      (local_stamp (sch_nprocs s) (fst (proj1_sig x)) (snd (proj1_sig x))
                   (local_obs s (fst (proj1_sig x)) (snd (proj1_sig x))))
      (local_stamp (sch_nprocs s) (fst (proj1_sig y)) (snd (proj1_sig y))
                   (local_obs s (fst (proj1_sig y)) (snd (proj1_sig y)))).
Proof.
  intros s Hwf Hnp x y.
  rewrite (local_stamp_correct s x). rewrite (local_stamp_correct s y).
  rewrite stamp_le_stamp.
  exact (blo_iff_stamp s Hwf Hnp x y).
Qed.
```

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/OnlineClockLocal.vo 2`
Expected: exit 0.

Likely fixes:
- `stamp_le_stamp`: if `cbn; tauto` leaves a goal, the `let '((…)) :=` did not
  reduce — try `unfold stamp_le, stamp, le_prod; cbn beta iota; split; intros H; exact H`
  or `; split; trivial` (the two sides are definitionally equal, so `reflexivity`
  on the `<->` via `iff_refl`/`tauto` should close it). As a last resort
  `split; intro H; destruct H; split; assumption`.
- `blo_iff_local_stamp`: if `rewrite stamp_le_stamp` (a setoid rewrite under `<->`)
  fails, replace the last three lines with:
  `rewrite (local_stamp_correct s x), (local_stamp_correct s y);
   split; intro H; [ apply stamp_le_stamp; apply (blo_iff_stamp s Hwf Hnp x y); exact H
                   | apply (blo_iff_stamp s Hwf Hnp x y); apply stamp_le_stamp; exact H ].`
  Do NOT change the corollary statement.

- [ ] **Step 3: Commit**

```bash
git add execution/OnlineClockLocal.v
git commit -m "feat(online-maint): blo_iff_local_stamp (causality via the schedule-blind clock)"
```

---

### Task 3: interface lemmas + Print Assumptions + export

**Files:**
- Modify: `execution/OnlineClockLocal.v` (append)
- Modify: `execution/Execution.v` (add export)

- [ ] **Step 1: Append the two minimal-interface lemmas**

```coq
(* A Send/Local event contributes no cross-process clock datum (comp = own pid). *)
Lemma local_stamp_send_eq_local :
  forall N p i t tg, local_stamp N p i (Send t tg) = local_stamp N p i Local.
Proof. reflexivity. Qed.

(* A Recv uses only its sender id, never the tag: the only cross-process datum is src. *)
Lemma local_stamp_recv_tag_irrel :
  forall N p i src tg tg', local_stamp N p i (Recv src tg) = local_stamp N p i (Recv src tg').
Proof. reflexivity. Qed.
```

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 180 execution/OnlineClockLocal.vo 2`
Expected: exit 0. (If a `reflexivity` fails because `Send`/`Recv` arg order differs
from `Op`'s actual constructors, read `execution/Op.v` and match — but the statements
must remain "Send carries no clock info" / "tag irrelevant".)

- [ ] **Step 3: Print Assumptions check (no admits)**

Temporarily append at end of file:
```coq
Print Assumptions local_stamp_correct.
Print Assumptions blo_iff_local_stamp.
```
Run: `bash .claude/scripts/timed-build.sh 180 execution/OnlineClockLocal.vo 2`
Read the wrapper's output file. Expected: only standard axioms inherited from
`blo_iff_stamp` (`classic`, `proof_irrelevance`, `constructive_definite_description`,
`Extensionality_Ensembles`) — and `local_stamp_correct` should be axiom-FREE (it is
near-definitional). Confirm NO `admit`/`Admitted`. Then REMOVE both `Print
Assumptions` lines and rebuild to confirm still green.

- [ ] **Step 4: Export from `execution/Execution.v`**

Append ` OnlineClockLocal` to the end of the `From Execution Require Export …
OnlineClock.` line (before the final `.`). The tail becomes `… BarrierExecDim
OnlineClock OnlineClockLocal.`

- [ ] **Step 5: Build the public surface**

Run: `bash .claude/scripts/timed-build.sh 300 execution/Execution.vo 2`
Expected: exit 0.

- [ ] **Step 6: Commit**

```bash
git add execution/OnlineClockLocal.v execution/Execution.v
git commit -m "feat(online-maint): minimal-interface lemmas + export OnlineClockLocal"
```

---

### Task 4: examples `OnlineClockLocalExamples.v`

**Files:**
- Create: `execution/OnlineClockLocalExamples.v`
- Modify: `execution/dune` (add `OnlineClockLocalExamples`)
- Modify: `_CoqProject` (add `execution/OnlineClockLocalExamples.v`)

- [ ] **Step 1: Create the examples file**

```coq
(* Online clock locality: worked instances (test-only). *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Poset Schedule ScheduleWf
                             BarrierExecDim OnlineClock OnlineClockExamples
                             OnlineClockLocal.
Import ListNotations.

(* the local observations of s_msg3's three events *)
Example obs_e00 : local_obs s_msg3 0 0 = Send 1 0.
Proof. vm_compute. reflexivity. Qed.
Example obs_e10 : local_obs s_msg3 1 0 = Recv 0 0.
Proof. vm_compute. reflexivity. Qed.
Example obs_e20 : local_obs s_msg3 2 0 = Local.
Proof. vm_compute. reflexivity. Qed.

(* local_stamp computes the same literal timestamps as the offline stamp *)
Example lstamp_e00 : local_stamp 3 0 0 (local_obs s_msg3 0 0) = ((0,0,0),(0,2,0)).
Proof. vm_compute. reflexivity. Qed.
Example lstamp_e10 : local_stamp 3 1 0 (local_obs s_msg3 1 0) = ((0,0,1),(0,2,1)).
Proof. vm_compute. reflexivity. Qed.
Example lstamp_e20 : local_stamp 3 2 0 (local_obs s_msg3 2 0) = ((0,2,0),(0,0,0)).
Proof. vm_compute. reflexivity. Qed.

(* a concrete instance of the locality theorem *)
Example lstamp_correct_e00 :
  local_stamp (sch_nprocs s_msg3) (fst (proj1_sig e00)) (snd (proj1_sig e00))
              (local_obs s_msg3 (fst (proj1_sig e00)) (snd (proj1_sig e00)))
  = stamp s_msg3 e00.
Proof. apply local_stamp_correct. Qed.

(* causality through the schedule-blind clock: the ordered (true) case *)
Example msg3_local_e00_le_e10 :
  stamp_le
    (local_stamp (sch_nprocs s_msg3) (fst (proj1_sig e00)) (snd (proj1_sig e00))
                 (local_obs s_msg3 (fst (proj1_sig e00)) (snd (proj1_sig e00))))
    (local_stamp (sch_nprocs s_msg3) (fst (proj1_sig e10)) (snd (proj1_sig e10))
                 (local_obs s_msg3 (fst (proj1_sig e10)) (snd (proj1_sig e10)))).
Proof. apply (blo_iff_local_stamp s_msg3 wf_s_msg3 msg3_pos e00 e10). exact msg3_blo_e00_e10. Qed.
```

Implementer note: if any `vm_compute` literal differs (e.g. `obs_e00` or an
`lstamp` triple), read the value the prover reports and use it — the deliverable
is that `local_obs`/`local_stamp` are closed computable functions matching the
offline `stamp`, not the specific constant. If `msg3_pos` is not in scope from
`OnlineClockExamples`, prove `0 < sch_nprocs s_msg3` inline with `vm_compute; lia`.

- [ ] **Step 2: Register the examples file**

`execution/dune`: add `  OnlineClockLocalExamples` after `  OnlineClockLocal`.
`_CoqProject`: add `execution/OnlineClockLocalExamples.v` after `execution/OnlineClockLocal.v`.

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/OnlineClockLocalExamples.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/OnlineClockLocalExamples.v execution/dune _CoqProject
git commit -m "test(online-maint): local_obs/local_stamp = offline stamp; causality via local clock"
```

---

### Task 5: docs + whole-project green

**Files:**
- Modify: `docs/INDEX.md`
- Modify: `execution/DIM2_CLOCK.md`

- [ ] **Step 1: Add an INDEX.md subsection**

Immediately AFTER the `#### `execution/OnlineClock.v` …` subsection (and its table
and the `OnlineClockExamples.v` paragraph), insert:

```markdown
#### `execution/OnlineClockLocal.v` — online maintenance: the locality theorem (exported)

`local_stamp (N p i : nat) (o : Op)` computes the clock from purely local data —
the schedule `s` is **not** an argument, so the function cannot consult a global
view; that signature *is* the locality. `local_stamp_correct` proves it equals the
offline `stamp` at every valid event (near-definitional via `block_op_for`), and
`blo_iff_local_stamp` restates the causality characterization `blo ⟺ stamp_le`
purely through it. Two `reflexivity` interface lemmas pin the minimal interface:
the only cross-process datum the clock reads is a `Recv`'s sender id (no clock-value
piggybacking; per-process state is `(pid, a local counter)`). Admit-free.

| Name | Meaning |
|------|---------|
| `local_stamp` | schedule-blind clock: `(N,p,i,op) → (nat³ × nat³)` |
| `local_obs` | the op a process observes at its event (`op_for …`) |
| `local_stamp_correct` | `local_stamp … = stamp s x` for every valid event |
| `stamp_le` / `stamp_le_stamp` | product order on stamp pairs; bridge to `le_prod` |
| `blo_iff_local_stamp` | `blo s x y ↔ stamp_le (local_stamp x) (local_stamp y)` |
| `local_stamp_send_eq_local` / `local_stamp_recv_tag_irrel` | Send carries no clock data; Recv uses only its sender |

`OnlineClockLocalExamples.v` (test): `s_msg3`'s local observations and stamps
match the offline literals; a `local_stamp_correct` instance; causality via the
local clock.
```

- [ ] **Step 2: Update `execution/DIM2_CLOCK.md` §6**

In the "Online (the next research step)" / closing paragraph, record that the
**locality** of the clock is now proven (`local_stamp_correct` / `blo_iff_local_stamp`
in `OnlineClockLocal.v`): the clock is a function of local data only (own pid,
index, op, and a Recv's sender), with no clock-value piggyback. Narrow the
remaining open item to a *full operational distributed-semantics* model (per-process
states + message channels + a global run relation), if ever pursued. Add a row to
the lemma-map table:
`| clock computable from purely local data (no global view) | local_stamp_correct / blo_iff_local_stamp (OnlineClockLocal.v) |`.

- [ ] **Step 3: Whole-project build**

Run: `bash .claude/scripts/timed-build.sh 1800 @all 4`
Expected: exit 0 (whole project green, including the two new files).

- [ ] **Step 4: Commit**

```bash
git add docs/INDEX.md execution/DIM2_CLOCK.md
git commit -m "docs(online-maint): INDEX subsection + DIM2_CLOCK locality now proven"
```

---

## Self-Review

**Spec coverage:**
- Component 1 (`local_stamp`, `local_obs`) → Task 1. ✓
- Component 2 (`local_stamp_correct`) → Task 1. ✓
- Component 3 (`stamp_le`, `stamp_le_stamp`, `blo_iff_local_stamp`) → Task 2. ✓
- Component 4 (interface lemmas) → Task 3. ✓
- Component 5 (examples) → Task 4. ✓
- Wiring (dune/_CoqProject/Execution.v), INDEX, DIM2_CLOCK, whole-project green,
  Print Assumptions, zero admits → Tasks 1, 3, 4, 5. ✓

**Placeholder scan:** no TBD/TODO; every code step has full code; build commands
and expected outputs are explicit.

**Type consistency:** `local_stamp`/`local_obs`/`stamp_le`/`local_stamp_correct`/
`blo_iff_local_stamp` names and signatures match across Tasks 1–5; `local_stamp`'s
`(N p i : nat) (o : Op)` argument order is used identically everywhere; the example
`stamp_le (local_stamp …) (local_stamp …)` shape matches the corollary's RHS.

**Risk notes:** the only non-trivial proofs are `local_stamp_correct` (one
`rewrite block_op_for` + `destruct` + `reflexivity`) and `stamp_le_stamp`
(`cbn; tauto` over definitionally-equal Props) — both have fallback tactics in the
task notes. Everything else is `reflexivity`/`vm_compute`/`apply`. If a `vm_compute`
example constant differs, use the prover's value (the theorem, not the constant, is
the deliverable).

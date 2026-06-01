# Sync-Shape Operational Definitions + IsFullySync Bridge — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Define sync-shape at the `Op`/`Program` level, prove every `desugar s` program is sync-shaped, and prove the conditional bridge `FullySynchronizing s -> IsFullySync (exec_of_schedule s) (frontier_blocks s)` + a dim≤2 payoff corollary.

**Architecture:** New `execution/SyncShape.v` (program-level `sync_shaped` + `desugar_sync_shaped`; `frontier_block`/`frontier_blocks`; `FullySynchronizing`; the `IsFullySync` bridge; the dim≤2 corollary), `execution/SyncShapeExamples.v` (the `s_demo` end-to-end instance, test-only). Split the bridge into `SyncShapeBridge.v` if `SyncShape.v` exceeds ~500 lines.

**Tech Stack:** Coq/Rocq 9.1; `Posets`; `Dimension`; execution `Op`, `Schedule`, `Poset`, `Ordinal`, `Frontier`, `FullySync`, `FullySyncDim2`; Stdlib `Ensembles`/`List`/`Arith`/`Lia`/`Classical`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/SyncShape.v` | `synchronous_message`, `sync_shaped`, `desugar_sync_shaped`; `frontier_block`/`frontier_blocks`; `FullySynchronizing`; `nth_frontier_blocks`/`union_upto_frontier_blocks` helpers; `fully_synchronizing_is_fully_sync`; `fully_synchronizing_dim2`. |
| `execution/SyncShapeExamples.v` | `s_demo_sync_shaped`, `s_demo_fully_synchronizing`, `s_demo_is_fully_sync` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `synchronous_message`, `sync_shaped`, `desugar_sync_shaped`, `frontier_block`, `frontier_blocks`, `FullySynchronizing`, `fully_synchronizing_is_fully_sync`, `fully_synchronizing_dim2`, `s_demo`, `s_demo_sync_shaped`, `s_demo_fully_synchronizing`, `s_demo_is_fully_sync`.

**Confirmed signatures (from the codebase):**
- `Op.matched P p i q j t := op_at P p i = Some (Send q t) /\ op_at P q j = Some (Recv p t)`. `op_at P p i := nth_error (proc_ops P p) i`. `proc_len P p := length (proc_ops P p)`. `nprocs P := length (procs P)`.
- `Schedule.op_at_desugar : forall s p k, p < sch_nprocs s -> k < length (sch_frontiers s) -> op_at (desugar_prog s) p k = Some (op_for (nth k (sch_frontiers s) []) p k)`.
- `Schedule.op_for_tag : forall fr p k q t, (op_for fr p k = Send q t -> t = k) /\ (op_for fr p k = Recv q t -> t = k)`.
- `Schedule.proc_len_desugar : forall s p, p < sch_nprocs s -> proc_len (desugar_prog s) p = length (sch_frontiers s)`. `nprocs_desugar : nprocs (desugar_prog s) = sch_nprocs s`.
- `Schedule.exec_of_schedule s := exec_of (desugar s)`. `ep_carrier (exec_of_schedule s) = Event (desugar s)`; an event's `proj1_sig` is `(p,i)`.
- `FullySync.IsFullySync E blocks` = 4-conj: (1) `forall blk, List.In blk blocks -> exists x, In blk x`; (2) `forall x, exists i, i < length blocks /\ In (nth i blocks (Empty_set _)) x`; (3) `forall i j x, i<length -> j<length -> i<>j -> In (nth i …) x -> ~In (nth j …) x`; (4) `forall k, 0 < k -> k < length blocks -> IsBarrier E (union_upto E blocks k) (fun x => ~ In (union_upto E blocks k) x)`. `union_upto E blocks k := fun x => exists i, i < k /\ In (nth i blocks (Empty_set _)) x`.
- `Frontier.IsBarrier E L U` = 5-conj: cover `forall x, In L x \/ In U x`; disjoint `forall x, ~(In L x /\ In U x)`; `exists x, In L x`; `exists y, In U y`; `Hbelow forall x y, In L x -> In U y -> ep_order E x y`.
- `FullySyncDim2.fully_sync_dim_le2 : forall E blocks, IsFullySync E blocks -> (forall blk, List.In blk blocks -> exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) -> (exists d, exec_has_dimension E d /\ d <= 2)`. (NB: the dim≤2 corollary uses the `no_alt_cycle` form is NOT what `fully_sync_dim_le2` takes — it takes per-block `exists d, … /\ d<=2`. ADJUST the corollary's hypothesis to match: `forall blk ∈ frontier_blocks, exists d, inhabited (PosetDimension (sub_order … blk) d) /\ d<=2`. Confirm with `About fully_sync_dim_le2`.)
- `Ordinal.sub_order E S`.

---

## Task SS0: Scaffold

**Files:** create `execution/SyncShape.v`, `execution/SyncShapeExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the two stubs.
- [ ] **Step 2:** Add `SyncShape`, `SyncShapeExamples` to the `(modules …)` list in `execution/dune` (that order, after the Transformation A modules).
- [ ] **Step 3:** Add the two `.v` paths to `_CoqProject` (same order, after `TransformAExamples.v`).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/SyncShape.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/SyncShape.v execution/SyncShapeExamples.v execution/dune _CoqProject
git commit -m "scaffold sync-shape modules"
```

---

## Task SS1: Program-level sync-shape (`SyncShape.v`)

**Files:** `execution/SyncShape.v`

- [ ] **Step 1: Imports + defs + `desugar_sync_shaped`**

```coq
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

Lemma desugar_sync_shaped : forall s, sync_shaped (desugar_prog s).
```
Strategy for `desugar_sync_shaped`: `intros s p i q j t [Hs Hr]` (`Hs : op_at (desugar_prog s) p i = Some (Send q t)`, `Hr : op_at (desugar_prog s) q j = Some (Recv p t)`).
- Derive ranges: `op_at P p i = Some _` is `nth_error (proc_ops P p) i = Some _`, so `i < length (proc_ops P p) = proc_len P p` (`nth_error_Some`); and `proc_len (desugar_prog s) p > 0` ⟹ `p < sch_nprocs s` (`proc_len_desugar` gives `length (sch_frontiers s)` only for `p < sch_nprocs s`; for `p >= sch_nprocs s`, `proc_ops (desugar_prog s) p = nth p (procs …) [] = []` so `op_at = None`, contradicting `Hs`). Concretely: prove a helper `op_at_desugar_range : op_at (desugar_prog s) p i = Some o -> p < sch_nprocs s /\ i < length (sch_frontiers s)` (from `op_at` being `Some` ⟹ `proc_ops` nonempty at `i` ⟹ `p` in range via `nprocs_desugar`, `i` in range via `proc_len_desugar`). Use it on `Hs` (gives `p < sch_nprocs s`, `i < #frontiers`) and `Hr` (gives `q < sch_nprocs s`, `j < #frontiers`).
- `op_at_desugar s p i <ranges> : op_at (desugar_prog s) p i = Some (op_for (nth i frontiers []) p i)`; with `Hs`, `op_for (nth i frontiers []) p i = Send q t`; `proj1 (op_for_tag …) that : t = i`.
- Similarly `op_at_desugar s q j <ranges>` + `Hr` ⟹ `op_for (nth j frontiers []) q j = Recv p t`; `proj2 (op_for_tag …) that : t = j`.
- `lia` / `congruence`: `i = t = j`.

(Prove `op_at_desugar_range` as a local helper first. `nth_error_Some : nth_error l n <> None <-> n < length l`; `proc_ops (desugar_prog s) p` — if `p >= sch_nprocs s`, `nth p (map …) [] = []` via `nth_overflow` since `length (map … (seq 0 (sch_nprocs s))) = sch_nprocs s`.)

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/SyncShape.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/SyncShape.v && git commit -m "feat(execution): sync_shaped definition; desugar produces sync-shaped programs"`.

---

## Task SS2: Frontier blocks + `FullySynchronizing` + bookkeeping helpers (`SyncShape.v`)

**Files:** `execution/SyncShape.v` (extend)

- [ ] **Step 1: Defs + the two `nth`/`union_upto` helpers**

```coq
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

(* length of the blocks list *)
Lemma length_frontier_blocks :
  forall s, length (frontier_blocks s) = length (sch_frontiers s).

(* nth of the blocks list, for k < #frontiers *)
Lemma nth_frontier_blocks :
  forall s k, k < length (sch_frontiers s) ->
    nth k (frontier_blocks s) (Empty_set _) = frontier_block s k.

(* membership in union_upto reduces to "index < k" *)
Lemma union_upto_frontier_blocks :
  forall s k x,
    Ensembles.In _ (union_upto (exec_of_schedule s) (frontier_blocks s) k) x <->
    snd (proj1_sig x) < k.
```
Strategies:
- `length_frontier_blocks`: `unfold frontier_blocks; rewrite length_map, length_seq; reflexivity`.
- `nth_frontier_blocks`: `unfold frontier_blocks`. `nth k (map (frontier_block s) (seq 0 n)) (Empty_set _)` — use `nth_indep` (k < length) to switch the default to `frontier_block s (nth k (seq 0 n) 0)`, then `map_nth`/`nth_map` and `seq_nth k` (`nth k (seq 0 n) 0 = k` for `k < n`). So `= frontier_block s k`. (Mirror the `nth_map_restrict` proof in `FinFullySync.v`.)
- `union_upto_frontier_blocks`: `unfold union_upto`. `In (union_upto …) x = exists i, i < k /\ In (nth i (frontier_blocks s) ∅) x`. For `i < k`: if `i < #frontiers`, `nth i (frontier_blocks s) ∅ = frontier_block s i` (`nth_frontier_blocks`), `In (frontier_block s i) x = (snd (proj1_sig x) = i)`. So the `exists i` is `exists i, i < k /\ snd (proj1_sig x) = i` ⟺ `snd (proj1_sig x) < k`. (Forward: the `i` witness is `< k`. Backward: `i := snd (proj1_sig x) < k`; need `i < #frontiers` for `nth_frontier_blocks` — the event's index `snd (proj1_sig x) < proc_len = #frontiers` always, from `proj2_sig`/`Valid`; derive it. If `i >= #frontiers` could occur for `i < k <= #frontiers`, it can't since `k <= #frontiers`.) Mind the `i < #frontiers` side-condition when `k <= #frontiers`.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/SyncShape.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/SyncShape.v && git commit -m "feat(execution): frontier blocks, FullySynchronizing, nth/union helpers"`.

Helper you'll need: an event's index is `< #frontiers`. Prove
`event_index_lt : forall s (x : ep_carrier (exec_of_schedule s)), snd (proj1_sig x) < length (sch_frontiers s)`.
From `x`'s validity (`proj2_sig x : In (ValidSet (desugar s)) (proj1_sig x)` = `fst < nprocs /\ snd < proc_len (fst)`), and `proc_len (desugar_prog s) (fst …) = length (sch_frontiers s)` (`proc_len_desugar`, with `fst < nprocs (desugar_prog s) = sch_nprocs s`). Add this lemma in Step 1.

---

## Task SS3: The bridge `fully_synchronizing_is_fully_sync` (`SyncShape.v`)

**Files:** `execution/SyncShape.v` (extend)

- [ ] **Step 1: State + prove the bridge**

```coq
Lemma fully_synchronizing_is_fully_sync :
  forall s, FullySynchronizing s ->
    0 < sch_nprocs s ->
    IsFullySync (exec_of_schedule s) (frontier_blocks s).
```
(Use `0 < sch_nprocs s` for nonemptiness of each frontier block — every process emits an op at every index, so any process gives a witness.)
Strategy: `intros s Hfsync Hnp.` `unfold IsFullySync.` Split into the 4 conjuncts (`split; [|split; [|split]]` — NOT `repeat split`, which descends into `IsBarrier`):
1. **nonempty:** `intros blk Hblk.` `blk ∈ frontier_blocks s` ⟹ `blk = frontier_block s k` for some `k < #frontiers` (`in_map_iff` + `in_seq`). Witness: the event `(0, k)` (process 0 — valid since `0 < sch_nprocs s` and `k < #frontiers = proc_len`). Build `exist _ (0,k) <valid>` (validity `0 < sch_nprocs s = nprocs (desugar s)` via `nprocs_desugar`, `k < proc_len` via `proc_len_desugar`); `In (frontier_block s k) <that>` = `snd (0,k) = k` = `reflexivity`.
2. **cover:** `intro x.` `i := snd (proj1_sig x)`; `event_index_lt` ⟹ `i < #frontiers = length (frontier_blocks s)` (`length_frontier_blocks`). `exists i; split; [exact (that) | ]`. `In (nth i (frontier_blocks s) ∅) x` — `nth_frontier_blocks` (`i < #frontiers`) ⟹ `= frontier_block s i` ⟹ `snd (proj1_sig x) = i` = `reflexivity`.
3. **disjoint:** `intros i j x Hi Hj Hij Hin.` `Hi,Hj : i,j < length (frontier_blocks s)` = `< #frontiers` (`length_frontier_blocks`). `rewrite nth_frontier_blocks in Hin by lia` ⟹ `Hin : snd (proj1_sig x) = i`. Goal `~ In (nth j …) x`; `rewrite nth_frontier_blocks by lia`; goal `~ (snd (proj1_sig x) = j)`; from `Hin` (`= i`) and `i <> j`, `congruence`.
4. **prefix barrier:** `intros k Hk0 Hk.` (`Hk : k < length (frontier_blocks s)` = `< #frontiers`.) Goal `IsBarrier (exec_of_schedule s) (union_upto … k) (fun x => ~ In (union_upto … k) x)`. `unfold IsBarrier`; split into 5:
   - cover `forall x, In (union_upto…k) x \/ ~ In (union_upto…k) x`: `intro x; apply classic`.
   - disjoint `forall x, ~(In … x /\ ~In … x)`: `intros x [H1 H2]; exact (H2 H1)`.
   - inhabited L (`exists x, In (union_upto…k) x`): `k > 0`, so index-0 events are in `union_upto k`. Witness `(0,0)` (valid: `0 < sch_nprocs s`, `0 < #frontiers` since `k <= #frontiers` and `k > 0`); `union_upto_frontier_blocks` ⟹ `In … <that>` iff `snd (0,0) = 0 < k` ✓.
   - inhabited U (`exists y, ~ In (union_upto…k) y`): index-`k` events are NOT in `union_upto k` (`k < #frontiers` so index `k` is valid; `union_upto_frontier_blocks` ⟹ `In iff k < k` = false). Witness `(0,k)`.
   - **`Hbelow`** (`forall x y, In (union_upto…k) x -> ~ In (union_upto…k) y -> ep_order (exec_of_schedule s) x y`): `intros x y Hx Hy.` `union_upto_frontier_blocks` on `Hx` ⟹ `snd (proj1_sig x) < k`; on `Hy` (negation) ⟹ `~ (snd (proj1_sig y) < k)` ⟹ `k <= snd (proj1_sig y)`. So `snd (proj1_sig x) < k <= snd (proj1_sig y)`, i.e. `snd (proj1_sig x) < snd (proj1_sig y)`; `Hfsync x y <that>` ⟹ `ep_order … x y`. **Consumes the hypothesis.**

This is the bulk of the slice. If `SyncShape.v` approaches 500 lines, MOVE this lemma (+ the SS2 helpers) into `execution/SyncShapeBridge.v` (`From Execution Require Import SyncShape.`; wire dune + `_CoqProject`); report if split.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 480 execution/SyncShape.vo 1`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/SyncShape.v && git commit -m "feat(execution): fully-synchronizing schedule has IsFullySync frontier decomposition"`.

---

## Task SS4: The dim≤2 payoff corollary (`SyncShape.v`)

**Files:** `execution/SyncShape.v` (extend)

- [ ] **Step 1: `fully_synchronizing_dim2`**

```coq
Corollary fully_synchronizing_dim2 :
  forall s, FullySynchronizing s -> 0 < sch_nprocs s ->
    (forall blk, List.In blk (frontier_blocks s) ->
       exists d, inhabited (PosetDimension (sub_order (exec_of_schedule s) blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
```
(Confirm `fully_sync_dim_le2`'s block-hypothesis shape with `About fully_sync_dim_le2`; the plan above uses `exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2` — match it.)
Strategy: `intros s Hfsync Hnp Hblocks.` `pose proof (fully_synchronizing_is_fully_sync s Hfsync Hnp) as Hfs.` `apply (fully_sync_dim_le2 (exec_of_schedule s) (frontier_blocks s) Hfs Hblocks).`

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 360 execution/SyncShape.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/SyncShape.v && git commit -m "feat(execution): fully-synchronizing + per-block dim<=2 => execution dim<=2"`.

---

## Task SS5: The `s_demo` end-to-end instance (`SyncShapeExamples.v`)

**Files:** `execution/SyncShapeExamples.v`

`s_demo` = 2 processes, 2 frontiers: `[ [(0,1)] ; [(1,0)] ]` — 4 events `a=(0,0), b=(1,0), c=(0,1), d=(1,1)`. Frontier 0: proc0 sends to proc1 (`a` Send, `b` Recv). Frontier 1: proc1 sends to proc0 (`d` Send, `c` Recv). hb: `a≺c` (prog proc0), `b≺d` (prog proc1), `a→b` (msg, frontier0 tag 0), `d→c` (msg, frontier1 tag 1). So index-0 events `{a,b}` precede index-1 events `{c,d}`: `a≺c`(prog), `a≺b≺d`, `b≺d`(prog), and `a≺b`, `d≺c` — need `a≺c,a≺d,b≺c,b≺d`. Check: `a≺c`✓(prog), `b≺d`✓(prog), `a≺b≺d`⟹`a≺d`✓, `b≺d≺c`⟹`b≺c`✓. All four index0≺index1 hold. (`d≺c` from the frontier-1 message proc1→proc0: `d` Send, `c` Recv.)

- [ ] **Step 1: The three examples**

```coq
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical Relation_Operators.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Frontier
                              FullySync Schedule SyncShape.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.

Definition s_demo : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [(1,0)] ] |}.

Example s_demo_sync_shaped : sync_shaped (desugar_prog s_demo).

Example s_demo_fully_synchronizing : FullySynchronizing s_demo.

Example s_demo_is_fully_sync :
  IsFullySync (exec_of_schedule s_demo) (frontier_blocks s_demo).
```
Strategies:
- `s_demo_sync_shaped` := `desugar_sync_shaped s_demo`.
- `s_demo_fully_synchronizing`: `unfold FullySynchronizing. intros x y Hlt.` Each event's index `< 2` (`event_index_lt`). `Hlt : snd (proj1_sig x) < snd (proj1_sig y)` ⟹ `snd x = 0, snd y = 1`. By a `valid_event`-style case analysis on `x` and `y` (`proj1_sig ∈ {(0,0),(1,0),(0,1),(1,1)}` with the index constraint pinning `x ∈ {(0,0),(1,0)}`, `y ∈ {(0,1),(1,1)}`), exhibit `ep_order (exec_of_schedule s_demo) x y` for each of the 4 (x,y) combos via the `edge` relation (`rt_step`/`rt_trans`): `(0,0)≺(0,1)` prog; `(0,0)≺(1,1)` via `(0,0)→(1,0)` msg then `(1,0)≺(1,1)` prog; `(1,0)≺(1,1)` prog; `(1,0)≺(0,1)` via `(1,0)≺(1,1)` prog then `(1,1)→(0,1)` msg. Build concrete events `exist _ (p,i) <valid>` (validity by `vm_compute; lia`), canonicalize `x`/`y` via `proof_irrelevance`, compute `op_at` via `vm_compute` for the message edges. (Reuse the `DimExamples.v`/`Examples.v` concrete-event + edge-witness techniques; this is the heaviest part.)
- `s_demo_is_fully_sync` := `fully_synchronizing_is_fully_sync s_demo s_demo_fully_synchronizing <0 < 2>` (`Nat.lt_0_succ`/`lia`).

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 480 execution/SyncShapeExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/SyncShapeExamples.v && git commit -m "test(execution): s_demo is sync-shaped, fully-synchronizing, IsFullySync"`.

---

## Task SS6: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `SyncShape` (+ `SyncShapeBridge` if SS3 split it) to the `Require Export` line in `execution/Execution.v` (NOT the examples).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 900 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions desugar_sync_shaped.` and `Print Assumptions fully_synchronizing_is_fully_sync.` to `SyncShape.v`, `Print Assumptions s_demo_is_fully_sync.` to `SyncShapeExamples.v`; build each; read the axiom blocks (expect only standard classical/choice axioms); then `git checkout -- execution/SyncShape.v execution/SyncShapeExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "Sync-shape" subsection:
```
#### `execution/SyncShape.v` — sync-shape operational definitions + IsFullySync bridge

Program-level "sync-shape" (every matched send/recv pair at the same local index — the rendezvous form): every `desugar s` program is sync-shaped. A fully-synchronizing schedule's execution is a fully-synchronized decomposition by frontiers (`IsFullySync`), connecting program syntax to the dimension machinery.

| Name | Meaning |
|------|---------|
| `sync_shaped` / `synchronous_message` | a program where every matched send/recv pair is at the same local index |
| `desugar_sync_shaped` | every frontier-model (`desugar s`) program is sync-shaped |
| `frontier_block` / `frontier_blocks` | the per-local-index event blocks of a schedule's execution |
| `FullySynchronizing` | every index-i event precedes every index-j>i event (the barrier ordering, a hypothesis) |
| `fully_synchronizing_is_fully_sync` | a fully-synchronizing schedule's execution is `IsFullySync` by frontiers |
| `fully_synchronizing_dim2` | + per-frontier-block dim≤2 ⇒ execution dim≤2 |
| `s_demo_*` | (test) a concrete 2×2 fully-synchronizing schedule end-to-end |
```
Match the actual headers/style used elsewhere. Note: `FullySynchronizing` is the barrier-ordering lifted to the schedule (caller-discharged); not derived from per-frontier connectivity (a later refinement).
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export sync-shape; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (sync-shape defs) → SS1; Component 2 (frontier blocks + `FullySynchronizing` + helpers) → SS2; Component 3 (bridge) → SS3; Component 4 (dim2 corollary) → SS4; Component 5 (s_demo) → SS5; wiring/testing/audit → SS0 + SS6. All mapped.
- **The substantive proofs are SS1 `desugar_sync_shaped`** (a clean `op_for_tag` corollary + range helper) and **SS3 the bridge** (4 `IsFullySync` obligations, #4's `Hbelow` = `FullySynchronizing`, the rest index arithmetic via the SS2 helpers). SS2/SS4 are bookkeeping/corollary; SS5 is the heaviest (concrete event-ordering proof).
- **Corollary hypothesis correction:** the spec's `fully_synchronizing_dim2` mentioned `no_alt_cycle`, but `fully_sync_dim_le2` actually takes per-block `exists d, inhabited (PosetDimension … d) /\ d<=2`. The plan (SS4) uses THAT shape. Confirm with `About fully_sync_dim_le2`.
- **Name consistency:** `sync_shaped`, `desugar_sync_shaped`, `frontier_block`/`frontier_blocks`, `FullySynchronizing`, `fully_synchronizing_is_fully_sync`, `fully_synchronizing_dim2`, `s_demo`/`s_demo_*`.
- **Reused (confirmed):** `op_at_desugar`/`op_for_tag`/`proc_len_desugar`/`nprocs_desugar`/`exec_of_schedule` (Schedule); `IsFullySync`/`union_upto` (FullySync); `IsBarrier` (Frontier); `fully_sync_dim_le2` (FullySyncDim2); `sub_order` (Ordinal); `nth_indep`/`map_nth`/`seq_nth`/`nth_error_Some`/`classic`/`proof_irrelevance` (Stdlib). Event-validity (`proj2_sig`/`ValidSet`) for `event_index_lt`.
- **Out of scope:** connectivity⟹FullySynchronizing; Transformation B; `desugar_wf`.

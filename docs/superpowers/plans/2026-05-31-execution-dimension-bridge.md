# Execution Dimension Bridge — Implementation Plan (Sub-project B, part 1)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.
>
> **Coq-specific note (same convention as the core-model plan):** **Definitions, record/lemma statements are authoritative — implement them verbatim.** Proof *bodies* give a strategy + named sub-lemmas, not a guaranteed tactic script; develop exact tactics at execution time. "Test passes" = **the file builds** via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124 = timeout → simplify/split; 137 = OOM → `-j1`). ZERO `Admitted`. Keep each `.v` < 500 lines, each `Qed` < 5 min.

**Goal:** Connect sub-project A's `ExecPoset` to the `Dimension` theory and prove two concrete executions have dimension exactly 2 — via an explicit 2-realizer — plus a reusable critical-pair characterization interface.

**Architecture:** Three new modules in the `Execution` theory (which already depends on the `Dimension` theory): `DimBridge` (reusable bridge core), `DimCriticalPairs` (critical-pair interface + dim≤2 ⟺ no-alternating-cycle master bridge), `DimExamples` (two concrete dim-2 results, test-only).

**Tech Stack:** Coq/Rocq 9.1, `Posets.PosetClasses`/`FinitePoset`, the `Dimension` theory (`DimDefs`, `CriticalPairs`, `Theorems`), Stdlib `Ensembles`/`Finite_sets`. Builds via the wrapper.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/DimBridge.v` | `exec_has_dimension`; existence; `exec_dim_ge_2`; `exec_dim_eq_2_of_realizer`. |
| `execution/DimCriticalPairs.v` | `exec_critical_pair`; specialized re-exports; `exec_dim_le_2_iff_no_alt_cycle` (master bridge, high-risk). |
| `execution/DimExamples.v` | `exec_has_dimension E_min 2` and `exec_has_dimension (exec_of_schedule sched_n3) 2` (test-only). |
| `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md` | wiring + index. |

Canonical names: `exec_has_dimension`, `exec_dimension_exists`, `exec_dim_ge_2`, `exec_dim_eq_2_of_realizer`, `exec_critical_pair`, `exec_dim_le_2_iff_no_alt_cycle`, `sched_min`, `E_min`. Use exactly.

---

## Task B0: Scaffold the three modules

**Files:** Create `execution/DimBridge.v`, `execution/DimCriticalPairs.v`, `execution/DimExamples.v`; modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1: Create three stub files** — each containing one comment line, e.g. `(* execution dimension bridge — DimBridge *)`.

- [ ] **Step 2: Add modules to `execution/dune`** — insert `DimBridge`, `DimCriticalPairs`, `DimExamples` into the `(modules …)` list (after `Agreement`, before `Examples` is fine; order in the list does not matter to dune).

- [ ] **Step 3: Add to `_CoqProject`** — after the existing `execution/*.v` lines add:
```
execution/DimBridge.v
execution/DimCriticalPairs.v
execution/DimExamples.v
```

- [ ] **Step 4: Build the stubs**

Run: `bash .claude/scripts/timed-build.sh 120 execution/DimBridge.vo 2`
Expected: exit 0 (empty file compiles).

- [ ] **Step 5: Commit**
```bash
git add execution/DimBridge.v execution/DimCriticalPairs.v execution/DimExamples.v execution/dune _CoqProject
git commit -m "scaffold execution dimension-bridge modules"
```

---

## Task B1: Bridge core (`DimBridge.v`)

**Files:** `execution/DimBridge.v`

- [ ] **Step 1: Imports + `exec_has_dimension` + existence**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset.

(* make the execution poset instances available to the Dimension machinery *)
#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition exec_has_dimension (E : ExecPoset) (d : nat) : Prop :=
  inhabited (PosetDimension (ep_carrier E) (ep_order E) d).

Lemma exec_dimension_exists :
  forall E, exists d, exec_has_dimension E d.
```
Strategy for `exec_dimension_exists`: `unfold exec_has_dimension, ep_carrier, ep_order`. Apply `dushnik_miller_exists` (from `Theorems.v`: `forall n, cardinal A (Full_set A) n -> exists d, inhabited (PosetDimension R d)`) with `n := ep_size E` and the witness `ep_size_ok E : cardinal (ep_carrier E) (Full_set _) (ep_size E)`. The `IsPoset (ep_carrier E) (ep_order E)` needed by `dushnik_miller_exists` comes from `hb_IsPoset (ep_ranked E)` (Existing Instance). If `ep_carrier`/`ep_order` don't unfold to the exact `Event`/`hb` shape `dushnik_miller_exists` expects, `unfold ep_carrier, ep_order in *` first.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 180 execution/DimBridge.vo 2`. Expected exit 0.

- [ ] **Step 3: `exec_dim_ge_2`**

```coq
Lemma exec_dim_ge_2 :
  forall E (x y : ep_carrier E),
    Incomparable (ep_order E) x y ->
    forall d, PosetDimension (ep_carrier E) (ep_order E) d -> 2 <= d.
```
Strategy (mirror `dim_ge_1_of_two` in `AntichainComplement.v:56`, extended to rule out `d = 1`):
- `Incomparable R x y := ~ (R x y \/ R y x)`; note `x <> y` (else `R x x` by `poset_refl` contradicts). Extract `Hne : x <> y`.
- `destruct d as [|[|d']]; [..|..|lia]`. Two bad cases:
  - `d = 0`: realizer empty (`cardinalO_empty` on `dimension_cardinality`); `realizer_intersection` then forces `ep_order E x y` (vacuous `forall L ∈ ∅`), and likewise `ep_order E y x` — contradicts `Incomparable`.
  - `d = 1`: realizer is a singleton. From `dimension_cardinality : cardinal _ realizer 1`, use `cardinal_invert` (`cardinal _ S (S n) -> exists A' a, S = Add _ A' a /\ ~In A' a /\ cardinal A' n`) with `n = 0` ⇒ `realizer = Add (Empty_set _) L = Singleton L`. So the only member is `L`, and `realizer_intersection` gives `ep_order E u v <-> L u v` for all `u v`. `L` is a linear extension ⇒ total ⇒ `L x y \/ L y x` ⇒ `ep_order E x y \/ ep_order E y x` ⇒ contradicts `Incomparable`.
- Search for exact names: `cardinalO_empty`, `cardinal_invert`, `Add`, `Singleton`. `cardinalO_empty` is used in `AntichainComplement.v`; reuse it (it's in scope via `Dimension`/`Theorems` or Stdlib `Finite_sets_facts`).

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 180 execution/DimBridge.vo 2`. Expected exit 0.

- [ ] **Step 5: `exec_dim_eq_2_of_realizer`**

```coq
Lemma exec_dim_eq_2_of_realizer :
  forall E,
    (exists L1 L2,
       IsLinearExtension (ep_order E) L1 /\
       IsLinearExtension (ep_order E) L2 /\
       (forall x y, ep_order E x y <-> (L1 x y /\ L2 x y))) ->
    (exists x y, Incomparable (ep_order E) x y) ->
    exec_has_dimension E 2.
```
Strategy:
- Let `realizer := fun L => L = L1 \/ L = L2 : Ensemble (ep_carrier E -> ep_carrier E -> Prop)`.
- `IsRealizer (ep_order E) realizer`: `realizer_linear` from the two `IsLinearExtension`; `realizer_intersection x y`: `ep_order E x y <-> (forall L, realizer L -> L x y)`. Forward: from the given iff, `L1 x y` and `L2 x y`; any `L ∈ realizer` is `L1` or `L2`. Backward: instantiate the `forall` at `L1` and `L2`, get `L1 x y /\ L2 x y`, apply the iff's `<-`.
- From the incomparable pair, `L1 <> L2` (the pair is oriented oppositely by `total_comparable` + the intersection iff being false one way). Hence `cardinal _ realizer 2` (`realizer = Add (Add Empty L1) L2`, `L2 <> L1`, `L1 <> ` nothing-in-empty; build with `card_add`).
- Get some `d` with `PosetDimension … d` from `exec_dimension_exists` (`destruct`); `dimension_is_minimum` applied to `realizer` (a realizer of cardinal 2) gives `d <= 2`; `exec_dim_ge_2` (Step 3) on the incomparable pair gives `2 <= d`; so `d = 2`; rewrite to conclude `exec_has_dimension E 2`.

- [ ] **Step 6: Build** — `bash .claude/scripts/timed-build.sh 240 execution/DimBridge.vo 2`. Expected exit 0. `grep -nE "Admitted|admit" execution/DimBridge.v` must be empty.

- [ ] **Step 7: Commit**
```bash
git add execution/DimBridge.v
git commit -m "feat(execution): dimension bridge core (existence, dim>=2, explicit 2-realizer)"
```

---

## Task B2: Critical-pair interface — layer 2a (`DimCriticalPairs.v`)

**Files:** `execution/DimCriticalPairs.v`

- [ ] **Step 1: Imports + definitions + specialized re-exports**

```coq
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset.
From Execution Require Import DimBridge.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition exec_critical_pair (E : ExecPoset) (x y : ep_carrier E) : Prop :=
  IsCriticalPair (ep_order E) x y.

(* Every incomparable pair of an execution contains a critical pair. *)
Lemma exec_incomparable_has_critical_pair :
  forall E (x y : ep_carrier E),
    Incomparable (ep_order E) x y ->
    exists x' y', ep_order E x' x /\ ep_order E y y' /\ exec_critical_pair E x' y'.

(* The library's dim<=2 reversibility characterization, specialized to executions. *)
Lemma exec_critical_pairs_reversible_iff_no_alt_cycle :
  forall E (S : Ensemble (ep_carrier E * ep_carrier E)),
    (exists L, IsLinearExtension (ep_order E) L /\
               forall x y, Ensembles.In _ S (x, y) -> L y x)
    <->
    ~ (exists cycle, (forall p, List.In p cycle -> Ensembles.In _ S p)
                     /\ IsAlternatingCycle (ep_order E) cycle).
```
Strategy: both are direct instantiations of parametric library results at
`(ep_carrier E, ep_order E)` with the `IsPoset`/`Finite` instances in scope:
- `exec_incomparable_has_critical_pair` = `incomparable_lifting_to_critical_pair` (it needs `Finite (Full_set (ep_carrier E))`, obtainable from `ep_size_ok E` via `cardinal_finite`; provide it).
- `exec_critical_pairs_reversible_iff_no_alt_cycle` = `critical_pairs_reversible_iff_no_alternating_cycle` instantiated; if that theorem is stated inside a `Section` with `Context (S : Ensemble (A*A))`, instantiate `S` accordingly. Check its exact parameters with `About critical_pairs_reversible_iff_no_alternating_cycle.`

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/DimCriticalPairs.vo 2`. Expected exit 0; zero admits.

- [ ] **Step 3: Commit**
```bash
git add execution/DimCriticalPairs.v
git commit -m "feat(execution): critical-pair interface for executions (layer 2a)"
```

---

## Task B3: Master bridge — layer 2b (HIGH RISK, may be deferred)

**Files:** `execution/DimCriticalPairs.v` (extend)

> This is the one genuinely hard proof in this spec. **If it cannot be closed after real effort, STOP and report BLOCKED** — do NOT admit it. The controller will split it into a tracked follow-up; Tasks B1, B2, B4, B5 already form a complete deliverable without it.

- [ ] **Step 1: State the master bridge**

```coq
(* dim <= 2  iff  no alternating cycle among the critical pairs. *)
Lemma exec_dim_le_2_iff_no_alt_cycle :
  forall E,
    (exists d, exec_has_dimension E d /\ d <= 2)
    <->
    ~ (exists cycle,
         (forall p, List.In p cycle -> exec_critical_pair E (fst p) (snd p))
         /\ IsAlternatingCycle (ep_order E) cycle).
```

- [ ] **Step 2: Prove the Dushnik–Miller helper** (the substantive content)

```coq
Lemma exec_dim_le_2_iff_reverse_all_cp :
  forall E,
    (exists d, exec_has_dimension E d /\ d <= 2)
    <->
    (exists L, IsLinearExtension (ep_order E) L /\
               forall x y, exec_critical_pair E x y -> L y x).
```
Strategy:
- (⇐) Given `L` reversing every critical pair: let `S_cp := fun p => exec_critical_pair E (fst p) (snd p)`. Build the two-element realizer `{L1, L2}` with `L2 := L` and `L1 :=` a linear extension of `ep_order E` that reverses NO critical pair (obtain `L1` from `szpilrajn`/`extend_to_linear` on `ep_order E` itself — `ep_order E` already orients none of its incomparable critical pairs, so any of its linear extensions works for the "kept" side; concretely reuse `exec_critical_pairs_reversible_iff_no_alt_cycle` direction or `dushnik_miller`'s `all_linear_extensions` to get one extension). Verify `{L1, L2}` is a realizer via `critical_pair_realizer_iff` (CriticalPairs.v:135): a realizer ⟺ every critical pair reversed by some member — here every critical pair is reversed by `L2 = L`. Cardinal ≤ 2 ⇒ `dim ≤ 2` via `dimension_is_minimum` + `exec_dimension_exists`.
- (⇒) Given `dim ≤ 2`: there is a realizer of size ≤ 2; by `critical_pair_realizer_iff`, every critical pair is reversed by some member; the standard argument (size-2 realizer, one extension `L1` keeps the poset order so the OTHER `L2` must reverse every critical pair `L1` keeps — and `L1` keeps all of them since it extends `ep_order E`) yields a single `L := L2` reversing all critical pairs. Use `critical_pair_realizer_iff` both ways.
- Helpers you may need from `Theorems.v`: `szpilrajn_theorem`/`extend_to_linear`, `all_linear_extensions_is_realizer`. Search for exact names.

- [ ] **Step 3: Derive the master bridge** — `exec_dim_le_2_iff_no_alt_cycle` = compose `exec_dim_le_2_iff_reverse_all_cp` (Step 2) with `exec_critical_pairs_reversible_iff_no_alt_cycle` (Task B2) at `S := S_cp` (note: the cycle-side membership `exec_critical_pair E (fst p) (snd p)` must line up with `In _ S_cp p`; they are definitionally equal). Close by `tauto`/`rewrite`.

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 600 execution/DimCriticalPairs.vo 1`. Expected exit 0; zero admits. If it times out, split `exec_dim_le_2_iff_reverse_all_cp`'s two directions into separate lemmas.

- [ ] **Step 5: Commit**
```bash
git add execution/DimCriticalPairs.v
git commit -m "feat(execution): dim<=2 iff no alternating cycle of critical pairs"
```

---

## Task B4: Minimal concrete example (`DimExamples.v`)

**Files:** `execution/DimExamples.v`

The poset (fully worked): `sched_min` gives 4 events
`a=(0,0), b=(0,1), c=(1,0), d=(1,1)` with `hb`: `a ≺ b,c,d`; `c ≺ d`; and `b ∥ c`, `b ∥ d`.
Two injective `hb`-monotone keys:
`key1`: `a↦0, b↦1, c↦2, d↦3`; `key2`: `a↦0, c↦1, d↦2, b↦3`.
(`L_i x y := key_i (proj1_sig x ...) <= key_i ...`; intersection: the required pairs
`a<b, a<c, a<d, c<d` are exactly the `hb` pairs, and `b–c`, `b–d` disagree in the two keys.)

- [ ] **Step 1: Define `sched_min`, `E_min`, the keys, and the linear extensions**

```coq
From Stdlib Require Import List Arith Lia Ensembles Finite_sets Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule.
From Execution Require Import DimBridge.
Import ListNotations.

Definition sched_min : Schedule :=
  {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [] ] |}.
Definition E_min : ExecPoset := exec_of_schedule sched_min.

(* key on raw (process,index) pairs *)
Definition key1_min (pi : nat * nat) : nat :=
  match pi with (0,0) => 0 | (0,1) => 1 | (1,0) => 2 | (1,1) => 3 | _ => 99 end.
Definition key2_min (pi : nat * nat) : nat :=
  match pi with (0,0) => 0 | (1,0) => 1 | (1,1) => 2 | (0,1) => 3 | _ => 99 end.

Definition L1_min (x y : ep_carrier E_min) : Prop :=
  key1_min (proj1_sig x) <= key1_min (proj1_sig y).
Definition L2_min (x y : ep_carrier E_min) : Prop :=
  key2_min (proj1_sig x) <= key2_min (proj1_sig y).
```
(Note: `ep_carrier E_min = Event (desugar sched_min)`; `proj1_sig x : nat*nat`.)

- [ ] **Step 2: Prove each `L_i_min` is a linear extension**

For each `i`, prove `IsLinearExtension (ep_order E_min) L_i_min`:
- `IsTotalOrder`: `IsPoset` (refl: `key ≤ key`; antisym: `key x = key y` ⇒ `x = y` — here use that the four valid events have distinct keys, so equal keys force equal `proj1_sig`, then equal events by `proof_irrelevance`/`event_eq_dec`; for invalid pairs the `99` default never arises because events are valid — but antisym must still hold for ALL `x y : ep_carrier E_min`; since every such `x` has `proj1_sig x ∈ {(0,0),(0,1),(1,0),(1,1)}` by its validity proof, derive that and case-split). `total_comparable`: `key x ≤ key y \/ key y ≤ key x` by `lia`.
- `linear_extends`: `ep_order E_min x y -> L_i_min x y`, i.e. `key_i` is monotone along `hb`. Prove a helper `key_i` monotone along `edge` (finite check: for each edge form, compare keys — `lia` after computing the two ops), then lift along `clos_refl_trans` exactly like `rank_hb_le` (`Rank.v`): induction on the closure.

Helper to extract that a valid event's `proj1_sig` is one of the four pairs:
```coq
Lemma valid_event_min_cases :
  forall x : ep_carrier E_min,
    let pi := proj1_sig x in
    pi = (0,0) \/ pi = (0,1) \/ pi = (1,0) \/ pi = (1,1).
```
(from `proj2_sig x : fst pi < 2 /\ snd pi < proc_len … = 2`; `lia`/`omega`-style case split on the two coordinates each `< 2`.)

- [ ] **Step 3: Prove the intersection `hb = L1 ∩ L2`**

```coq
Lemma hb_min_realizer :
  forall x y : ep_carrier E_min,
    ep_order E_min x y <-> (L1_min x y /\ L2_min x y).
```
- Forward: from `linear_extends` of both (Step 2).
- Backward: `intros [H1 H2]`. Using `valid_event_min_cases` on `x` and `y`, reduce to the 4×4 concrete pairs; for the four pairs where both keys are `≤` (`a<b, a<c, a<d, c<d`, plus reflexive equalities) exhibit the explicit `hb` path (`apply rt_step`/`rt_trans` with the program-order or message `edge`); for every other pair, `H1`/`H2` are contradictory (`simpl in *; lia`).

- [ ] **Step 4: Conclude dimension 2**

```coq
Theorem E_min_dim_2 : exec_has_dimension E_min 2.
```
Strategy: `apply exec_dim_eq_2_of_realizer`. First arg: `exists L1_min, L2_min`, with the two `IsLinearExtension` (Step 2) and `hb_min_realizer` (Step 3). Second arg: exhibit the incomparable pair `b=(0,1)`, `c=(1,0)`: `Incomparable (ep_order E_min) b c` — both `~ hb b c` and `~ hb c b` follow because their keys disagree (`L1_min b c` holds but `L2_min b c` fails, so by `hb_min_realizer` `~ hb b c`; symmetric for the other direction). Construct `b`, `c` as `exist _ (0,1) _` / `exist _ (1,0) _` with validity proofs `ltac:(cbn; lia)` style.

- [ ] **Step 5: Build** — `bash .claude/scripts/timed-build.sh 300 execution/DimExamples.vo 2`. Expected exit 0; zero admits.

- [ ] **Step 6: Commit**
```bash
git add execution/DimExamples.v
git commit -m "test(execution): minimal execution has dimension exactly 2"
```

---

## Task B5: N=3 example (`DimExamples.v`, extend)

**Files:** `execution/DimExamples.v` (extend)

`sched_n3` (from `Examples.v`) has 6 events `(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)` with `hb`:
`(0,0) ≺ (0,1),(1,0),(1,1),(2,1)`; `(1,0) ≺ (1,1) ≺ (2,1)`; `(1,0) ≺ (2,1)`; `(2,0) ≺ (2,1)`.
Incomparable pairs include `(0,1)` vs everything except `(0,0)`, and `(2,0)` vs `(0,*),(1,*)`.

- [ ] **Step 1: Define two injective `hb`-monotone keys for the 6 events**

Follow the minimal-example template. Pick `key1_n3`, `key2_n3 : nat*nat -> nat` assigning the six pairs distinct values, both monotone along `hb`, and disagreeing on exactly the incomparable pairs. Derive them by: list the `hb` partial order (above); choose `key1` = one topological order, `key2` = a second topological order that reverses every incomparable pair relative to `key1` (a valid pair exists because this poset is 2-dimensional — that is exactly what we are proving). Verify the choice by checking, for every incomparable pair, the two keys disagree (a finite check). Define `L1_n3`, `L2_n3` as `key_i (proj1_sig ·) <= key_i (proj1_sig ·)`.

```coq
Definition E_n3 : ExecPoset := exec_of_schedule sched_n3.   (* sched_n3 from Examples.v *)
(* key1_n3, key2_n3, L1_n3, L2_n3 as in the minimal example, over the 6 pairs *)
```
(Import `sched_n3` by adding `Examples` to the `From Execution Require Import …` line of `DimExamples.v`.)

- [ ] **Step 2: Linear-extension + intersection proofs (same method as B4)**

```coq
Lemma valid_event_n3_cases :
  forall x : ep_carrier E_n3, let pi := proj1_sig x in
    pi = (0,0) \/ pi = (0,1) \/ pi = (1,0) \/ pi = (1,1) \/ pi = (2,0) \/ pi = (2,1).
Lemma L1_n3_linext : IsLinearExtension (ep_order E_n3) L1_n3.
Lemma L2_n3_linext : IsLinearExtension (ep_order E_n3) L2_n3.
Lemma hb_n3_realizer :
  forall x y : ep_carrier E_n3, ep_order E_n3 x y <-> (L1_n3 x y /\ L2_n3 x y).
```
Same structure as B4: `valid_event_n3_cases` reduces to the 36 concrete ordered pairs; `linear_extends` via edge-monotonicity + `clos_refl_trans` induction; intersection backward by exhibiting `hb` paths for the comparable pairs and key-disagreement (`lia`) for the rest. This is mechanical but larger; if `DimExamples.v` approaches 500 lines, the controller will move the n3 proof to its own file `DimExampleN3.v` (wire it the same way).

- [ ] **Step 3: Conclude**

```coq
Theorem E_n3_dim_2 : exec_has_dimension E_n3 2.
```
`apply exec_dim_eq_2_of_realizer` with the two linear extensions + `hb_n3_realizer`; the incomparable witness `(0,1)`,`(2,0)` (reuse the reasoning from `n3_concurrent` in `Examples.v`, or re-derive via key disagreement).

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 480 execution/DimExamples.vo 2` (or the split file). Expected exit 0; zero admits. If 124, split per Step 2's note.

- [ ] **Step 5: Commit**
```bash
git add execution/DimExamples.v
git commit -m "test(execution): N=3 execution has dimension exactly 2"
```

---

## Task B6: Aggregator export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1: Export from the aggregator** — edit the `Require Export` line in `execution/Execution.v` to add `DimBridge DimCriticalPairs` (NOT `DimExamples`).

- [ ] **Step 2: Build the whole `execution` library** — `bash .claude/scripts/timed-build.sh 600 execution 2`. Expected exit 0.

- [ ] **Step 3: Whole-project build** — `bash .claude/scripts/timed-build.sh 1800 @all 2`. Expected exit 0.

- [ ] **Step 4: `Print Assumptions` audit** — temporarily append to `execution/DimExamples.v`:
```coq
Print Assumptions E_min_dim_2.
Print Assumptions E_n3_dim_2.
```
Build it (`bash .claude/scripts/timed-build.sh 300 execution/DimExamples.vo 2 2>&1 | tee /tmp/dim_pa.log`), read the axiom blocks, then `git checkout -- execution/DimExamples.v` to revert. Expected: only standard classical axioms (`classic`, `proof_irrelevance`, `constructive_definite_description`, `Extensionality_Ensembles`); record them in the commit message / report. Any `admit`-generated axiom or `execution/` lemma = RED FLAG → fix.

- [ ] **Step 5: Update `docs/INDEX.md`** — add a "Dimension bridge" subsection under the Execution library listing: `exec_has_dimension`, `exec_dimension_exists`, `exec_dim_ge_2`, `exec_dim_eq_2_of_realizer` (DimBridge); `exec_critical_pair`, `exec_incomparable_has_critical_pair`, `exec_dim_le_2_iff_no_alt_cycle` (DimCriticalPairs); `E_min_dim_2`, `E_n3_dim_2` (DimExamples). Match the existing table style.

- [ ] **Step 6: Commit**
```bash
git add execution/Execution.v docs/INDEX.md
git commit -m "feat(execution): export dimension bridge; index; assumptions audit"
```

---

## Self-review notes

- **Spec coverage:** Component 1 (bridge core) → B1; Component 2a → B2; Component 2b master bridge → B3 (flagged deferrable); Component 3 minimal example → B4; Component 3 N=3 → B5; file layout/wiring/testing/audit → B0 + B6. All spec sections mapped.
- **High-risk isolation:** B3 (master bridge) is a separate task/commit and explicitly deferrable; B1/B2/B4/B5 deliver the concrete dim-2 results without it.
- **Name consistency:** `exec_has_dimension`, `exec_dim_ge_2`, `exec_dim_eq_2_of_realizer`, `exec_critical_pair`, `exec_dim_le_2_iff_no_alt_cycle`, `E_min`, `E_n3`, `key1_min`/`key2_min`/`L1_min`/`L2_min` (and `_n3` analogues) used consistently across tasks.
- **Realizer/finiteness:** every dimension lemma needs `IsPoset`/`Finite` of `(ep_carrier E, ep_order E)` — provided by `hb_IsPoset`/`hb_IsFinitePoset` (Existing Instances) and `ep_size_ok`/`cardinal_finite`. Stated in B1/B2.
- **Possible Stdlib name drift:** `cardinalO_empty`, `cardinal_invert`, `szpilrajn_theorem`, `extend_to_linear`, `all_linear_extensions_is_realizer` — confirm exact names with `About`/`Search` at execution time.

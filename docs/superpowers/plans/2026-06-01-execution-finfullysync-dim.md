# Exact n-way Fully-Synchronized Dimension — Implementation Plan (slice 2 of 2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Prove `fully_sync_dimension` — the exact dimension of a ≥2-element fully-synchronized execution is `max(1, maxᵢ dim(Bᵢ))` — via a generic `fin_fully_sync_dimension` (induction over the block list, reusing the dim≤2 n-way scaffolding but with slice 1's exact `fin_barrier_dimension_full`), instantiated for `IsFullySync`.

**Architecture:** New `execution/FinFullySyncDim.v` (generic theorem + carrier-quantified aux induction), `execution/FullySyncDimExact.v` (ExecPoset instance), `execution/FinFullySyncDimExamples.v` (all-singleton-chain example, test-only). The induction is a near-copy of `FinFullySync.v`'s `fin_fully_sync_dim_le2_aux`, swapping the dim≤2 conclusion for the exact `max(1, fold dims)` and adding a singleton-vs-≥2 lower-part split.

**Tech Stack:** Coq/Rocq 9.1; `Posets`; `Dimension` (`DimDefs`, `Theorems`, `AntichainComplement` for `dim_ge_1_of_two`); execution `DimIso`, `FinPosetDimSurgery`, `FinPosetDim`, `FinExtremumDim`, `FinFullySync`, and (instance/examples) `Poset`, `Ordinal`, `FullySync`, `FullySyncDim2`, `DimBridge`; Stdlib `Ensembles`/`Finite_sets`/`List`/`Arith`/`Lia`/`Classical`/`ProofIrrelevance`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/FinFullySyncDim.v` | `singleton_union_one_block` (sub-lemma), `fin_fully_sync_dimension_aux`, `fin_fully_sync_dimension` (generic). |
| `execution/FullySyncDimExact.v` | `fully_sync_dimension` (ExecPoset instance). |
| `execution/FinFullySyncDimExamples.v` | `chain_all_singleton_dim` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `singleton_union_one_block`, `fin_fully_sync_dimension_aux`, `fin_fully_sync_dimension`, `fully_sync_dimension`, `chain_all_singleton_dim`.

**CONFIRMED reusable helpers (from `FinFullySync.v`, all general):**
- `fin_ordinal_partition R (blocks)`; `restrict_block (L B)` (NO `R` arg); `fin_sub_order_finite R Hfin L`; `fin_block_iso_full R (B) (Hfull : forall x, In B x) d (Hd : inhabited (PosetDimension (fin_sub_order R B) d)) : inhabited (PosetDimension R d)`.
- `restricted_block_dim2 R {HR} (L B) (Hsub : forall x, In B x -> In L x) d (Hd : inhabited (PosetDimension (fin_sub_order R B) d)) : inhabited (PosetDimension (fin_sub_order (fin_sub_order R L) (restrict_block L B)) d)` — **already general in `d`** (the "dim2" name is a misnomer; reuse it directly, no new lemma needed).
- `fin_prefix_barrier R (pre Bk) (Hpre : pre <> []) (Hpart : fin_ordinal_partition R (pre ++ [Bk])) : fin_is_barrier R (fun x => exists i, i < length pre /\ In (nth i pre ∅) x) Bk`.
- `fin_prefix_restricted_partition R (pre Bk) (Hpart) : fin_ordinal_partition (fin_sub_order R L) (map (restrict_block L) pre)` (the inline restricted partition; read its exact statement in `FinFullySync.v`).
- The peel device: `destruct blocks as [|b0 bs] eqn:Hbl` then `destruct (exists_last Hneq) as [pre [Bk Heq]]; subst blocks`. `app_nth1`/`app_nth2`/`Nat.sub_diag` for `nth (pre++[Bk])`.

From `FinExtremumDim.v`: `fin_barrier_dimension_full R Hfin (L U) (HB : fin_is_barrier R L U) dL dU dW (HdL)(HdU)(HdW) : dW = Nat.max 1 (Nat.max dL dU)` (CONFIRM with `About` — recall slice-1 found `fin_barrier_dimension`/`fin_block_dim0_*` do NOT take `Hfin`, but `fin_barrier_dimension_full` DOES per its own signature — verify); `fin_singleton_dim0 R {HR} (forall x y, x=y) : PosetDimension R 0` (no `Hfin` arg).
From `FinPosetDimSurgery.v`: `fin_dim_exists R Hfin : exists d, inhabited (PosetDimension R d)`; `fin_posdim_unique`.
From `AntichainComplement`: `dim_ge_1_of_two R d (PosetDimension R d) (exists a b, a<>b) : 1 <= d`.

**Section convention** (FinFullySyncDim.v): `Section FinFullySyncDim. Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (Hfin : Finite A (Full_set A)).` — but the AUX lemma is carrier-quantified (`forall n A' R' HR' Hfin' blocks dims, …`), like `fin_fully_sync_dim_le2_aux`.

**EXECUTION-TIME FIRST STEP:** `About fin_barrier_dimension_full`, `About fin_singleton_dim0`, `About fin_block_iso_full`, `About restricted_block_dim2`, `About fin_prefix_barrier`, `About fin_prefix_restricted_partition`, `About dim_ge_1_of_two`, `About fin_posdim_unique` — confirm every binder before writing the induction.

---

## Task Y0: Scaffold

**Files:** create `execution/FinFullySyncDim.v`, `execution/FullySyncDimExact.v`, `execution/FinFullySyncDimExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the three stubs.
- [ ] **Step 2:** Add `FinFullySyncDim`, `FullySyncDimExact`, `FinFullySyncDimExamples` to the `(modules …)` list in `execution/dune` (that order, after the exact-barrier-dim modules).
- [ ] **Step 3:** Add the three `.v` paths to `_CoqProject` (same order, after the exact-barrier-dim entries).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/FinFullySyncDim.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/FinFullySyncDim.v execution/FullySyncDimExact.v execution/FinFullySyncDimExamples.v execution/dune _CoqProject
git commit -m "scaffold exact n-way fully-sync dimension modules"
```

---

## Task Y1: The singleton-prefix sub-lemma (`FinFullySyncDim.v`)

**Files:** `execution/FinFullySyncDim.v`

This isolates the trickiest arithmetic fact: if the union of a nonempty prefix is a
single element, the prefix is one singleton block, so its dims-fold is 0.

- [ ] **Step 1: Imports + section + sub-lemma**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim FinExtremumDim FinFullySync.
Import ListNotations.

(* If the union L of a nonempty prefix `pre` (blocks nonempty, pairwise disjoint)
   has at most one element, then `pre` is a single block and its dims-fold is 0. *)
Lemma singleton_union_one_block :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (pre : list (Ensemble A)) (predims : list nat) (L : Ensemble A),
    pre <> [] ->
    length predims = length pre ->
    (forall i, i < length pre -> exists x, Ensembles.In _ (nth i pre (Empty_set _)) x) ->   (* nonempty *)
    (forall i j x, i < length pre -> j < length pre -> i <> j ->
       Ensembles.In _ (nth i pre (Empty_set _)) x ->
       ~ Ensembles.In _ (nth j pre (Empty_set _)) x) ->                                     (* disjoint *)
    (forall i, i < length pre ->
       PosetDimension (fin_sub_order R (nth i pre (Empty_set _))) (nth i predims 0)) ->
    (forall x, Ensembles.In _ L x <-> exists i, i < length pre /\ Ensembles.In _ (nth i pre (Empty_set _)) x) ->
    (forall u v : {z | Ensembles.In _ L z}, u = v) ->          (* L has <= 1 element *)
    fold_right Nat.max 0 predims = 0.
(* NB: takes nonempty+disjoint DIRECTLY, NOT `fin_ordinal_partition R pre` (unsatisfiable
   for a proper prefix — cover ranges over all A). Both derivable from the partition of
   `pre ++ [Bk]` at indices < length pre via app_nth1. *)
```
Strategy:
- From "`L` has ≤1 element" + `L = ⋃ pre` + each `pre`-block nonempty & pairwise
  disjoint (from `fin_ordinal_partition R pre`): show `pre` has exactly ONE block.
  If `pre` had ≥2 blocks `i ≠ j`, both nonempty with witnesses `xi ∈ Bi`, `xj ∈ Bj`,
  both in `L`; disjointness ⟹ `xi ≠ xj` (different blocks); but lifting both into
  `{z|In L z}` and using "all equal" ⟹ `xi = xj` (via `proj1_sig`), contradiction.
  So `length pre = 1`, hence `pre = [B0]`, `predims = [d0]` (lengths).
- `B0` is a singleton: `B0 = L` (single block ⟹ its union is `B0`), and `L` ≤1
  element. So `fin_sub_order R B0` has ≤1 element ⟹ `d0 = 0` by `fin_posdim_unique`
  with `fin_singleton_dim0` (the `PosetDimension … (nth 0 predims 0) = d0` hypothesis
  vs `PosetDimension (fin_sub_order R B0) 0`). Then `fold_right Nat.max 0 [d0] = Nat.max 0 0 = 0`.

This sub-lemma is fiddly (the "≥2 blocks ⟹ two distinct elements" argument); keep it
focused. If it balloons, that's acceptable — it's isolated here.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/FinFullySyncDim.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/FinFullySyncDim.v && git commit -m "feat(execution): singleton prefix has zero dims-fold"`.

---

## Task Y2: The carrier-quantified aux induction (`FinFullySyncDim.v`)

**Files:** `execution/FinFullySyncDim.v` (extend)

**READ FIRST:** `FinFullySync.v`'s `fin_fully_sync_dim_le2_aux` (lines ~363–438) IN FULL — this task is that proof with the conclusion swapped to the exact formula. Reuse its `exists_last` peel, `fin_prefix_barrier`, `fin_prefix_restricted_partition`, and the `pre = []` / `pre ≠ []` split; ADD the singleton-vs-≥2 lower-part case.

- [ ] **Step 1: State the aux + the wrapper**

```coq
Lemma fin_fully_sync_dimension_aux :
  forall n (A : Type) (R : A -> A -> Prop) (HR : IsPoset A R)
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)) (dims : list nat),
    length blocks <= n -> length dims = length blocks ->
    @fin_ordinal_partition A R blocks ->
    (forall i, i < length blocks ->
       PosetDimension (@fin_sub_order A R (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b, a <> b) ->
    forall dW, PosetDimension R dW -> dW = Nat.max 1 (fold_right Nat.max 0 dims).

Lemma fin_fully_sync_dimension :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)) (dims : list nat),
    fin_ordinal_partition R blocks ->
    length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (fin_sub_order R (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : A, a <> b) ->
    forall dW, PosetDimension R dW -> dW = Nat.max 1 (fold_right Nat.max 0 dims).
```
`fin_fully_sync_dimension` := `fin_fully_sync_dimension_aux (length blocks) A R HR Hfin blocks dims (le_n _) … `.

- [ ] **Step 2: Prove `fin_fully_sync_dimension_aux`** (`induction n`)

`induction n as [|n IHn]; intros A R HR Hfin blocks dims Hlen Hlendims Hpart Hdims Hge2 dW HdW.`
- **`n = 0`:** `length blocks <= 0` ⟹ `blocks = []` ⟹ cover clause says every `x` is in `nth i [] ∅` for `i < 0` — impossible, so `A` empty, contradicting `Hge2` (two distinct elements). `exfalso`; `destruct Hge2 as [a [b _]]; destruct (Hcov a) as [i [Hi _]]; lia` (`i < length [] = 0`).
- **`n = S n'`:** `destruct blocks as [|b0 bs] eqn:Hbl`. `blocks = []`: same `exfalso` as base. Else `assert (Hneq : blocks <> [])` (`subst; discriminate`); `destruct (exists_last Hneq) as [pre [Bk Heq]]`; `subst blocks`. Correspondingly split `dims = predims ++ [dk]`: from `length dims = length (pre++[Bk]) = length pre + 1`, `dims` is nonempty; `destruct (exists_last <dims<>[]>) as [predims [dk Hdeq]]; subst dims`. (`length predims = length pre`.)
  - `length (pre ++ [Bk]) <= S n'` ⟹ `length pre <= n'` (`length_app`; `lia`).
  - **`pre = []`** (`blocks = [Bk]`, `dims = [dk]`): `Bk` full (cover: every `x ∈ nth 0 [Bk] ∅ = Bk`). `fin_block_iso_full R Bk <Bk full> dk` needs `inhabited (PosetDimension (fin_sub_order R Bk) dk)` from `Hdims 0 …` (= `PosetDimension (fin_sub_order R (nth 0 [Bk] ∅)) (nth 0 [dk] 0) = PosetDimension (fin_sub_order R Bk) dk`); `inhabits` it; get `inhabited (PosetDimension R dk)`; `destruct` + `fin_posdim_unique` with `HdW` ⟹ `dW = dk`. `dim_ge_1_of_two R dW HdW Hge2 : 1 <= dW` ⟹ `1 <= dk`. `fold_right Nat.max 0 [dk] = Nat.max dk 0 = dk`. So `dW = dk = Nat.max 1 dk` (`lia`). Goal `dW = Nat.max 1 (fold_right Nat.max 0 [dk])` ⟹ `lia`.
  - **`pre ≠ []`**: `set (L := fun x => exists i, i < length pre /\ In (nth i pre ∅) x)`.
    - `Hbar : fin_is_barrier R L Bk := fin_prefix_barrier R pre Bk <pre<>[]> Hpart` (note `Hpart : fin_ordinal_partition R (pre++[Bk])`).
    - `dk`'s block dim: `HdBk : PosetDimension (fin_sub_order R Bk) dk` from `Hdims (length pre) …` (`nth (length pre) (pre++[Bk]) ∅ = Bk` via `app_nth2`+`Nat.sub_diag`; `nth (length pre) (predims++[dk]) 0 = dk` similarly).
    - `dL`: `destruct (fin_dim_exists (fin_sub_order R L) (fin_sub_order_finite R Hfin L)) as [dL [HdL]]` (`HdL : PosetDimension (fin_sub_order R L) dL`).
    - `pose proof (fin_barrier_dimension_full R Hfin L Bk Hbar dL dk dW HdL HdBk HdW) as HdWeq` (`HdWeq : dW = Nat.max 1 (Nat.max dL dk)`). (Confirm `fin_barrier_dimension_full`'s arg order; it may or may not take `Hfin` — match `About`.)
    - `destruct (classic (exists u v : {z | In L z}, u <> v)) as [HL2 | HL1].`
      - **`HL2` (L ≥2):** IH at `(fin_sub_order R L, fin_sub_order_finite R Hfin L, map (restrict_block L) pre, predims)`:
        - length: `length (map (restrict_block L) pre) = length pre <= n'` (`length_map`).
        - partition: `fin_prefix_restricted_partition R pre Bk Hpart` (read its exact statement — it yields `fin_ordinal_partition (fin_sub_order R L) (map (restrict_block L) pre)`).
        - per-block dims: `forall i, i < length (map …) -> PosetDimension (fin_sub_order (fin_sub_order R L) (nth i (map (restrict_block L) pre) ∅)) (nth i predims 0)`. For each `i`: `nth i (map (restrict_block L) pre) ∅ = restrict_block L (nth i pre ∅)` (`nth_map_restrict`); the prefix block `nth i pre ∅` has dim `nth i predims 0` (from `Hdims i …`, since `nth i (pre++[Bk]) ∅ = nth i pre ∅` and `nth i (predims++[dk]) 0 = nth i predims 0` for `i < length pre` via `app_nth1`); `restricted_block_dim2 R L (nth i pre ∅) <Bi ⊆ L> (nth i predims 0) (inhabits that)` transports it (it's general in `d`). `destruct` the `inhabited` to get the bare `PosetDimension`.
        - `Hge2` for the sub-poset: `HL2` directly (`exists u v, u <> v`).
        - IH returns `dL = Nat.max 1 (fold_right Nat.max 0 predims)`.
        - Substitute into `HdWeq`: `dW = Nat.max 1 (Nat.max (Nat.max 1 (fold predims)) dk)`. Rewrite `fold_right Nat.max 0 (predims ++ [dk]) = Nat.max (fold_right Nat.max 0 predims) dk` (prove/`Search` `fold_right_max_app` or do `induction predims`). Goal `dW = Nat.max 1 (Nat.max (fold predims) dk)`; with `dL = max 1 (fold predims)`, `lia` closes (`max 1 (max (max 1 f) dk) = max 1 (max f dk)`).
      - **`HL1` (L singleton):** `~ ∃ u v, u <> v` ⟹ `forall u v : {z|In L z}, u = v` (by `classic`/`NNPP`: if `u <> v` for some, contradiction; so all equal). `fin_singleton_dim0 (fin_sub_order R L) <all equal>` gives `PosetDimension (fin_sub_order R L) 0`; `fin_posdim_unique` with `HdL` ⟹ `dL = 0`. `singleton_union_one_block R pre predims L <pre<>[]> <len> <Hpart_pre> <Hdims_pre> <L = ⋃ pre> <all equal> : fold_right Nat.max 0 predims = 0` (Y1). [Derive `Hpart_pre : fin_ordinal_partition R pre` — WAIT: as in H3, `fin_ordinal_partition R pre` is UNSATISFIABLE for a proper prefix (cover over all A). So `singleton_union_one_block` must NOT require full `fin_ordinal_partition R pre`. RESTATE Y1's `singleton_union_one_block` to take what's actually available: the nonempty + disjoint clauses of `pre` (derivable from `Hpart` of `pre++[Bk]` restricted to indices `< length pre`) + the per-block dims + `L = ⋃ pre` + all-equal. Adjust Y1's hypotheses to use `(forall i, i<length pre -> exists x, In (nth i pre ∅) x)` (nonempty) and `(forall i j x, i<length pre -> j<length pre -> i<>j -> In (nth i pre ∅) x -> ~ In (nth j pre ∅) x)` (disjoint) instead of `fin_ordinal_partition R pre`. Both follow from `Hpart` of `pre++[Bk]` via `app_nth1`. UPDATE Y1 accordingly.]
        - With `dL = 0` and `fold predims = 0`: `HdWeq : dW = Nat.max 1 (Nat.max 0 dk) = Nat.max 1 dk`. Goal `dW = Nat.max 1 (fold (predims++[dk]))`; `fold (predims++[dk]) = Nat.max (fold predims) dk = Nat.max 0 dk = dk`; so `Nat.max 1 dk = Nat.max 1 dk`. `lia` (after the fold-app rewrite + `fold predims = 0`).

This is LONG (~200-300 lines). If `FinFullySyncDim.v` approaches 500 lines, move the aux into the file but factor the `pre ≠ []` body's two sub-cases into helper lemmas. ZERO admits — if a sub-step resists after real effort, report BLOCKED.

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 900 execution/FinFullySyncDim.vo 1`. Exit 0; zero admits.
- [ ] **Step 4: Commit** — `git add execution/FinFullySyncDim.v && git commit -m "feat(execution): exact n-way ordinal-partition dimension by induction"`.

---

## Task Y3: ExecPoset instance (`FullySyncDimExact.v`)

**Files:** `execution/FullySyncDimExact.v`

**READ FIRST:** `FullySyncDim2.v`'s `fully_sync_dim_le2` — this is the SAME translation (`IsFullySync` → `fin_ordinal_partition`) with the exact theorem instead of the dim≤2 one.

- [ ] **Step 1: `fully_sync_dimension`**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FullySync FullySyncDim2 FinPosetDimSurgery FinPosetDim
                              FinFullySync FinFullySyncDim.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Lemma fully_sync_dimension :
  forall E blocks dims, IsFullySync E blocks ->
    length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    forall dW, PosetDimension (ep_order E) dW ->
      dW = Nat.max 1 (fold_right Nat.max 0 dims).
```
Strategy (mirror `fully_sync_dim_le2`):
- `Hfin : Finite (ep_carrier E)(Full_set _)` := `cardinal_finite _ _ (ep_size E)(ep_size_ok E)`.
- `Hpart : fin_ordinal_partition (ep_order E) blocks` from `IsFullySync`'s nonempty/cover/disjoint fields + `fully_sync_pairwise_below E blocks Hfs` (the "below" clause). Assemble (`repeat split` carefully — destructure `Hfs` first; reuse `FullySyncDim2.v`'s exact assembly).
- block dims: `fin_sub_order (ep_order E) blk` is definitionally `sub_order E blk`, so the given `Hdims` supplies them directly (`unfold`/`change` if needed).
- `apply (fin_fully_sync_dimension (ep_order E) Hfin blocks dims Hpart Hlendims Hdims' Hge2 dW HdW)`. (`HR` from `hb_IsPoset`.) Conclude.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 360 execution/FullySyncDimExact.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/FullySyncDimExact.v && git commit -m "feat(execution): fully_sync_dimension (ExecPoset exact n-way dimension)"`.

---

## Task Y4: All-singleton-chain example (`FinFullySyncDimExamples.v`)

**Files:** `execution/FinFullySyncDimExamples.v`

The `E_min` nontrivial cross-check is blocked on task #66 (`dim{b,c,d}=2` exact realizer). Use a cheap all-singleton example that exercises the n-way `fold` + singleton-L recursion end-to-end.

- [ ] **Step 1: `chain_all_singleton_dim`**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import FinPosetDimSurgery FinPosetDim FinExtremumDim
                              FinFullySync FinFullySyncDim.
Import ListNotations.

(* The 2-element chain false < true on bool, as a generic finite poset. *)
Definition chainR (a b : bool) : Prop := a = b \/ (a = false /\ b = true).

Example chain_all_singleton_dim :
  exists dW, inhabited (PosetDimension chainR dW) /\ dW = 1.
```
Strategy: reuse slice 1's `FinExtremumDimExamples.v` `chain2_R` machinery (READ it — `IsPoset bool chainR`, `Finite bool (Full_set bool)`, the singleton realizer `PosetDimension chainR 1`). Then apply `fin_fully_sync_dimension chainR Hfin blocks dims …`:
- `blocks := [ (fun b => b = false) ; (fun b => b = true) ]` (the two singleton blocks).
- `dims := [0; 0]` (each singleton block has dimension 0 via `fin_singleton_dim0`).
- `fin_ordinal_partition chainR blocks`: nonempty (`false`/`true`); cover (`destruct b`); disjoint (`false <> true`); below (`false < true`: `nth 0 = {false}`, `nth 1 = {true}`, `chainR false true` holds).
- per-block dims `forall i < 2, PosetDimension (fin_sub_order chainR (nth i blocks ∅)) (nth i [0;0] 0)`: each block is a singleton ⟹ `fin_singleton_dim0` ⟹ dim 0. (`nth 0/1 [0;0] 0 = 0`.)
- `Hge2 : exists a b : bool, a <> b` := `false, true`.
- `dW`: from the slice-1 `PosetDimension chainR 1` (or `fin_dim_exists`). `fin_fully_sync_dimension … dW HdW : dW = Nat.max 1 (fold_right Nat.max 0 [0;0]) = Nat.max 1 0 = 1`.
- `exists dW; split; [exact (inhabits HdW) | <dW = 1>]`. (If you used the explicit `PosetDimension chainR 1`, `dW = 1` directly; else `fin_fully_sync_dimension` forces `dW = 1`.)

(NOTE: `fin_fully_sync_dimension` is stated with `PosetDimension R dW` (Type-valued) as a hypothesis and concludes `dW = …` (Prop) — so you SUPPLY a `PosetDimension chainR dW`; the slice-1 explicit `chain2_dim1 : PosetDimension chainR 1` is the clean witness. Then the conclusion `1 = Nat.max 1 0` is `reflexivity`/`lia`. Wrap as `exists 1; split; [exact (inhabits chain2_dim1) | reflexivity]` and separately invoke `fin_fully_sync_dimension` to VALIDATE consistency, or just use it to derive `dW=1`.)

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 360 execution/FinFullySyncDimExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/FinFullySyncDimExamples.v && git commit -m "test(execution): all-singleton chain exact n-way dimension = 1"`.

---

## Task Y5: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `FinFullySyncDim FullySyncDimExact` to the `Require Export` line in `execution/Execution.v` (NOT the examples).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 900 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions fin_fully_sync_dimension.` to `FinFullySyncDim.v`, `Print Assumptions fully_sync_dimension.` to `FullySyncDimExact.v`, `Print Assumptions chain_all_singleton_dim.` to `FinFullySyncDimExamples.v`; build each; read the axiom blocks (expect only standard classical/choice axioms); then `git checkout -- execution/FinFullySyncDim.v execution/FullySyncDimExact.v execution/FinFullySyncDimExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add an "Exact n-way fully-synchronized dimension" subsection: `singleton_union_one_block`, `fin_fully_sync_dimension` (generic: `dim = max(1, fold dims)` for ≥2-elt), `fully_sync_dimension` (ExecPoset), `chain_all_singleton_dim`. Note it's slice 2 (completing the exact n-way `dim=max`). Match existing table style.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export exact n-way fully-sync dimension; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (generic theorem) → Y1 (`singleton_union_one_block`) + Y2 (aux + `fin_fully_sync_dimension`); Component 2 (restriction helper) → reuses `restricted_block_dim2` (already general in `d` — NO new lemma, noted in Y2); Component 3 (ExecPoset) → Y3; Component 4 (example) → Y4; wiring/testing/audit → Y0 + Y5. All mapped.
- **Crux:** Y2's carrier-quantified aux with the THREE-way split (`pre=[]` / ≥2-L IH / singleton-L). The singleton-L case depends on Y1, which (per the inline correction in Y2 Step 2) must NOT require full `fin_ordinal_partition R pre` (unsatisfiable for a prefix — same trap as H3); Y1's hypotheses use the prefix's nonempty+disjoint clauses directly. **Y1 must be stated that way from the start** (see Y1 Step 1 — adjust its `fin_ordinal_partition R pre` hypothesis to the nonempty+disjoint+per-block-dims form before implementing).
- **Heavy reuse de-risks Y2:** `fin_prefix_barrier`, `fin_prefix_restricted_partition`, `restricted_block_dim2`, `fin_block_iso_full`, the `exists_last` peel — all confirmed present in `FinFullySync.v`. Y2 is `fin_fully_sync_dim_le2_aux` with the exact conclusion.
- **Name consistency:** `singleton_union_one_block`, `fin_fully_sync_dimension`(`_aux`), `fully_sync_dimension`, `chain_all_singleton_dim`; `fold_right Nat.max 0 dims` throughout.
- **`fold_right_max_app`** (`fold_right Nat.max 0 (l ++ [x]) = Nat.max (fold_right Nat.max 0 l) x`): not guaranteed in Stdlib; prove a 3-line local lemma by `induction l` if `Search` finds nothing.
- **Reused (confirmed):** `restricted_block_dim2`/`fin_prefix_barrier`/`fin_prefix_restricted_partition`/`fin_block_iso_full`/`fin_sub_order_finite`/`restrict_block`/`nth_map_restrict` (FinFullySync); `fin_barrier_dimension_full`/`fin_singleton_dim0` (FinExtremumDim); `fin_dim_exists`/`fin_posdim_unique` (Surgery/FinPosetDim); `dim_ge_1_of_two` (AntichainComplement); `fully_sync_pairwise_below`/`IsFullySync`/`sub_order`/`ep_size_ok` (FullySync/Ordinal/Poset); slice-1 `chain2_R`/`chain2_dim1` pattern (FinExtremumDimExamples).
- **Out of scope:** `E_min` nontrivial cross-check (task #66).

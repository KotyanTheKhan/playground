# Execution Barrier dim≤2 Lever — Implementation Plan (B part 2 follow-up)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. Proof bodies give a strategy. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Prove the all-cases binary dim≤2 lever `barrier_dim_le2` (a barrier with both blocks dim≤2 ⟹ whole dim≤2, no `dim>0` hypothesis), by composing `barrier_dimension` with the extremum reductions for singleton blocks.

**Architecture:** Two new modules in the `Execution` theory: `BarrierDim2` (the `block_dim0_global_min/max` bridge + `barrier_dim_le2`) and `BarrierDim2Examples` (concrete `E_min` instance, test-only).

**Tech Stack:** Coq/Rocq 9.1; `Dimension` (`DimDefs`); execution `Poset`, `DimBridge`, `Frontier`, `Ordinal`, `ExtremumReduction`, `FrontierExamples`/`DimExamples`/`ReductionExamples`; Stdlib `Ensembles`/`Finite_sets`/`FunctionalExtensionality`/`PropExtensionality`/`ProofIrrelevance`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/BarrierDim2.v` | `block_dim0_global_min`, `block_dim0_global_max`, `barrier_dim_le2`. |
| `execution/BarrierDim2Examples.v` | `E_min_dim_le_2_via_barrier` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `block_dim0_global_min`, `block_dim0_global_max`, `barrier_dim_le2`, `E_min_dim_le_2_via_barrier`.

---

## Task F0: Scaffold

**Files:** create `execution/BarrierDim2.v`, `execution/BarrierDim2Examples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the two stubs.
- [ ] **Step 2:** Add `BarrierDim2`, `BarrierDim2Examples` to the `(modules …)` list in `execution/dune`.
- [ ] **Step 3:** Add the two `.v` paths to `_CoqProject` (after the extremum-reduction entries).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/BarrierDim2.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/BarrierDim2.v execution/BarrierDim2Examples.v execution/dune _CoqProject
git commit -m "scaffold execution barrier-dim2 modules"
```

---

## Task F1: The bridge helpers + `barrier_dim_le2` (`BarrierDim2.v`)

**Files:** `execution/BarrierDim2.v`

- [ ] **Step 1: Imports + `block_dim0_global_min`**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal ExtremumReduction.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Lemma block_dim0_global_min :
  forall E L U, IsBarrier E L U ->
    PosetDimension (sub_order E L) 0 ->
    exists m, IsGlobalMin E m /\ (forall x, Ensembles.In _ U x <-> x <> m).
```
Strategy:
- Destruct `IsBarrier E L U` as `[Hcov [Hdisj [HinhL [HinhU Hbelow]]]]`. `HinhL : exists x, In L x` gives a witness `m0` with `Hm0 : In L m0`. The carrier element `m := m0`.
- From `PosetDimension (sub_order E L) 0`: `dimension_cardinality` gives `cardinal _ (dimension_realizer _) 0`; `cardinalO_empty` ⟹ realizer is `Empty_set`; then `realizer_intersection` ⟹ for all sub-poset elements `a b`, `sub_order E L a b` (vacuous `forall L' ∈ ∅`). So `sub_order E L` is universal on `{z | In L z}`.
- All `L` elements equal `m`: for `x` with `Hx : In L x`, the sub-poset elements `exist _ x Hx` and `exist _ m Hm0` are related both ways (universal) ⟹ `poset_antisym` (of `sub_order_poset`) ⟹ `exist _ x Hx = exist _ m Hm0` ⟹ `x = m` (`f_equal proj1_sig` / `proj1_sig`).
- `IsGlobalMin E m`: `intro x`. By `Hcov x`: `In L x ⟹ x = m ⟹ ep_order E m m` (`poset_refl`); `In U x ⟹ Hbelow m x Hm0 (that) : ep_order E m x` (`m ∈ L`).
- `forall x, In U x <-> x <> m`: (`->`) `In U x`; if `x = m` then `In L m` (Hm0) and `In U m` contradict `Hdisj m`; so `x <> m`. (`<-`) `x <> m`; by `Hcov x`, `In L x` would give `x = m` (all L = m) — contra; so `In U x`.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/BarrierDim2.vo 2`. Exit 0.

- [ ] **Step 3: `block_dim0_global_max`** (dual)

```coq
Lemma block_dim0_global_max :
  forall E L U, IsBarrier E L U ->
    PosetDimension (sub_order E U) 0 ->
    exists m, IsGlobalMax E m /\ (forall x, Ensembles.In _ L x <-> x <> m).
```
Same structure with `U` the singleton: `m ∈ U`; all `U` elements `= m`; `IsGlobalMax E m` (`intro x`; `In U x ⟹ x=m ⟹` refl; `In L x ⟹ Hbelow x m … : ep_order E x m`); `L = {x | x <> m}`.

- [ ] **Step 4: `barrier_dim_le2`**

```coq
Lemma barrier_dim_le2 :
  forall E L U, IsBarrier E L U ->
    (exists d, inhabited (PosetDimension (sub_order E L) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension (sub_order E U) d) /\ d <= 2) ->
    (exists d, exec_has_dimension E d /\ d <= 2).
```
Strategy: `intros E L U HB [dL [ [HdL] HleL ]] [dU [ [HdU] HleU ]]`. `destruct dL as [|dL']`.
- **`dL = 0` case:** `destruct (block_dim0_global_min E L U HB HdL) as [m [Hmin HUeq]]`.
  - Rewrite `U` to `(fun x => x <> m)`: `assert (HUfun : U = (fun x => x <> m))` by `apply functional_extensionality; intro x; apply propositional_extensionality; exact (HUeq x)`. `rewrite HUfun in HdU` (so `HdU : PosetDimension (sub_order E (fun x => x <> m)) dU`).
  - Apply `remove_min_preserves_dim2 E m Hmin`. Its `->` (proj1, `block dim2 -> E dim2`): provide `(exists d, inhabited (PosetDimension (sub_order E (fun x => x <> m)) d) /\ d <= 2)` = `exists dU; split; [exact (inhabits HdU) | exact HleU]`. Result: `exists d, exec_has_dimension E d /\ d <= 2`. (Confirm the iff orientation with the lemma; use `proj1` of the iff if it is `(block dim2) <-> (E dim2)`.)
- **`dL = S dL'` (so `0 < dL`), `dU = 0` case:** `destruct dU as [|dU']`; for `dU = 0`: symmetric via `block_dim0_global_max` + `remove_max_preserves_dim2` (rewrite `L` to `(fun x => x <> m)`, supply the `L`-hypothesis `exists (S dL'); split; [exact (inhabits HdL) | exact HleL]`).
- **`dL = S dL'`, `dU = S dU'` (both `> 0`) case:** `destruct (exec_dimension_exists E) as [d [Hd]]`. `pose proof (barrier_dimension E L U HB (S dL') (S dU') d HdL HdU Hd (Nat.lt_0_succ _) (Nat.lt_0_succ _)) as Hmax` (`Hmax : d = Nat.max (S dL') (S dU')`). `exists d; split; [exact (inhabits Hd) | rewrite Hmax; lia]` (with `HleL : S dL' <= 2`, `HleU : S dU' <= 2`, `Nat.max … <= 2` by `lia`).

(Confirm `barrier_dimension`'s exact argument order with `About barrier_dimension`. `cardinalO_empty` and `realizer_intersection`/`dimension_realizer`/`dimension_cardinality` are as used in `DimBridge.v`'s `exec_dim_ge_2`.)

- [ ] **Step 5: Build** — `bash .claude/scripts/timed-build.sh 360 execution/BarrierDim2.vo 2`. Exit 0; `grep -nE "Admitted|admit|Axiom" execution/BarrierDim2.v` empty.
- [ ] **Step 6: Commit** — `git add execution/BarrierDim2.v && git commit -m "feat(execution): all-cases binary barrier dim<=2 lever"`.

---

## Task F2: Concrete `E_min` instance (`BarrierDim2Examples.v`)

**Files:** `execution/BarrierDim2Examples.v`

- [ ] **Step 1: The example**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              Reduction ExtremumReduction DimExamples FrontierExamples BarrierDim2.

Example E_min_dim_le_2_via_barrier :
  exists d, exec_has_dimension E_min d /\ d <= 2.
```
Strategy: `apply (barrier_dim_le2 E_min Lmin Umin E_min_barrier)` (`Lmin`/`Umin`/`E_min_barrier` from `FrontierExamples.v`). Two goals — block `dim ≤ 2` for `Lmin` and `Umin`:
- For each block `S ∈ {Lmin, Umin}`: `exists d, inhabited (PosetDimension (sub_order E_min S) d) /\ d <= 2`. Obtain via `subposet_reduces_dim (ep_carrier E_min) (ep_order E_min) S` (gives `ReducesDim (sub_order E_min S) (ep_order E_min)`) + `reduces_dim2`, with:
  - block-dimension existence (`exists dR, inhabited (PosetDimension (sub_order E_min S) dR)`): from `subposet_dimension_le (ep_order E_min) S 2 Hd2` where `Hd2 : PosetDimension (ep_order E_min) 2` from `E_min_dim_2` (`destruct E_min_dim_2 as [Hd2]`) — take its `inhabited` component;
  - the `E`-side `dim ≤ 2`: `exists 2; split; [exact E_min_dim_2 | lia]`.
  Package the two block goals; this re-uses `E_min_dim_2` as ground truth (acceptable for a demonstration that the lever applies — `E_min`'s only barrier is this singleton one).

Note: `Lmin`/`Umin` are `Ensemble (ep_carrier E_min)`; `barrier_dim_le2` expects the block hypotheses about `sub_order E_min Lmin` / `sub_order E_min Umin`, matching `subposet_reduces_dim`'s subposet form definitionally.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/BarrierDim2Examples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/BarrierDim2Examples.v && git commit -m "test(execution): E_min dim<=2 via all-cases barrier lever"`.

---

## Task F3: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `BarrierDim2` to the `Require Export` line in `execution/Execution.v` (NOT the examples).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 600 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions barrier_dim_le2.` to `execution/BarrierDim2.v` and `Print Assumptions E_min_dim_le_2_via_barrier.` to `execution/BarrierDim2Examples.v`; build, read the axiom blocks (expect only standard classical/choice axioms), then `git checkout -- execution/BarrierDim2.v execution/BarrierDim2Examples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "Barrier dim≤2 lever" subsection: `block_dim0_global_min`/`block_dim0_global_max`, `barrier_dim_le2` (BarrierDim2.v); `E_min_dim_le_2_via_barrier` (BarrierDim2Examples.v). Match existing table style.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export barrier dim<=2 lever; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (bridge) → F1 Steps 1–3; Component 2 (`barrier_dim_le2`) → F1 Step 4; Component 3 (concrete) → F2; wiring/testing/audit → F0 + F3. All mapped.
- **The bridge `block_dim0_global_*` (F1) is the only real proof**; `barrier_dim_le2` is a case-split composing `barrier_dimension` + `remove_min/max_preserves_dim2`.
- **Name consistency:** `block_dim0_global_min`/`block_dim0_global_max`, `barrier_dim_le2`, `E_min_dim_le_2_via_barrier`; `IsBarrier` destructured as `[Hcov [Hdisj [HinhL [HinhU Hbelow]]]]`; `sub_order E S`.
- **Reused (confirmed present):** `barrier_dimension`/`sub_order`/`posdim_unique` (Ordinal), `remove_min/max_preserves_dim2`/`IsGlobalMin`/`IsGlobalMax` (ExtremumReduction), `IsBarrier` (Frontier), `E_min_barrier`/`Lmin`/`Umin` (FrontierExamples), `E_min_dim_2` (DimExamples), `subposet_reduces_dim`/`reduces_dim2` (Reduction), `cardinalO_empty`/`subposet_dimension_le` (Dimension), `exec_dimension_exists` (DimBridge).
- **Execution-time checks:** `About barrier_dimension` (arg order + the `0<dL`/`0<dU` positions), `remove_min_preserves_dim2` iff orientation (`proj1` vs `proj2`), `cardinalO_empty` name.

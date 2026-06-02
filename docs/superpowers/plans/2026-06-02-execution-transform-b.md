# Transformation B Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development.

**Goal:** Formalize Transformation B's core — a 2-process (2-chain-covered) block has dim ≤ 2 — and frame it as a dimension-property-preserving block swap in a fully-sync execution.

**Architecture:** `execution/TransformB.v` — the general `two_chain_cover_dim_le2` (via `width_exists` + `dimension_le_width` + pigeonhole), a concrete 2-process block `B2` (dim ≤ 2), its `B2_simplified` chain, and `transform_B_preserves_dim2`. `execution/TransformBExamples.v` — the concrete equal-bound example.

**Tech Stack:** Rocq 9.1; Dilworth/dimension libraries (`Dilworth.Definitions`, `Dilworth.WidthLowerBound`, `Dimension.WidthBound`, `Dimension.WidthExists`), `DimTwoGeneric` (`dim2_record`), `ChainDim` (`chain_dim_1`), `FullySyncDim2` (`fully_sync_dim_le2`). Builds via the wrapper.

---

## Task TB0: Scaffold
**Files:** create `execution/TransformB.v`, `execution/TransformBExamples.v`; modify `execution/dune`, `_CoqProject`.
- [ ] **Step 1: `execution/TransformB.v`**
```coq
(* Transformation B: a 2-process (2-chain-covered) block has dimension <= 2;
   block replacement preserves the fully-sync execution's dim <= 2. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                           ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems WidthBound WidthExists.
From Dilworth Require Import Definitions WidthLowerBound.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 DimTwoGeneric ChainDim.
```
- [ ] **Step 2: `execution/TransformBExamples.v`**
```coq
(* Transformation B example: a concrete 2-process block and its simplification,
   both dim <= 2 (test-only). *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                           ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import TransformB DimTwoGeneric ChainDim.
```
- [ ] **Step 3:** Confirm module names with a quick build; `Dilworth.Definitions`/`Dilworth.WidthLowerBound`, `Dimension.WidthBound`/`WidthExists` are the `-R` logical names for `posets/dilworth/*` and `posets/dimension/*` (the dune `(theories … Dilworth Dimension …)` provides them — verify via the scaffold build; if an import fails, `grep -rn "dimension_le_width\|width_exists\|pigeonhole_chains_antichains\|Class IsChain" posets/` and import the file that defines it under its actual logical name).
- [ ] **Step 4:** add `TransformB`, `TransformBExamples` to `execution/dune` + `_CoqProject` (after `WindowSyncExamples`).
- [ ] **Step 5: build** `bash .claude/scripts/timed-build.sh 120 execution/TransformBExamples.vo 2` → EXIT=0.
- [ ] **Step 6: commit** `git add -A && git commit -m "chore(execution): scaffold TransformB modules"`.

---

## Task TB1: the faithful general lemma (`TransformB.v`)
Append. **This is the crux — verify every cross-library signature with `About`/`Print` before relying on it.**

First confirm (run these, adapt the proof to what they report):
- `About dimension_le_width.` — expect `forall {A}{R}{HR}` (section-generalized) then `forall n d w, cardinal A (Full_set A) n -> PosetDimension R d -> Width R (Full_set A) w -> d <= w`.
- `About width_exists.` — `forall n, cardinal A (Full_set A) n -> Inhabited A (Full_set A) -> exists w, inhabited (Width R (Full_set A) w)`.
- `About pigeonhole_chains_antichains.` and `Print IsChainCover. Print IsChain. Print IsAntichain. Print Width. Print IsLargestAntichain.` — to read exact field names.

```coq
Lemma two_chain_cover_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (C0 C1 : Ensemble A) (n : nat),
    cardinal A (Full_set A) n -> Inhabited A (Full_set A) ->
    IsChain R C0 -> IsChain R C1 ->
    (forall x, Ensembles.In A (Full_set A) x ->
        Ensembles.In A C0 x \/ Ensembles.In A C1 x) ->
    forall d, PosetDimension R d -> d <= 2.
Proof.
  intros A R HR C0 C1 n Hcard Hinhab HC0 HC1 Hcov d Hdim.
  destruct (width_exists R n Hcard Hinhab) as [w [HW]].
  pose proof (dimension_le_width R n d w Hcard Hdim HW) as Hdw.
  assert (Hw2 : w <= 2).
  { destruct (le_lt_dec w 2) as [Hle | Hgt]; [exact Hle | exfalso].
    (* the largest antichain has w >= 3 elements but is covered by 2 chains *)
    set (cover := fun c : Ensemble A => c = C0 \/ c = C1).
    assert (Hcc : IsChainCover R (Full_set A) cover).
    { constructor.
      - intros c [-> | ->]; assumption.                 (* chains *)
      - intros c _ x _. constructor.                    (* included in Full_set *)
      - intros x _. (* covered *) destruct (Hcov x (Full_intro _ _)) as [H0 | H1];
          [ exists C0; split; [left; reflexivity | exact H0]
          | exists C1; split; [right; reflexivity | exact H1] ]. }
    (* the largest antichain `la` of size w *)
    (* extract from HW : Width R (Full_set) w — la, IsAntichain la, Included la Full, cardinal la w *)
    (* (field names per `Print Width` / `Print IsLargestAntichain`) *)
    destruct HW as [la Hla].
    (* cover cardinality: 1 or 2, in both cases < w (since w >= 3) *)
    destruct (classic (C0 = C1)) as [Heq | Hne].
    - (* cover = {C0}, cardinal 1 *)
      assert (Hcov1 : cardinal (Ensemble A) cover 1).
      { replace cover with (Add (Ensemble A) (Empty_set _) C0).
        - apply card_add; [apply card_empty | intro Hb; destruct Hb].
        - apply Extensionality_Ensembles; split.
          + intros c [c0 Hc0 | c0 Hc0]; [destruct Hc0 | apply Singleton_inv in Hc0; left; symmetry; exact Hc0].
          + intros c [-> | ->]; [right; constructor | rewrite Heq; right; constructor]. }
      (* pigeonhole: w > 1 antichain elements into 1 chain => two distinct in a chain => comparable => eq *)
      (* use pigeonhole_chains_antichains Hcc <la is antichain> <Included> Hcov1 <cardinal la w> (w>1) *)
      admit_REPLACE.
    - (* cover = {C0,C1}, cardinal 2 *)
      assert (Hcov2 : cardinal (Ensemble A) cover 2).
      { replace cover with (Add (Ensemble A) (Add (Ensemble A) (Empty_set _) C0) C1).
        - apply card_add; [ apply card_add; [apply card_empty | intro Hb; destruct Hb]
                          | intro Hb; destruct Hb as [c Hb|c Hb]; [destruct Hb | apply Singleton_inv in Hb; apply Hne; symmetry; exact Hb] ].
        - apply Extensionality_Ensembles; split.
          + intros c [-> | ->]; [left; right; constructor | right; constructor].
          + intros c [c0 [c1 Hc1|c1 Hc1] | c0 Hc0];
              [ destruct Hc1 | apply Singleton_inv in Hc1; left; symmetry; exact Hc1
              | apply Singleton_inv in Hc0; right; symmetry; exact Hc0 ]. }
      admit_REPLACE. }
  lia.
Qed.
```
**The two `admit_REPLACE` are placeholders — REPLACE with the real pigeonhole contradiction (NO `Admitted`/`admit` in the final file).** Each: apply `pigeonhole_chains_antichains R (Full_set A) cover la <ncov> w Hcc <la_is_antichain> <la_included> <Hcov1/Hcov2> <cardinal la w> <w > ncov>` to get `[x [y [c [Hx [Hy [Hc [Hcx [Hcy Hxy]]]]]]]]`; `c` is a chain (`Hcc.chain_cover_chains c Hc`); `x,y ∈ c` ⟹ `R x y \/ R y x` (chain); `x,y ∈ la` an antichain ⟹ `x = y` (`antichain_incomparable`); contradicts `Hxy : x <> y`. The `w > ncov` is `lia` from `Hgt : w > 2 ≥ ncov`. Extract `la`'s antichain/included/cardinal facts from `Hla` per the real `IsLargestAntichain` field names (`Print IsLargestAntichain`).

ALTERNATIVE if the `Width`/`IsLargestAntichain`/cover plumbing fights you: prove a direct
`antichain_le2` (`forall anti, IsAntichain R anti -> Included A anti (Full_set A) -> forall m, cardinal A anti m -> m <= 2`) by `cardinal_invert`-extracting 3 distinct elements from `m ≥ 3`, pigeonholing into `C0`/`C1` (each `In Full_set` ⟹ `In C0 \/ In C1`, 3 into 2 ⟹ two share a chain), deriving comparability ⟹ equality ⟹ contradiction; then bound `w` via `width_la`'s `cardinal … w`. Use whichever closes; the goal is `d <= 2`, axiom-free modulo the libraries' standard axioms.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 360 execution/TransformB.vo 2` → EXIT=0; zero admits.
- [ ] **Commit** `git add execution/TransformB.v && git commit -m "feat(execution): two_chain_cover_dim_le2 (2-process block has dim <= 2)"`.

---

## Task TB2: concrete block + simplification + transformation (`TransformB.v`)
Append.
```coq
(* concrete 2-process block: process 0 chain a0<a1, process 1 chain b0<b1, a's || b's *)
Inductive B2 : Set := a0 | a1 | b0 | b1.
Definition B2_R (x y : B2) : Prop :=
  x = y \/ (x = a0 /\ y = a1) \/ (x = b0 /\ y = b1).

#[export] Instance B2_poset : IsPoset B2 B2_R.
(* constructor; destruct-bash the 4x4 cases; antisym/trans by discriminate/lia-free case work *)

Definition B2_C0 : Ensemble B2 := fun z => z = a0 \/ z = a1.
Definition B2_C1 : Ensemble B2 := fun z => z = b0 \/ z = b1.

Lemma B2_C0_chain : IsChain B2_R B2_C0.   (* both a0<a1: comparable *)
Lemma B2_C1_chain : IsChain B2_R B2_C1.
Lemma B2_Hfin : cardinal B2 (Full_set B2) 4.   (* Add..Add over a0,a1,b0,b1; mirror chain2_Hfin/bcd_Hfin *)
Lemma B2_inhab : Inhabited B2 (Full_set B2).    (* exists a0 *)
Lemma B2_cover : forall x, Ensembles.In B2 (Full_set B2) x -> Ensembles.In B2 B2_C0 x \/ Ensembles.In B2 B2_C1 x.
  (* destruct x; left/right *)

Lemma B2_dim_le2 : forall d, PosetDimension B2_R d -> d <= 2.
Proof.
  apply (two_chain_cover_dim_le2 B2_R B2_C0 B2_C1 4 B2_Hfin B2_inhab
           B2_C0_chain B2_C1_chain B2_cover).
Qed.

(* Transformation B's "one local modification": the simplified block is a single chain. *)
Definition B2s := bool.   (* p0 = false < p1 = true *)
Definition B2s_R (x y : bool) : Prop := x = y \/ (x = false /\ y = true).
(* B2s_R is a total order on 2 elements => dim 1 (chain_dim_1) => <= 2 *)
Lemma B2s_dim_le2 : forall d, PosetDimension B2s_R d -> d <= 2.
  (* dim is unique (posdim_unique) and = 1 (chain_dim_1); or: any realizer => d >= ... ; simplest:
     chain_dim_1 gives PosetDimension B2s_R 1; posdim_unique d 1 => d = 1 <= 2. Check posdim_unique exists. *)

(* The transformation preserves the fully-sync execution's dim <= 2 (= fully_sync_dim_le2). *)
Lemma transform_B_preserves_dim2 :
  forall E blocks,
    IsFullySync E blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension E d /\ d <= 2.
Proof. intros E blocks Hfs Hblk. exact (fully_sync_dim_le2 E blocks Hfs Hblk). Qed.
```
NOTES: prove the small lemmas by case-bashing `B2`'s 4 constructors (`destruct x; …`; `IsPoset` antisym/trans via `destruct`+`discriminate`). `IsChain`'s `chain_comparable` field: `forall x y, In s x -> In s y -> R x y \/ R y x` — for `B2_C0` the elements are `a0,a1`, comparable by `B2_R`. `B2_Hfin`: mirror `chain2_Hfin`/`bcd_Hfin` (`Add` chain + distinctness by `discriminate`). For `B2s_dim_le2`: `chain_dim_1` needs a `Finite`/totality witness — reuse the `chain2_*` bool machinery if importing `FinExtremumDimExamples` is undesirable; simplest is to apply `two_chain_cover_dim_le2` to `B2s` too (C0 = Full, C1 = Empty — a 1-chain cover is a 2-chain cover with one empty chain; `IsChain (Empty_set)` is vacuous). Prefer that uniformity if `chain_dim_1`'s hypotheses are awkward. Confirm `posdim_unique`/`fin_posdim_unique` signature if used.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 300 execution/TransformB.vo 2` → EXIT=0; zero admits.
- [ ] **Commit** `git add execution/TransformB.v && git commit -m "feat(execution): concrete 2-process block + simplification + transform_B_preserves_dim2"`.

---

## Task TB3: examples + wiring + audit
**Files:** `execution/TransformBExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.
- [ ] **Step 1: examples** (append)
```coq
Example B2_dim_le2_demo : forall d, PosetDimension B2_R d -> d <= 2.
Proof. exact B2_dim_le2. Qed.

(* the equal-bound that drives Transformation B: both the 2-process block and its
   simplification have dim <= 2, so swapping one for the other preserves the bound. *)
Example transform_B_equal_bound :
  (forall d, PosetDimension B2_R d -> d <= 2) /\
  (forall d, PosetDimension B2s_R d -> d <= 2).
Proof. split; [exact B2_dim_le2 | exact B2s_dim_le2]. Qed.
```
- [ ] **Step 2: build** `bash .claude/scripts/timed-build.sh 180 execution/TransformBExamples.vo 2` → EXIT=0.
- [ ] **Step 3: export** append `TransformB` to `execution/Execution.v`'s `Require Export` list.
- [ ] **Step 4: whole-project** `bash .claude/scripts/timed-build.sh 1800 @all 4` → EXIT=0.
- [ ] **Step 5: audit** scratch `execution/TransformBAudit.v` (`From Execution Require Import TransformB. Print Assumptions two_chain_cover_dim_le2. Print Assumptions transform_B_preserves_dim2.`), register, build, capture (expected standard classical/proof-irrelevance/choice axioms from the dimension layer; no `admit`), then REMOVE + revert registration.
- [ ] **Step 6: INDEX** add a `#### execution/TransformB.v — Transformation B (2-process block dim ≤ 2)` subsection: `two_chain_cover_dim_le2`, the concrete `B2` block + `B2_dim_le2`, `B2s` simplification, `transform_B_preserves_dim2`; note the honest caveat (paper geometry informal; "critical pairs" formalized as the width≤2 ⟹ dim≤2 bound).
- [ ] **Step 7: commit** `git add execution/TransformBExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): Transformation B example + export + INDEX"`.

---

## Self-Review (vs the spec)
- **Coverage:** general lemma (TB1); concrete block + simplification + preservation (TB2); examples/wiring/audit (TB3). Components 1–4 mapped.
- **Reuse:** `width_exists`/`dimension_le_width`/`pigeonhole_chains_antichains` (libraries); `fully_sync_dim_le2` (existing); `dim2_record`/`chain_dim_1` available as fallbacks.
- **Name consistency:** `two_chain_cover_dim_le2`/`B2`/`B2_R`/`B2_C0`/`B2_C1`/`B2_dim_le2`/`B2s`/`B2s_R`/`B2s_dim_le2`/`transform_B_preserves_dim2` across TB1–TB3.
- **Honest scope:** caveats recorded (informal geometry, critical-pairs-as-dimension-bound); no execution-`sub_order` generic block lemma (bare block + `fully_sync_dim_le2` suffice).
- **No placeholders in the final code:** the two `admit_REPLACE` in TB1 MUST be replaced with the real pigeonhole contradiction; build steps assert zero admits.

# Exact Barrier Dimension — Implementation Plan (exact n-way dim=max, slice 1 of 2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Prove the exact extremum-surgery lemmas (`fin_add_min_dim`/`fin_add_max_dim`: adding a global extremum gives `dim = max(d,1)`) and the binary all-cases `fin_barrier_dimension_full` (`dim = max(1, max(dL,dU))`), on bare finite posets.

**Architecture:** New `execution/FinExtremumDim.v` (the two exact extremum lemmas + the binary barrier-full formula) and `execution/FinExtremumDimExamples.v` (the `E_min` cross-check, test-only). Both build on the slice-1 generic lever chain (`FinPosetDimSurgery`, `FinPosetDim`) and `DimIso`. The exact extremum surgery is a port of `fin_remove_min_dim2`'s backward direction tracking exact cardinality instead of `≤ 2`.

**Tech Stack:** Coq/Rocq 9.1; `Posets` (`PosetClasses`, `FinitePoset`); `Dimension` (`DimDefs`, `Theorems`, `AntichainComplement` for `dim_ge_1_of_two`); execution `DimIso`, `FinPosetDimSurgery`, `FinPosetDim`, and (examples) `Poset`, `Ordinal`, `DimBridge`, `DimExamples`, `FrontierExamples`; Stdlib `Ensembles`/`Finite_sets`/`Finite_sets_facts`/`Image`/`Arith`/`Lia`/`Classical`/`ProofIrrelevance`/`FunctionalExtensionality`/`PropExtensionality`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/FinExtremumDim.v` | `fin_singleton_dim0` (helper), `fin_add_min_dim`, `fin_add_max_dim`, `fin_barrier_dimension_full`. |
| `execution/FinExtremumDimExamples.v` | `dim_block_bcd_2`, `E_min_exact_dim_via_barrier` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `fin_add_min_dim`, `fin_add_max_dim`, `fin_barrier_dimension_full`, `E_min_exact_dim_via_barrier`.

**Section convention** (FinExtremumDim.v): `Section FinExtremumDim. Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (Hfin : Finite A (Full_set A)).` — matching the slice-1 files. Slice-1 names take `R` as a leading explicit arg post-section (`fin_sub_order R S`, `fin_global_min R m`, `fin_lift_min` is `fin_lift_min m LB` — NB `fin_lift_min` does NOT take `R` (its body references `R` only via the section, confirm with `About fin_lift_min`), `fin_barrier_dimension R Hfin …`, `fin_block_dim0_global_min R …`). **Confirm every slice-1 binder with `About` before use.**

**KEY REFERENCE — read first:** `execution/FinPosetDimSurgery.v`'s `fin_remove_min_dim2` proof. Its backward direction (the `d = S d'` branch) already builds `RE := Im _ _ RB (fin_lift_min m)`, proves `IsRealizer R RE`, derives `cardinal RE (S d')` via `cardinal_Im_injective … (fin_lift_min_inj m)`, and finishes `dimension_is_minimum HdE RE (S d') HRE_real HRE_card : dW ≤ S d'`. `fin_add_min_dim`'s `≤` direction is THIS construction, keeping the exact `d` instead of chaining to `≤ 2`.

---

## Task X0: Scaffold

**Files:** create `execution/FinExtremumDim.v`, `execution/FinExtremumDimExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the two stubs.
- [ ] **Step 2:** Add `FinExtremumDim`, `FinExtremumDimExamples` to the `(modules …)` list in `execution/dune` (in that order, after the fully-sync modules).
- [ ] **Step 3:** Add the two `.v` paths to `_CoqProject` (same order, after the fully-sync entries).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/FinExtremumDim.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/FinExtremumDim.v execution/FinExtremumDimExamples.v execution/dune _CoqProject
git commit -m "scaffold exact barrier dimension modules"
```

---

## Task X1: `fin_singleton_dim0` + `fin_add_min_dim` (`FinExtremumDim.v`)

**Files:** `execution/FinExtremumDim.v`

- [ ] **Step 1: Imports, section, and the singleton helper**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim.

Section FinExtremumDim.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  (* A poset with at most one element has dimension 0 (empty realizer). *)
  Lemma fin_singleton_dim0 :
    (forall x y : A, x = y) -> PosetDimension R 0.
End FinExtremumDim.
```
`fin_singleton_dim0` proof (`≤ 1 element ⟹ dim 0`): build `PosetDimension R 0` with `dimension_realizer := Empty_set _`. `IsRealizer R (Empty_set _)`: `realizer_linear` vacuous; `realizer_intersection x y`: forward trivial-over-∅; backward `(forall L ∈ ∅, L x y) -> R x y` — since `x = y` (the hypothesis), `R x y` by `poset_refl` (rewrite `x = y`). `cardinal _ (Empty_set _) 0` by `card_empty`. `dimension_is_minimum` trivially `0 <= n`. (This is the exact `d = 0` ingredient; reuse the `IsRealizer (Empty_set _)` pattern from `DimBridge.v`'s `exec_dim_ge_2` `d=0` case or `fin_small_dim_le_2`.)

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 180 execution/FinExtremumDim.vo 2`. Exit 0.

- [ ] **Step 3: `fin_add_min_dim`**

```coq
Lemma fin_add_min_dim :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (m : A),
    fin_global_min R m ->
    (exists x, x <> m) ->
    forall d, PosetDimension (fin_sub_order R (fun x => x <> m)) d ->
      forall dW, PosetDimension R dW -> dW = Nat.max d 1.
```
(State it OUTSIDE the section so `R`/`Hfin` are explicit, matching how `fin_remove_min_dim2` is callable. Match the slice-1 binder style exactly.)
Proof by `Nat.le_antisymm` (`dW <= max d 1` and `max d 1 <= dW`):
- **`dW <= max d 1`:** `destruct d as [|d']`.
  - `d = S d'`: PORT the backward `d = S d'` branch of `fin_remove_min_dim2` VERBATIM up to the `dimension_is_minimum HdE RE (S d') HRE_real HRE_card : dW <= S d'` step (the realizer `RE := Im _ _ (dimension_realizer Hd_block) (fin_lift_min m)`, `IsRealizer R RE`, `cardinal RE (S d')`). Here `Hd_block : PosetDimension (fin_sub_order R (fun x => x<>m)) (S d')` is the lemma's `d`-hypothesis. Conclude `dW <= S d' = max (S d') 1` (`lia`, since `S d' >= 1`).
  - `d = 0`: the rest `{x | x <> m}` has dimension 0 ⟹ (empty realizer ⟹ `fin_sub_order R (fun x=>x<>m)` universal ⟹) any two non-`m` elements equal. Combined with `m` global min, `R` is TOTAL (any `a b`: if either `= m`, `m` below ⟹ comparable; else both `<> m`, equal ⟹ comparable). Then the singleton realizer `Singleton _ R` (cardinality 1) is a realizer of the total `R`; `dimension_is_minimum HdW (Singleton _ R) 1 … : dW <= 1 = max 0 1`. (Reuse `fin_small_dim_le_2`'s total-order ⟹ size-1-realizer argument — it proves `<= 2` via a singleton realizer of cardinality 1, so it ALREADY gives `<= 1`; lift that sub-argument, or call a sharpened local `fin_total_dim_le_1`.)
- **`max d 1 <= dW`** (`Nat.max_lub`):
  - `d <= dW`: `subposet_dimension_le R (fun x => x <> m) dW HdW` gives `exists dq, inhabited (PosetDimension (fin_sub_order R (fun x=>x<>m)) dq) /\ dq <= dW`. `destruct`; `posdim_unique` (the block's `IsPoset` is `fin_sub_order_poset R (fun x=>x<>m)`) identifies `dq = d` (from the lemma's `d`-hypothesis and `Hinh`). So `d <= dW`.
  - `1 <= dW`: `dim_ge_1_of_two dW HdW (ex_intro … x (ex_intro … m Hxm))` where `Hxm : x <> m` from the `(exists x, x <> m)` hypothesis. (`dim_ge_1_of_two : forall d, PosetDimension R d -> (exists a b, a <> b) -> 1 <= d`; confirm it's in scope from `AntichainComplement`.)

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinExtremumDim.vo 1`. Exit 0; zero admits. If 124, factor the `≤`-surgery into a helper `fin_add_min_dim_le`.
- [ ] **Step 5: Commit** — `git add execution/FinExtremumDim.v && git commit -m "feat(execution): exact dimension of adding a global minimum"`.

---

## Task X2: `fin_add_max_dim` (`FinExtremumDim.v`)

**Files:** `execution/FinExtremumDim.v` (extend)

- [ ] **Step 1: `fin_add_max_dim`** — the dual of `fin_add_min_dim` (place `m` at the top via `fin_lift_max`).

```coq
Lemma fin_add_max_dim :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (m : A),
    fin_global_max R m ->
    (exists x, x <> m) ->
    forall d, PosetDimension (fin_sub_order R (fun x => x <> m)) d ->
      forall dW, PosetDimension R dW -> dW = Nat.max d 1.
```
Port `fin_add_min_dim`'s proof with `fin_global_min ↦ fin_global_max`, `fin_lift_min ↦ fin_lift_max`, `fin_lift_min_is_linext ↦ fin_lift_max_is_linext`, `fin_lift_min_inj ↦ fin_lift_max_inj` (all from `FinPosetDimSurgery.v` — confirm names with `Search fin_lift_max`). The `≥` direction is identical (subposet + `dim_ge_1_of_two`). The `d = 0` total-order argument is the same (`R` total). The `Im (fin_lift_max m)` realizer construction mirrors `fin_remove_max_dim2`'s backward direction — read that proof in `FinPosetDimSurgery.v` and port the exact-cardinality version.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinExtremumDim.vo 1`. Exit 0; zero admits. If the file exceeds ~500 lines or times out, MOVE `fin_add_max_dim` into a new file `execution/FinExtremumDimMax.v` (`From Execution Require Import FinExtremumDim.`; same `Section` context; wire dune + `_CoqProject`); report if you split.
- [ ] **Step 3: Commit** — `git add execution/FinExtremumDim.v && git commit -m "feat(execution): exact dimension of adding a global maximum"`.

---

## Task X3: `fin_barrier_dimension_full` (`FinExtremumDim.v`)

**Files:** `execution/FinExtremumDim.v` (extend)

- [ ] **Step 1: The binary exact barrier formula**

```coq
Lemma fin_barrier_dimension_full :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (L U : Ensemble A),
    fin_is_barrier R L U ->
    forall dL dU dW,
      PosetDimension (fin_sub_order R L) dL ->
      PosetDimension (fin_sub_order R U) dU ->
      PosetDimension R dW ->
      dW = Nat.max 1 (Nat.max dL dU).
```
Proof by case on `dL`, then `dU` (mirrors `fin_barrier_dim_le2`'s structure):
- `intros … HB dL dU dW HdL HdU HdW`. `destruct dL as [|dL'].`
- **`dL = 0`:** `fin_block_dim0_global_min R L U HB HdL` gives `[m [Hmin HUeq]]` (`Hmin : fin_global_min R m`, `HUeq : forall x, In U x <-> x <> m`).
  - `assert (HUfun : U = (fun x => x <> m))` by `functional_extensionality` + `propositional_extensionality` from `HUeq`. `rewrite HUfun in HdU` ⟹ `HdU : PosetDimension (fin_sub_order R (fun x=>x<>m)) dU`.
  - `exists x, x <> m`: from `fin_is_barrier`'s `U`-inhabited (a `y ∈ U`, and `In U y <-> y <> m` gives `y <> m`).
  - `fin_add_min_dim R Hfin m Hmin (that) dU dW HdU HdW : dW = Nat.max dU 1`. Conclude `Nat.max 1 (Nat.max 0 dU) = Nat.max 1 dU = Nat.max dU 1 = dW` (`lia`).
- **`dL = S dL'`:** `destruct dU as [|dU'].`
  - **`dU = 0`:** symmetric — `fin_block_dim0_global_max R L U HB HdU` gives `m` (global max) with `L = {x | x <> m}`; rewrite `L` in `HdL`; `exists x, x<>m` from `L`-inhabited; `fin_add_max_dim R Hfin m Hmax (that) dL dW HdL' HdW : dW = Nat.max dL 1` (where `dL = S dL'`); `lia` to `Nat.max 1 (Nat.max (S dL') 0) = dW`.
  - **`dU = S dU'`** (both `> 0`): `fin_barrier_dimension R Hfin L U HB (S dL') (S dU') dW HdL HdU HdW (Nat.lt_0_succ _)(Nat.lt_0_succ _) : dW = Nat.max (S dL') (S dU')`; conclude `= Nat.max 1 (Nat.max (S dL')(S dU'))` (`lia`, since `Nat.max (S _)(S _) >= 1`).

(Confirm `fin_barrier_dimension`'s arg order and `fin_block_dim0_global_min/max`'s exact output with `About`.)

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 480 execution/FinExtremumDim.vo 1`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/FinExtremumDim.v && git commit -m "feat(execution): all-cases binary exact barrier dimension"`.

---

## Task X4: `E_min` cross-check (`FinExtremumDimExamples.v`)

**Files:** `execution/FinExtremumDimExamples.v`

`E_min` (4 events `a=(0,0), b=(0,1), c=(1,0), d=(1,1)`; `a` global min; `Lmin = {a}`, `Umin = {b,c,d}`). The `dL = 0` / `fin_add_min_dim` path.

- [ ] **Step 1: `dim_block_bcd_2` — the `{b,c,d}` block has dimension exactly 2**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimIso Ordinal
                              FinPosetDimSurgery FinPosetDim FinExtremumDim
                              DimExamples FrontierExamples.

#[local] Existing Instance hb_IsPoset.

Lemma dim_block_bcd_2 :
  PosetDimension (fin_sub_order (ep_order E_min) Umin) 2.
```
Strategy: `fin_sub_order (ep_order E_min) Umin` is definitionally `sub_order E_min Umin`, the order on `{z | proj1_sig z <> (0,0)}` = `{b,c,d}` with `c < d`, `b` incomparable. Prove `PosetDimension … 2` by EXPLICIT 2-realizer, mirroring `DimExamples.v`'s `E_min_dim_2` / `E_n3_dim_2` technique:
- two injective-key linear extensions `K1`, `K2` on the 3 block events (e.g. `K1: b<c<d`, `K2: c<d<b`) whose intersection is the block order (the comparable pair `c<d` agreed, the incomparable `b`–`c`, `b`–`d` disagreed);
- build the size-2 realizer `{K1,K2}`; `IsRealizer`; `cardinal … 2`; `dimension_is_minimum` for `<= 2`; `dim >= 2` from an incomparable pair (`b`,`c`) via `exec_dim_ge_2`-style (or `dim_ge_1_of_two` is only `>=1`; for `>=2` exhibit the incomparable pair and reuse the explicit-realizer minimality, OR show no size-1 realizer exists because the order isn't total).
This is a real ~80-150 line explicit-realizer proof. READ `DimExamples.v` (`E_min_dim_2`, the `valid_event_min_cases`/`eq_ev_*` helpers) and reuse its scaffolding. **FALLBACK:** if this overruns, REPLACE the whole example with the cheap 2-chain (Step 3 alternative) and skip `dim_block_bcd_2`.

- [ ] **Step 2: `E_min_exact_dim_via_barrier`**

```coq
Example E_min_exact_dim_via_barrier :
  exists dW, PosetDimension (ep_order E_min) dW /\ dW = 2.
```
Strategy: `Hfin` from `ep_size_ok E_min` (`cardinal_finite`). `dim Lmin = 0`: `fin_singleton_dim0 (fin_sub_order (ep_order E_min) Lmin) <all-block-elements-equal>` — `Lmin = {a}` has one element, so any two `{z|In Lmin z}` are equal (`proj1_sig = (0,0)` for both + `proof_irrelevance`). Get `HdL : PosetDimension (fin_sub_order (ep_order E_min) Lmin) 0`. `HdU := dim_block_bcd_2 : PosetDimension (fin_sub_order (ep_order E_min) Umin) 2`. Some `dW` with `PosetDimension (ep_order E_min) dW` from `fin_dim_exists` (or `E_min_dim_2`). `fin_barrier_dimension_full (ep_order E_min) Hfin Lmin Umin Hbar 0 2 dW HdL HdU HdW : dW = Nat.max 1 (Nat.max 0 2) = 2`. (`Hbar : fin_is_barrier (ep_order E_min) Lmin Umin` from `E_min_barrier` — reassemble the 5 conjuncts as in `FinFullySyncExamples`/`FinPosetDimExamples` if not definitional.) `exists dW; split; [exact HdW | exact (that = 2)]`.

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 360 execution/FinExtremumDimExamples.vo 2`. Exit 0; zero admits.
  - **Fallback (if `dim_block_bcd_2` is intractable):** replace the file's content with a 2-element-chain example: a concrete 2-element `ExecPoset` (or a bare finite poset) `{m, m'}` with `m < m'`, `dim = max(0,1) = 1` via `fin_add_min_dim` with `d = 0`. State `Example chain2_exact_dim : <that poset> dimension = 1`. This still exercises `fin_add_min_dim` (the new lemma) on the singleton-rest path, just without the `E_min` cross-check. Document the swap in the commit message.
- [ ] **Step 4: Commit** — `git add execution/FinExtremumDimExamples.v && git commit -m "test(execution): E_min exact dimension via barrier (or 2-chain fallback)"`.

---

## Task X5: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `FinExtremumDim` to the `Require Export` line in `execution/Execution.v` (and `FinExtremumDimMax` if X2 split it); NOT the examples.
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 900 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions fin_barrier_dimension_full.` to `FinExtremumDim.v` and `Print Assumptions E_min_exact_dim_via_barrier.` (or the fallback name) to `FinExtremumDimExamples.v`; build each; read the axiom blocks (expect only standard classical/choice axioms); then `git checkout -- execution/FinExtremumDim.v execution/FinExtremumDimExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add an "Exact barrier dimension" subsection: `fin_add_min_dim`/`fin_add_max_dim` (adding a global extremum gives `dim = max(d,1)`), `fin_barrier_dimension_full` (`dim = max(1, max(dL,dU))` for a barrier), `E_min_exact_dim_via_barrier`. Note this is slice 1 of the exact n-way `dim = max`. Match existing table style.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export exact barrier dimension; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (exact extremum) → X1 (`fin_singleton_dim0`, `fin_add_min_dim`) + X2 (`fin_add_max_dim`); Component 2 (binary barrier-full) → X3; Component 3 (concrete) → X4; wiring/testing/audit → X0 + X5. All mapped.
- **The `≤`-direction surgery (X1/X2) is a PORT** of `fin_remove_min_dim2`/`fin_remove_max_dim2`'s already-proven backward direction, keeping exact cardinality `d` instead of chaining to `≤ 2`. The subagent must READ those proofs first; this de-risks the heaviest step.
- **The `(exists x, x <> m)` hypothesis is load-bearing** (without it the singleton-`R` case `dW=0` vs `max(0,1)=1` breaks). It is supplied in `fin_barrier_dimension_full` from `fin_is_barrier`'s block-inhabited fields.
- **Highest-risk item is X4's `dim_block_bcd_2`** (an exact `dim = 2` explicit-realizer proof) — explicitly fallback-able to a 2-chain example, so it cannot block the slice.
- **Name consistency:** `fin_add_min_dim`/`fin_add_max_dim` (`dim = max(d,1)`), `fin_barrier_dimension_full` (`dim = max(1, max(dL,dU))`), `fin_singleton_dim0`, `dim_block_bcd_2`, `E_min_exact_dim_via_barrier`.
- **Reused (confirmed present):** `fin_lift_min/max`(+`_is_linext`/`_inj`), `fin_global_min/max`, `fin_sub_order`, `fin_sub_order_poset`, `fin_dim_exists`, `fin_small_dim_le_2` (Surgery); `fin_is_barrier`, `fin_block_dim0_global_min/max`, `fin_barrier_dimension` (FinPosetDim); `dimension_iso` (DimIso); `dim_ge_1_of_two` (AntichainComplement), `subposet_dimension_le`, `posdim_unique`, `cardinal_Im_injective`, `cardinalO_empty`, `card_empty` (Dimension/Stdlib); `E_min`/`E_min_dim_2`/`Lmin`/`Umin`/`E_min_barrier`/`ep_size_ok`/`valid_event_min_cases` (examples).
- **Execution-time first step:** `About fin_lift_min`, `About fin_remove_min_dim2`, `About fin_barrier_dimension`, `About fin_block_dim0_global_min`, `About dim_ge_1_of_two` — confirm binder layouts before writing X1/X3.

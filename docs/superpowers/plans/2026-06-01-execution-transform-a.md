# Transformation A (Synchronization-Square Contraction) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Formalize Transformation A (synchronization-square contraction) as a dimension-preserving block replacement: a fully-synchronized execution and the one with a block contracted (sync-square ↔ 2-point, both dimension 1) have equal dimension, via `fully_sync_dimension`.

**Architecture:** New `execution/ChainDim.v` (`chain_dim_1`: a total order on ≥2 elements has dimension 1, reusing `fin_small_dim_le_2`'s singleton-realizer construction + `dim_ge_1_of_two`), `execution/TransformA.v` (`transform_preserves_dimension` corollary of `fully_sync_dimension`, the concrete `B_square`/`B_contracted` chain blocks, `transform_A_preserves`), `execution/TransformAExamples.v` (concrete example, test-only).

**Tech Stack:** Coq/Rocq 9.1; `Posets`; `Dimension` (`DimDefs`, `Theorems`, `AntichainComplement`); execution `FinPosetDimSurgery`, `FinPosetDim`, `FullySync`, `FullySyncDimExact`, `Poset`, `Ordinal`, `DimBridge`; Stdlib `Ensembles`/`Finite_sets`/`List`/`Arith`/`Lia`/`Classical`/`ProofIrrelevance`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/ChainDim.v` | `chain_dim_1` (total order on ≥2 elements ⟹ dimension 1). |
| `execution/TransformA.v` | `transform_preserves_dimension`; `B_square`/`B_contracted` chain blocks (each dim 1); `transform_A_preserves`. |
| `execution/TransformAExamples.v` | `transform_A_block_dims_eq` and/or `transform_A_example` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `chain_dim_1`, `transform_preserves_dimension`, `B_square_R`, `B_contracted_R`, `B_square_dim_1`, `B_contracted_dim_1`, `transform_A_preserves`, `transform_A_block_dims_eq`.

**EXECUTION-TIME FIRST STEP:** `About fully_sync_dimension`, `About dim_ge_1_of_two`, `About fin_dim_exists`, `About cardinal_finite` — confirm binder layouts. Read `FinPosetDimSurgery.v`'s `fin_small_dim_le_2` (the singleton-realizer `≤1` construction `chain_dim_1` ports) and `FinExtremumDimExamples.v`'s `chain2_R`/`chain2_poset`/`chain2_Hfin`/`chain2_dim1` (the bool-chain pattern reused for `B_contracted`).

---

## Task TA0: Scaffold

**Files:** create `execution/ChainDim.v`, `execution/TransformA.v`, `execution/TransformAExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the three stubs.
- [ ] **Step 2:** Add `ChainDim`, `TransformA`, `TransformAExamples` to the `(modules …)` list in `execution/dune` (that order, after the exact n-way modules).
- [ ] **Step 3:** Add the three `.v` paths to `_CoqProject` (same order, after `FinFullySyncDimExamples.v`).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/ChainDim.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/ChainDim.v execution/TransformA.v execution/TransformAExamples.v execution/dune _CoqProject
git commit -m "scaffold Transformation A modules"
```

---

## Task TA1: `chain_dim_1` (`ChainDim.v`)

**Files:** `execution/ChainDim.v`

**READ FIRST:** `FinPosetDimSurgery.v`'s `fin_small_dim_le_2` — its body builds `set (r := Singleton _ R)`, proves `IsRealizer R r` (R total ⟹ R is its own linear extension; the only member is R via `Singleton_inv`), `cardinal r 1` (via `Add`/`card_add`/`card_empty`), and derives `dimension_is_minimum Hd r 1 HrReal Hcard1 : d <= 1`. PORT that to get `d <= 1`; add `d >= 1`.

- [ ] **Step 1: State + prove `chain_dim_1`**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.

Lemma chain_dim_1 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)),
    (forall x y, R x y \/ R y x) ->
    (exists a b : A, a <> b) ->
    PosetDimension R 1.
```
Strategy:
- `intros A R HR Hfin Htot Hge2.`
- Get some dimension: from `Finite` ⟹ `cardinal` (`finite_cardinal`), `dushnik_miller_exists` gives `exists d, inhabited (PosetDimension R d)`; `destruct` ⟹ `d`, `Hd : PosetDimension R d`. (Or, if `fin_dim_exists` is reachable here — it's in `FinPosetDimSurgery`, which this file should NOT import to keep deps minimal; use `dushnik_miller_exists` directly: `destruct (finite_cardinal _ _ Hfin) as [n Hn]; destruct (dushnik_miller_exists R n Hn) as [d [Hd]]`.)
- `d <= 1`: PORT `fin_small_dim_le_2`'s construction inline — `set (r := Singleton (A->A->Prop) R)`; `assert (HrReal : IsRealizer R r)` (copy: `constructor; [intros L HL; apply Singleton_inv in HL; subst L; constructor; [constructor; [exact HR | exact Htot] | intros x y Hxy; exact Hxy] | intros x y; split; [intros Hxy L HL; apply Singleton_inv in HL; subst L; exact Hxy | intros Hall; apply (Hall R); constructor]]`); `assert (Hcard1 : cardinal _ r 1)` (copy the `Add`/`card_add` argument); `pose proof (dimension_is_minimum Hd r 1 HrReal Hcard1) as Hle1`.
- `1 <= d`: `pose proof (dim_ge_1_of_two R d Hd Hge2) as Hge1` (confirm `dim_ge_1_of_two`'s arg order with `About`; R explicit).
- `assert (d = 1) by lia`. `subst d`. `exact Hd`.

ZERO `Admitted`.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/ChainDim.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/ChainDim.v && git commit -m "feat(execution): a total order on >=2 elements has dimension 1"`.

---

## Task TA2: `transform_preserves_dimension` (`TransformA.v`)

**Files:** `execution/TransformA.v`

- [ ] **Step 1: The block-replacement dimension-invariance corollary**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FinPosetDimSurgery FinPosetDim FullySync FullySyncDimExact
                              ChainDim.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Lemma transform_preserves_dimension :
  forall E blocks dims E' blocks' dims',
    IsFullySync E blocks -> length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    IsFullySync E' blocks' -> length dims' = length blocks' ->
    (forall i, i < length blocks' ->
       PosetDimension (sub_order E' (nth i blocks' (Empty_set _))) (nth i dims' 0)) ->
    (exists a b : ep_carrier E', a <> b) ->
    fold_right Nat.max 0 dims = fold_right Nat.max 0 dims' ->
    forall dW dW', PosetDimension (ep_order E) dW -> PosetDimension (ep_order E') dW' ->
      dW = dW'.
```
Strategy: `intros … Hfold dW dW' HdW HdW'`. `pose proof (fully_sync_dimension E blocks dims … dW HdW) as HE` (`dW = Nat.max 1 (fold_right Nat.max 0 dims)`); `pose proof (fully_sync_dimension E' blocks' dims' … dW' HdW') as HE'` (`dW' = Nat.max 1 (fold_right Nat.max 0 dims')`). `rewrite HE, HE'. rewrite Hfold. reflexivity.` (or `congruence`). Pass the matching hypotheses to each `fully_sync_dimension` call.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/TransformA.vo 2`. Exit 0.

- [ ] **Step 3: The concrete chain blocks `B_square_R`, `B_contracted_R`**

```coq
(* B_contracted: the 2 synchronized points, a 2-element chain (false < true on bool). *)
Definition B_contracted_R (a b : bool) : Prop := a = b \/ (a = false /\ b = true).

(* B_square: the 4-event synchronization square, a 4-element chain on Fin-like nat<4
   with the natural order (s0 < r1 < s1 < r0). *)
Definition Sq := { n : nat | n < 4 }.
Definition B_square_R (x y : Sq) : Prop := proj1_sig x <= proj1_sig y.
```
Prove the supporting instances/facts for each:
- `IsPoset bool B_contracted_R` (reuse `chain2_poset` from `FinExtremumDimExamples.v` if importable — it's the SAME relation `chain2_R`; either `Import` it or re-prove ~10 lines). `Finite bool (Full_set bool)` (reuse `chain2_Hfin`). totality `forall a b, B_contracted_R a b \/ B_contracted_R b a` (`destruct a, b; tauto`-ish). ≥2 elements (`false <> true`).
- `IsPoset Sq B_square_R` (refl/antisym/trans via `≤` on `proj1_sig` + `proof_irrelevance` for antisym on the sig). `Finite Sq (Full_set Sq)` (4-element subtype of `nat` — build via `cardinal Sq (Full_set Sq) 4` listing the 4 elements with `card_add`, or via `cardinal_subtype_full` on `{n | n<4}` — reuse the `execution/Finite.v` pattern). totality (`≤` total via `Nat.le_ge_dec`/`lia`). ≥2 elements (`exist 0 _ <> exist 1 _`, distinct `proj1_sig`).
- `B_contracted_dim_1 : PosetDimension B_contracted_R 1` := `chain_dim_1 B_contracted_R <Hfin> <total> <≥2>`.
- `B_square_dim_1 : PosetDimension B_square_R 1` := `chain_dim_1 B_square_R <Hfin> <total> <≥2>`.

(If `B_square`'s `Finite`/`IsPoset` plumbing is heavy, the cheaper alternative is to
make `B_square` ALSO a `bool`-chain (same as contracted) — but that loses the
"4-event square" flavor. Prefer the genuine 4-element `Sq`; fall back to a 4-element
chain on a simpler carrier if `Finite Sq` resists. Either way both are dim-1 chains.)

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 300 execution/TransformA.vo 2`. Exit 0; zero admits.

- [ ] **Step 5: `transform_A_preserves`**

```coq
(* Transformation A: same fully-sync surroundings, the swapped block is dim 1 on both
   sides (B_square vs B_contracted), so the dims lists are equal and dimension is
   preserved. Stated with the two dims lists literally equal (both have 1 in the
   swapped slot). *)
Lemma transform_A_preserves :
  forall E blocks dims E' blocks' dims',
    IsFullySync E blocks -> length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    IsFullySync E' blocks' -> length dims' = length blocks' ->
    (forall i, i < length blocks' ->
       PosetDimension (sub_order E' (nth i blocks' (Empty_set _))) (nth i dims' 0)) ->
    (exists a b : ep_carrier E', a <> b) ->
    dims = dims' ->                            (* same per-block dimension list *)
    forall dW dW', PosetDimension (ep_order E) dW -> PosetDimension (ep_order E') dW' ->
      dW = dW'.
```
Strategy: `intros … Hdimseq …`. `apply (transform_preserves_dimension E blocks dims E' blocks' dims' …)`; the `fold_right Nat.max 0 dims = fold_right Nat.max 0 dims'` hypothesis is `f_equal _ Hdimseq` / `rewrite Hdimseq; reflexivity`. (`transform_A_preserves` IS `transform_preserves_dimension` with `dims = dims'`; it documents that A is a block swap with the swapped block dim 1 on both sides — the surrounding dims and the swapped `1` are identical, so the dims lists coincide.)

- [ ] **Step 6: Build** — `bash .claude/scripts/timed-build.sh 300 execution/TransformA.vo 2`. Exit 0; zero admits.
- [ ] **Step 7: Commit** — `git add execution/TransformA.v && git commit -m "feat(execution): Transformation A as dimension-preserving block replacement"`.

---

## Task TA3: Concrete example (`TransformAExamples.v`)

**Files:** `execution/TransformAExamples.v`

- [ ] **Step 1: The block-level equal-dimension fact (the honest core), + execution-level if tractable**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import ChainDim TransformA.
Import ListNotations.

(* The square block and the contracted block have equal dimension (both 1) — the
   per-block equal-dimension fact that makes Transformation A dimension-preserving. *)
Example transform_A_block_dims_eq :
  exists d, PosetDimension B_square_R d /\ PosetDimension B_contracted_R d.
```
Strategy: `exists 1; split; [exact B_square_dim_1 | exact B_contracted_dim_1]`. (This is the concrete payload: the two blocks are interchangeable because both are dim 1.)

OPTIONAL execution-level example (only if building two full `IsFullySync` witnesses is
tractable — reuse the all-singleton `cblocks` pattern from `FinFullySyncDimExamples.v`
extended with the square/contracted block): a concrete `E`/`E'` pair with `transform_A_preserves`
giving `dim E = dim E'`. If heavy, OMIT and keep `transform_A_block_dims_eq` as the
example (it is the genuine content). Document the choice in the commit message.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 240 execution/TransformAExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/TransformAExamples.v && git commit -m "test(execution): square and contracted blocks have equal dimension"`.

---

## Task TA4: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `ChainDim TransformA` to the `Require Export` line in `execution/Execution.v` (NOT the examples).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 900 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions chain_dim_1.` to `ChainDim.v`, `Print Assumptions transform_preserves_dimension.` to `TransformA.v`, `Print Assumptions transform_A_block_dims_eq.` to `TransformAExamples.v`; build each; read the axiom blocks (expect only standard classical/choice axioms); then `git checkout -- execution/ChainDim.v execution/TransformA.v execution/TransformAExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "Transformation A" subsection:
```
#### `execution/ChainDim.v` / `TransformA.v` — Transformation A (sync-square contraction)

Transformation A (contract a synchronization square into 2 synchronized points) as a dimension-preserving block replacement: replacing a fully-sync block by another of equal dimension preserves the whole execution's dimension (via `fully_sync_dimension`). The square and its contraction are both dimension-1 chains.

| Name | Meaning |
|------|---------|
| `chain_dim_1` | a total order on ≥2 elements has dimension 1 |
| `transform_preserves_dimension` | two fully-sync execs with equal max-block-dim have equal dimension |
| `B_square_R` / `B_contracted_R` | the 4-event square and 2-point contracted blocks (each dim 1) |
| `transform_A_preserves` | swapping the square block for its contraction preserves dimension |
| `transform_A_block_dims_eq` | (test) square and contracted blocks have equal dimension |
```
Match the actual headers/style used elsewhere. Note: A *preserves* (does not lower) dimension — matching the paper.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export Transformation A; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (`chain_dim_1`) → TA1; Component 2 (`transform_preserves_dimension`) → TA2 Step 1; Component 3 (`B_square`/`B_contracted`) → TA2 Steps 3–4; Component 4 (`transform_A_preserves`) → TA2 Step 5; Component 5 (example) → TA3; wiring/testing/audit → TA0 + TA4. All mapped.
- **The only genuinely new proof is `chain_dim_1`** (TA1), a port of `fin_small_dim_le_2`'s singleton-realizer `≤1` construction + `dim_ge_1_of_two`. Everything else is a corollary of `fully_sync_dimension` (TA2 Step 1 is a one-liner) or concrete chain-poset plumbing (TA2 Steps 3–4, reusing the `chain2`/`Finite.v` patterns).
- **Risk:** `Finite Sq (Full_set Sq)` for `Sq := {n|n<4}` — the 4-element subtype finiteness. Mitigation noted in TA2 Step 3 (fall back to a 4-element chain on a simpler carrier, or `cardinal_subtype_full` on `{n|n<4}` à la `execution/Finite.v`). Both blocks just need to be dim-1 chains.
- **Name consistency:** `chain_dim_1`, `transform_preserves_dimension`, `B_square_R`/`B_contracted_R`, `B_square_dim_1`/`B_contracted_dim_1`, `transform_A_preserves`, `transform_A_block_dims_eq`.
- **Reused (confirmed):** `fully_sync_dimension` (FullySyncDimExact); `fin_small_dim_le_2` (the `≤1` singleton-realizer construction, FinPosetDimSurgery — to port, not import-and-call, since it gives `≤2`); `dim_ge_1_of_two` (AntichainComplement); `dushnik_miller_exists`/`finite_cardinal`/`cardinal_subtype_full` (Dimension/Stdlib); `chain2_R`/`chain2_poset`/`chain2_Hfin` (FinExtremumDimExamples — for `B_contracted`).
- **Caveats recorded in INDEX + spec:** A preserves (not lowers) dimension; the geometry is our concrete realization of the paper's informal contraction.

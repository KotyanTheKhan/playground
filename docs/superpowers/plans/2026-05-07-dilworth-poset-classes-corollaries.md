# Dilworth Corollaries for All PosetClasses Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `IsPoset` instances for the semilattice/lattice class hierarchy, an `IsFinitePoset` bundling class, and four named Dilworth corollaries that apply to each lattice level.

**Architecture:** Four sequential commits, each green. (1) Split `PosetClasses.v` into `IsPoset`-only + new `LatticeClasses.v`. (2) Add `LatticeOrder.v` with the single `meet_le` order and its `IsPoset` instance — inherited automatically by all richer lattice classes. (3) Add `FinitePoset.v`. (4) Add `DilworthCorollaries.v` with four one-line corollaries and extend `Package.v`.

**Tech Stack:** Coq / Stdlib Ensembles + Finite_sets; `mise run build-posets` for all build checks.

---

### Task 1: Split PosetClasses.v → PosetClasses.v + LatticeClasses.v

**Files:**
- Modify: `posets/PosetClasses.v`
- Create: `posets/LatticeClasses.v`

- [ ] **Step 1: Create `posets/LatticeClasses.v`** with the four lattice classes moved verbatim from `PosetClasses.v`

```coq
(* Semilattice and lattice class definitions *)

Class IsMeetSemilattice (A : Type) (meet : A -> A -> A) := {
  meet_assoc : forall x y z, meet (meet x y) z = meet x (meet y z);
  meet_comm  : forall x y, meet x y = meet y x;
  meet_idem  : forall x, meet x x = x
}.

Class IsJoinSemilattice (A : Type) (join : A -> A -> A) := {
  join_assoc : forall x y z, join (join x y) z = join x (join y z);
  join_comm  : forall x y, join x y = join y x;
  join_idem  : forall x, join x x = x
}.

Class IsLattice (A : Type) (meet join : A -> A -> A)
      `{IsMeetSemilattice A meet} `{IsJoinSemilattice A join} := {
  absorption_meet : forall x y, meet x (join x y) = x;
  absorption_join : forall x y, join x (meet x y) = x
}.

Class IsDistributiveLattice (A : Type) (meet join : A -> A -> A)
      `{IsLattice A meet join} := {
  distrib_meet : forall x y z, meet x (join y z) = join (meet x y) (meet x z);
  distrib_join : forall x y z, join x (meet y z) = meet (join x y) (join x z)
}.
```

- [ ] **Step 2: Trim `posets/PosetClasses.v`** to `IsPoset` only — remove lines 9–43 (the finite-posets comment block, the `List` import, and all lattice classes)

```coq
(* Poset class definition *)

Class IsPoset (A : Type) (R : A -> A -> Prop) := {
  poset_refl : forall x, R x x;
  poset_antisym : forall x y, R x y -> R y x -> x = y;
  poset_trans : forall x y z, R x y -> R y z -> R x z
}.
```

- [ ] **Step 3: Build**

```
mise run build-posets
```

Expected: clean build. No existing file in `posets/dilworth/` imports the lattice classes from `PosetClasses`, so no other changes are needed.

- [ ] **Step 4: Commit**

```bash
git add posets/PosetClasses.v posets/LatticeClasses.v
git commit -m "refactor: split PosetClasses.v — lattice classes move to LatticeClasses.v"
```

---

### Task 2: Add LatticeOrder.v

**Files:**
- Create: `posets/LatticeOrder.v`

The canonical partial order for a meet-semilattice: `x ≤ y := meet x y = x`. One exported instance is automatically inherited by `IsLattice` and `IsDistributiveLattice` via their `IsMeetSemilattice` superclass.

Proof sketch for the three axioms:
- **Reflexivity**: `meet x x = x` ← `meet_idem x`
- **Antisymmetry**: `meet x y = x` and `meet y x = y` → rewrite second by `meet_comm` → `meet x y = y` → rewrite by first → `x = y`
- **Transitivity**: `meet x y = x` and `meet y z = y` → `meet x z = meet (meet x y) z = meet x (meet y z) = meet x y = x` using assoc

- [ ] **Step 1: Create `posets/LatticeOrder.v`** with the `meet_le` definition and instance

```coq
(* Canonical partial order derived from a meet-semilattice: x ≤ y iff meet x y = x *)

From Posets Require Import PosetClasses LatticeClasses.

Section MeetOrder.
  Context {A : Type} (meet : A -> A -> A) `{IsMeetSemilattice A meet}.

  Definition meet_le : A -> A -> Prop := fun x y => meet x y = x.

  #[export] Instance meet_semilattice_is_poset : IsPoset A meet_le.
  Proof.
    constructor.
    - (* Reflexivity: meet x x = x *)
      intro x. unfold meet_le. apply meet_idem.
    - (* Antisymmetry: meet x y = x ∧ meet y x = y → x = y *)
      intros x y Hxy Hyx. unfold meet_le in *.
      rewrite meet_comm in Hyx.
      rewrite Hxy in Hyx.
      exact Hyx.
    - (* Transitivity: meet x y = x ∧ meet y z = y → meet x z = x *)
      intros x y z Hxy Hyz. unfold meet_le in *.
      rewrite <- Hxy at 1.
      rewrite meet_assoc.
      rewrite Hyz.
      exact Hxy.
  Qed.
End MeetOrder.
```

**Antisymmetry proof trace:**
- `Hxy : meet x y = x`, `Hyx : meet y x = y`, goal: `x = y`
- `rewrite meet_comm in Hyx` → `Hyx : meet x y = y`
- `rewrite Hxy in Hyx` → `Hyx : x = y`
- `exact Hyx` ✓

**Transitivity proof trace:**
- `Hxy : meet x y = x`, `Hyz : meet y z = y`, goal: `meet x z = x`
- `rewrite <- Hxy at 1` (replaces first occurrence of `x` in goal with `meet x y`) → `meet (meet x y) z = x`
- `rewrite meet_assoc` → `meet x (meet y z) = x`
- `rewrite Hyz` → `meet x y = x`
- `exact Hxy` ✓

- [ ] **Step 2: Build**

```
mise run build-posets
```

Expected: clean build.

- [ ] **Step 3: Commit**

```bash
git add posets/LatticeOrder.v
git commit -m "feat: add LatticeOrder.v — meet_le order and IsPoset instance for IsMeetSemilattice"
```

---

### Task 3: Add FinitePoset.v

**Files:**
- Create: `posets/FinitePoset.v`

`IsFinitePoset A R n` bundles `IsPoset A R` and `cardinal A (Full_set A) n`. The `:>` on `fp_is_poset` makes `IsPoset A R` automatically dischargeable by typeclass inference whenever `IsFinitePoset A R n` is in context.

- [ ] **Step 1: Create `posets/FinitePoset.v`**

```coq
(* Finite poset bundling class: IsPoset + cardinality of the full set *)

From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.

Class IsFinitePoset (A : Type) (R : A -> A -> Prop) (n : nat) := {
  fp_is_poset :> IsPoset A R;
  fp_finite   :  cardinal A (Full_set A) n
}.
```

- [ ] **Step 2: Build**

```
mise run build-posets
```

Expected: clean build.

- [ ] **Step 3: Commit**

```bash
git add posets/FinitePoset.v
git commit -m "feat: add FinitePoset.v — IsFinitePoset bundling class"
```

---

### Task 4: Add DilworthCorollaries.v and extend Package.v

**Files:**
- Create: `posets/dilworth/DilworthCorollaries.v`
- Modify: `posets/dilworth/Package.v`

Four corollaries, all one-line applications of the existing `Dilworth` theorem. The `Dilworth` theorem (from `DilworthTheorem.v`) has signature (after the section):
```
Dilworth : forall {A : Type} (R : A -> A -> Prop) {H : IsPoset A R} (n w k : nat),
  cardinal A (Full_set A) n ->
  Width R (Full_set A) w ->
  ChainCoverNumber R (Full_set A) k ->
  w = k
```
`R` is explicit; `A` and `IsPoset A R` are implicit/typeclass.

- [ ] **Step 1: Create `posets/dilworth/DilworthCorollaries.v`**

```coq
(* Dilworth corollaries for IsFinitePoset and the lattice class hierarchy *)

From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses LatticeClasses LatticeOrder FinitePoset.
From Dilworth Require Import Definitions DilworthTheorem.

(* ------------------------------------------------------------------ *)
(* Corollary B: Dilworth without explicit n — IsFinitePoset carries it *)
(* ------------------------------------------------------------------ *)

Section DilworthFinite.
  Context {A : Type} {R : A -> A -> Prop} {n : nat} `{IsFinitePoset A R n}.

  Corollary Dilworth_finite : forall w k,
    Width R (Full_set A) w ->
    ChainCoverNumber R (Full_set A) k ->
    w = k.
  Proof.
    intros w k Hw Hk.
    exact (Dilworth _ _ w k fp_finite Hw Hk).
  Qed.
End DilworthFinite.

(* ------------------------------------------------------------------ *)
(* Corollaries A: Dilworth for each level of the lattice hierarchy     *)
(* In all three sections, the order is meet_le meet.                   *)
(* IsPoset A (meet_le meet) is resolved via meet_semilattice_is_poset. *)
(* ------------------------------------------------------------------ *)

Section DilworthMeetSemilattice.
  Context {A : Type} (meet : A -> A -> A) `{IsMeetSemilattice A meet}.

  Corollary Dilworth_meet_semilattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hn Hw Hk.
    exact (Dilworth _ n w k Hn Hw Hk).
  Qed.
End DilworthMeetSemilattice.

Section DilworthLattice.
  Context {A : Type} (meet join : A -> A -> A) `{IsLattice A meet join}.

  Corollary Dilworth_lattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hn Hw Hk.
    exact (Dilworth _ n w k Hn Hw Hk).
  Qed.
End DilworthLattice.

Section DilworthDistributiveLattice.
  Context {A : Type} (meet join : A -> A -> A) `{IsDistributiveLattice A meet join}.

  Corollary Dilworth_distributive_lattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof.
    intros n w k Hn Hw Hk.
    exact (Dilworth _ n w k Hn Hw Hk).
  Qed.
End DilworthDistributiveLattice.
```

**Proof note for each lattice corollary:** `exact (Dilworth _ n w k Hn Hw Hk)` — the first `_` is `R := meet_le meet`, inferred from `Hw : Width (meet_le meet) ...`. The `IsPoset A (meet_le meet)` implicit argument is resolved by `meet_semilattice_is_poset` (exported from `LatticeOrder.v`), which is found in context because `IsMeetSemilattice A meet` is a section hypothesis (directly or via superclass resolution for `IsLattice`/`IsDistributiveLattice`).

**Proof note for `Dilworth_finite`:** Both `_` holes are: first = `R` (inferred from `Hw`), second = `n` (inferred from `fp_finite : cardinal A (Full_set A) n`).

If any proof fails, fallback: replace `exact (Dilworth _ ...)` with `eapply Dilworth; eassumption`.

- [ ] **Step 2: Extend `posets/dilworth/Package.v`**

Add one line at the end (before the trailing blank line):

```coq
From Dilworth Require Export DilworthCorollaries.
```

Full file after edit:

```coq
(** Dilworth's Theorem: The width of a finite poset equals its minimum chain cover number.
    
    This module provides a formalization of Dilworth's theorem and related results.
    
    Key components:
    - Definitions: Basic definitions (chains, antichains, chain covers, width)
    - CardinalArithmetic: Cardinal arithmetic utilities (removal, pigeonhole)
    - InjectionPrinciple: Cardinal injection principle (fully proven)
    - CardinalLemmas: Cardinal extensionality and helper lemmas
    - WidthLowerBound: Proof that width ≤ minimum chain cover (DilworthA)
    - WidthUpperBound: Proof that minimum chain cover ≤ width (DilworthB)
    - DilworthTheorem: Main theorem combining both directions
    - DilworthCorollaries: Corollaries for IsFinitePoset and lattice class hierarchy
*)

From Dilworth Require Export CardinalArithmetic.
From Dilworth Require Export Definitions.
From Dilworth Require Export InjectionPrinciple.
From Dilworth Require Export CardinalLemmas.
From Dilworth Require Export WidthLowerBound.
From Dilworth Require Export WidthUpperBound.
From Dilworth Require Export DilworthTheorem.
From Dilworth Require Export DilworthCorollaries.
```

- [ ] **Step 3: Build**

```
mise run build-posets
```

Expected: clean build. All four corollaries type-check and their proofs compile.

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/DilworthCorollaries.v posets/dilworth/Package.v
git commit -m "feat: add DilworthCorollaries — Dilworth_finite, Dilworth_meet_semilattice, Dilworth_lattice, Dilworth_distributive_lattice"
```

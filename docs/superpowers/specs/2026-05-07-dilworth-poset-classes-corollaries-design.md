# Dilworth Corollaries for All PosetClasses — design

**Date:** 2026-05-07
**Branch:** `dilworth_continue_c`
**Scope:** Two goals — (A) `IsPoset` instances for the semilattice/lattice class hierarchy and Dilworth corollaries for each; (B) `IsFinitePoset` bundling class and a cleaner Dilworth corollary that hides the explicit cardinality argument. No changes to existing theorem statements or proofs.

---

## Motivation

The current `Dilworth` theorem lives in a section with `Context (R : A -> A -> Prop) \`{IsPoset A R}`. It already applies to any relation satisfying `IsPoset`, but:

- **Problem A:** `PosetClasses.v` defines `IsMeetSemilattice`, `IsLattice`, and `IsDistributiveLattice` via algebraic operations (`meet`, `join`), with no connection to `IsPoset`. Users of these richer structures cannot directly invoke `Dilworth` without manually constructing the order relation and its `IsPoset` instance.
- **Problem B:** The main theorem requires an explicit `cardinal A (Full_set A) n` hypothesis. Every call site must supply `n` even though it is uniquely determined by the poset. An `IsFinitePoset` bundling class removes this friction.

---

## File layout

No changes to `dune` files — both `posets/dune` and `posets/dilworth/dune` already carry `(include_subdirs qualified)`.

| File | Action | Responsibility |
|---|---|---|
| `posets/PosetClasses.v` | Trim | `IsPoset` only; lattice/semilattice classes and the `List` import removed |
| `posets/LatticeClasses.v` | **New** | `IsMeetSemilattice`, `IsJoinSemilattice`, `IsLattice`, `IsDistributiveLattice` (moved verbatim from `PosetClasses.v`) |
| `posets/LatticeOrder.v` | **New** | `meet_le` definition + `#[export] Instance meet_semilattice_is_poset` |
| `posets/FinitePoset.v` | **New** | `Class IsFinitePoset` bundling `IsPoset` + cardinality |
| `posets/dilworth/DilworthCorollaries.v` | **New** | Four corollaries: `Dilworth_finite`, `Dilworth_meet_semilattice`, `Dilworth_lattice`, `Dilworth_distributive_lattice` |
| `posets/dilworth/Package.v` | Extend | Add `From Dilworth Require Export DilworthCorollaries` |

All existing `From Posets Require Import PosetClasses` imports continue to work. Files that also use the lattice classes add `From Posets Require Import LatticeClasses`.

---

## `posets/LatticeClasses.v`

Exact content of `PosetClasses.v` lines 14–43, moved verbatim. No new proofs. The `From Stdlib Require Import List.` line moves here if needed, but can be dropped entirely if `List` is unused by the lattice classes (it is — drop it).

```coq
Class IsMeetSemilattice (A : Type) (meet : A -> A -> A) := { ... }.
Class IsJoinSemilattice (A : Type) (join : A -> A -> A) := { ... }.
Class IsLattice (A : Type) (meet join : A -> A -> A)
      `{IsMeetSemilattice A meet} `{IsJoinSemilattice A join} := { ... }.
Class IsDistributiveLattice (A : Type) (meet join : A -> A -> A)
      `{IsLattice A meet join} := { ... }.
```

---

## `posets/LatticeOrder.v`

The canonical partial order for a meet-semilattice: `x ≤ y := meet x y = x` ("x is already below y if their meet is x"). All three `IsPoset` axioms follow from the three semilattice laws:

| Axiom | Proof |
|---|---|
| Reflexivity `meet_le x x` | `meet_idem x` |
| Antisymmetry: `meet x y = x ∧ meet y x = y → x = y` | `meet_comm` turns `meet y x` into `meet x y = x`; combined with `Hyx : meet y x = y` gives `x = y` |
| Transitivity: `meet x y = x ∧ meet y z = y → meet x z = x` | `meet x z = meet (meet x y) z = meet x (meet y z) = meet x y = x` using `meet_assoc` |

```coq
From Posets Require Import PosetClasses LatticeClasses.

Section MeetOrder.
  Context {A : Type} (meet : A -> A -> A) `{IsMeetSemilattice A meet}.

  Definition meet_le : A -> A -> Prop := fun x y => meet x y = x.

  #[export] Instance meet_semilattice_is_poset : IsPoset A meet_le := { ... }.
End MeetOrder.
```

The single `#[export]` instance is found automatically for `IsLattice` (which extends `IsMeetSemilattice`) and `IsDistributiveLattice` (which extends `IsLattice`) — no additional instances needed.

The implementer may use tactic mode for the three axiom proofs if term-mode rewriting is awkward.

---

## `posets/FinitePoset.v`

```coq
From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses.

Class IsFinitePoset (A : Type) (R : A -> A -> Prop) (n : nat) := {
  fp_is_poset :> IsPoset A R;
  fp_finite   :  cardinal A (Full_set A) n
}.
```

`n` is an explicit class parameter so typeclass search can index on it. The `:>` coercion on `fp_is_poset` makes `IsPoset A R` automatically available whenever `IsFinitePoset A R n` is in context.

---

## `posets/dilworth/DilworthCorollaries.v`

Four corollaries; all proofs are one-line applications of the main `Dilworth` theorem.

```coq
From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses LatticeClasses LatticeOrder FinitePoset.
From Dilworth Require Import Definitions DilworthTheorem.

Section DilworthFinite.
  Context {A : Type} {R : A -> A -> Prop} {n : nat} `{IsFinitePoset A R n}.

  (* Dilworth without explicit n — the finite poset class carries it *)
  Corollary Dilworth_finite : forall w k,
    Width R (Full_set A) w ->
    ChainCoverNumber R (Full_set A) k ->
    w = k.
  Proof. intros w k. eapply Dilworth. exact fp_finite. Qed.
End DilworthFinite.

Section DilworthMeetSemilattice.
  Context {A : Type} (meet : A -> A -> A) `{IsMeetSemilattice A meet}.

  Corollary Dilworth_meet_semilattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof. intros n w k. apply Dilworth. Qed.
End DilworthMeetSemilattice.

Section DilworthLattice.
  Context {A : Type} (meet join : A -> A -> A) `{IsLattice A meet join}.

  Corollary Dilworth_lattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof. intros n w k. apply Dilworth. Qed.
End DilworthLattice.

Section DilworthDistributiveLattice.
  Context {A : Type} (meet join : A -> A -> A) `{IsDistributiveLattice A meet join}.

  Corollary Dilworth_distributive_lattice : forall n w k,
    cardinal A (Full_set A) n ->
    Width (meet_le meet) (Full_set A) w ->
    ChainCoverNumber (meet_le meet) (Full_set A) k ->
    w = k.
  Proof. intros n w k. apply Dilworth. Qed.
End DilworthDistributiveLattice.
```

The three lattice corollaries are mathematically identical — the value is having named anchors that make explicit that Dilworth applies at each level of the hierarchy.

---

## Migration order (commit-by-commit)

Each commit must leave the build green (`mise run build-posets`).

1. **Split `PosetClasses.v`**: create `LatticeClasses.v` with the moved content; trim `PosetClasses.v` to `IsPoset` only. No existing Dilworth files import the lattice classes, so no other files need updating. Build check.
2. **Add `LatticeOrder.v`**: new file, no changes to existing files. Build check.
3. **Add `FinitePoset.v`**: new file, no changes to existing files. Build check.
4. **Add `DilworthCorollaries.v`** and extend `Package.v`. Build check.

---

## Constraints

- No changes to existing theorem statements (`Dilworth`, `DilworthA`, `DilworthB`, etc.).
- No changes to `dune` files.
- No `IsJoinSemilattice → IsPoset` instance (out of scope; YAGNI).
- Build command: `mise run build-posets`.

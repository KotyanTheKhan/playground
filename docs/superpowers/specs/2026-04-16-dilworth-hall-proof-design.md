# Dilworth Theorem — Hall's Marriage Theorem Proof Design

**Date:** 2026-04-16
**Status:** Approved
**Goal:** Replace the two `Admitted` lemmas in `WidthUpperBound.v` with complete Coq proofs, using Hall's marriage theorem as the core engine.

---

## Problem Statement

Two lemmas in `posets/dilworth/WidthUpperBound.v` are admitted:

1. `above_chain_assignment_exists` (line ~492): Given `sub ⊆ Above(la)` where `la` is the largest antichain of `sub` with `|la| = w`, construct `f : A → A` such that:
   - For all `x ∈ sub`: `f(x) ∈ la` and `R (f x) x`
   - For all `a ∈ la`: the fiber `{x ∈ sub | f x = a}` is a chain

2. `below_chain_assignment_exists` (line ~549): Symmetric version for `sub ⊆ Below(la)`, with `R x (f x)` instead.

These are the only blockers to a complete axiom-free proof of Dilworth's theorem.

---

## Architecture

### New file: `posets/dilworth/Hall.v`

Standalone Hall's marriage theorem. Imports only `Stdlib` and `CardinalArithmetic.v` (for cardinal lemmas). No dependency on `Definitions.v`, `PosetClasses.v`, or any poset-specific concept.

### Modified files

- `posets/dilworth/WidthUpperBound.v` — add `From Dilworth Require Import Hall`; replace the two admits with proofs; add three helper lemmas
- `posets/dilworth/dune` — add `Hall` to the modules list

### Dependency order

```
Definitions → InjectionPrinciple → CardinalLemmas → Helpers
                                                   → Hall           (new)
                                                   → WidthLowerBound
                                                   → WidthUpperBound (imports Hall)
                                                   → DilworthTheorem
```

---

## Section 1: Hall.v

### Definitions

```coq
(* N(S) = union of individual neighbor sets *)
Definition set_neighbors (nbrs : A -> Ensemble A) (S : Ensemble A) : Ensemble A :=
  fun y => exists x, In A S x /\ In A (nbrs x) y.

(* Hall's condition: every S ⊆ X satisfies |S| ≤ |N(S)| *)
Definition HallCondition (X : Ensemble A) (nbrs : A -> Ensemble A) : Prop :=
  forall S ns nn,
    Included A S X ->
    cardinal A S ns ->
    cardinal A (set_neighbors nbrs S) nn ->
    ns <= nn.

(* Perfect matching: injective function X → Y respecting neighbors *)
Definition IsPerfectMatching (X Y : Ensemble A) (nbrs : A -> Ensemble A) (m : A -> A) : Prop :=
  (forall x, In A X x -> In A Y (m x)) /\
  (forall x, In A X x -> In A (nbrs x) (m x)) /\
  (forall x1 x2, In A X x1 -> In A X x2 -> m x1 = m x2 -> x1 = x2).
```

### Main theorem

```coq
Theorem hall_marriage_theorem : forall (X Y : Ensemble A) nx (nbrs : A -> Ensemble A),
  cardinal A X nx ->
  Finite A Y ->
  (forall x y, In A X x -> In A (nbrs x) y -> In A Y y) ->
  HallCondition X nbrs ->
  exists m : A -> A, IsPerfectMatching X Y nbrs m.
```

### Proof strategy — induction on `nx = |X|`

**Base** (`nx = 0`): `X = ∅`; any function satisfies the conditions vacuously.

**Inductive step** — classical case split on whether a tight proper subset exists:

- **Non-tight case:** Every proper non-empty `S ⊊ X` has `|N(S)| > |S|`.
  - Pick `x₀ ∈ X` (by `constructive_indefinite_description`) and any `y₀ ∈ nbrs(x₀)`.
  - Define `X' = X \ {x₀}`, `nbrs'(x) = nbrs(x) \ {y₀}`.
  - Hall's condition for `X'`: `|N'(S)| ≥ |N(S)| - 1 ≥ |S|` (strict surplus absorbs `y₀`).
  - Apply IH to `(X', Y \ {y₀}, nbrs')` to get `m'`.
  - Define `m(x₀) = y₀`, `m(x) = m'(x)` for `x ∈ X'`. Injectivity: `m'` maps into `Y \ {y₀}`.

- **Tight case:** Some proper non-empty `T ⊊ X` has `|N(T)| = |T|`.
  - Apply IH to `T` (with `nbrs` restricted) to get `m_T : T → N(T)`.
  - Define `X'' = X \ T`, `nbrs''(x) = nbrs(x) \ N(T)`.
  - Hall's condition for `X''`: for any `S ⊆ X''`,
    `|N''(S)| = |N(S ∪ T) \ N(T)| ≥ |N(S ∪ T)| - |N(T)| ≥ |S| + |T| - |T| = |S|`.
  - Apply IH to `(X'', Y \ N(T), nbrs'')` to get `m'' : X'' → Y \ N(T)`.
  - Define `m = m_T` on `T`, `m = m''` on `X''`. Injectivity: ranges are disjoint.

**Classical tools:** `constructive_indefinite_description`, `classic`, cardinal lemmas from `CardinalArithmetic.v`.

---

## Section 2: Connecting Hall's Theorem to the Admits

### Key mathematical facts (for `sub ⊆ Above(la)`, `la` = largest antichain, `|la| = w`)

1. **Minimal elements of `sub` = `la`.**
   If `m` is minimal in `sub`, then `m ∈ Above(la)` gives `a ∈ la` with `R a m`; since `a ∈ la ⊆ sub` and `m` minimal, `a = m`. Conversely every `a ∈ la` is minimal in `sub`.

2. **Hall's defect condition:** For any `S ⊆ sub`, the minimal elements of `S` form an antichain of size `≤ w`. Every non-minimal element of `S` has a strict predecessor in `S`, hence lies in `N(S)`. Therefore `|S \ N(S)| ≤ w`, i.e. `|S| - |N(S)| ≤ w`.

3. **Exact defect:** `N(sub) = sub \ la` (la-elements have no strict predecessors; all others do). So `|sub| - |N(sub)| = w`.

4. **Maximum matching = `|sub| - w`:**
   - `≥`: augmented-graph Hall's — add `w` dummy elements of type `unit` (represented as `sum A unit` with `inl` for real elements and `inr tt` as a single shared dummy, or `sum A (fin w)` for distinct dummies). Each `x ∈ sub` has `nbrs_aug(x) = strict successors of x ∪ {all dummies}`. Hall's condition holds: `|N_aug(S)| = |N(S)| + w ≥ (|S| - w) + w = |S|` by fact 2. Apply `hall_marriage_theorem` to get a perfect matching; elements mapped to dummies are the chain starters.
   - `≤`: any matching of size `m` induces a chain cover of size `|sub| - m`; by `DilworthA`, `|sub| - m ≥ w`.

5. **Chain starters = `la`:** In a maximum matching `M` of size `|sub| - w`:
   - All `la`-elements are right-unmatched (minimal elements have no strict predecessors, so nothing can be matched into them).
   - `|right-unmatched| = |sub| - |M| = w = |la|`.
   - Therefore right-unmatched = `la` exactly.

### New helper lemmas in `WidthUpperBound.v`

```coq
(* Minimal elements of sub are exactly la *)
Lemma min_elements_eq_la : forall (sub la : Ensemble A) w,
  IsLargestAntichain R sub la w ->
  Included A sub (Above R la) ->
  forall x, In A sub x ->
    (forall y, In A sub y -> R y x -> y = x) <-> In A la x.

(* Hall's defect condition for the Dilworth strict-order graph *)
Lemma dilworth_hall_defect : forall (sub la : Ensemble A) w,
  IsLargestAntichain R sub la w ->
  forall S ns nn,
    Included A S sub ->
    cardinal A S ns ->
    cardinal A (fun y => In A sub y /\ exists x, In A S x /\ R x y /\ x <> y) nn ->
    ns <= nn + w.

(* Extract assignment from matching; chain starters are la.
   The augmented matching m_aug : sub -> sum A unit maps each sub-element to
   either inl y (a strict successor y ∈ sub) or inr tt (a dummy = chain starter). *)
Lemma matching_to_assignment :
  forall (sub la : Ensemble A) w (m_aug : A -> sum A unit),
  IsLargestAntichain R sub la w ->
  Included A sub (Above R la) ->
  (* m_aug is a perfect matching on the augmented Dilworth graph *)
  IsPerfectMatching sub
    (fun z => match z with inl y => In A sub y | inr _ => True end)
    (fun x => match m_aug x with
              | inl y => R x y /\ x <> y   (* real edge: x <_strict y *)
              | inr _ => In A la x          (* dummy edge: x ∈ la (chain starter) *)
              end)
    m_aug ->
  (* la-elements are chain starters *)
  (forall a, In A la a -> m_aug a = inr tt) ->
  exists f : A -> A,
    (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
    (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
```

### Proof of `above_chain_assignment_exists`

```coq
Lemma above_chain_assignment_exists : ...
Proof.
  (* 1. Build augmented neighbors: nbrs_aug(x) = strict successors of x in sub ∪ {dummies} *)
  (* 2. Verify HallCondition for augmented graph via dilworth_hall_defect *)
  (* 3. Apply hall_marriage_theorem to get m_aug *)
  (* 4. Apply matching_to_assignment to get f with required properties *)
Qed.
```

### `below_chain_assignment_exists` — symmetric proof

Replace `Above` with `Below`, `R x y` with `R y x` throughout. Minimal elements become maximal elements; `la` = maximal elements of `sub` when `sub ⊆ Below(la)`.

---

## Section 3: File Changes Summary

| File | Change | Est. size |
|------|--------|-----------|
| `Hall.v` | New — `set_neighbors`, `HallCondition`, `IsPerfectMatching`, `hall_marriage_theorem` | ~150–200 lines |
| `WidthUpperBound.v` | Add `From Dilworth Require Import Hall`; add 3 helper lemmas; prove 2 admits | ~100 lines added |
| `dune` | Add `Hall` to modules list | 1 line |

### `dune` change

```
(library
 (name Dilworth)
 (modules
   CardinalArithmetic InjectionPrinciple CardinalLemmas Definitions
   Helpers Hall WidthLowerBound WidthUpperBound DilworthTheorem
   Examples ConcreteExample Package))
```

---

## Acceptance Criteria

- `dune build @all` succeeds with no `Admitted` and no new `Axiom` declarations
- `Hall.v` imports only `Stdlib` and `CardinalArithmetic.v` — no poset or order-theory imports
- The two formerly-admitted lemmas have complete proofs
- `DilworthTheorem.v` compiles and the `Dilworth` theorem is fully closed

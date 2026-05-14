# Design: Closing Hard Admits in Hiraguchi's Theorem

**Date:** 2026-05-14  
**Files:** `posets/dimension/Theorems.v`  
**Target admits:** `extension_through_critical_pair` (line 798), n=4,5 base cases (lines 864, 971)

---

## Problem Summary

`hiraguchi_thm` and `hiraguchi_bound` both carry two admitted goals:

1. **`extension_through_critical_pair`** (line 798): Given a critical pair (x',y') and a d'-element realizer of R restricted to S' = A\{x',y'}, produce a (d'+1)-element realizer of R.

2. **n=4,5 base cases** (lines 864, 971): After finding a critical pair and removing it, the current proof attempts `d_q ≤ 1` for the 2- or 3-element subposet. This goal is false in general (a 2-element antichain has dim=2) and the inductive structure is broken for these cases.

---

## Architecture

```
hiraguchi_thm / hiraguchi_bound
├── if n < 6 → small_hiraguchi          (NEW)
│     └── uses: add_incomparable_general
│               szpilrajn_theorem
│               critical_pair_realizer_iff
└── if n ≥ 6 →
      ├── incomparable pair →
      │     ├── extension_through_critical_pair  (FIX)
      │     │     └── uses: lift_and_force_is_poset  (NEW)
      │     │               szpilrajn_theorem
      │     │               critical_pair_realizer_iff
      │     └── (subposet IH: unchanged, always valid since pred(pred n) ≥ 4)
      └── chain → dim = 1 ≤ n/2  (unchanged)
```

---

## Component A: `lift_and_force_is_poset` (new lemma)

### Statement

```coq
Lemma lift_and_force_is_poset :
  forall (x' y' : A) (S' : Ensemble A)
         (L' : {a:A|In A S' a} -> {a:A|In A S' a} -> Prop),
  IsCriticalPair R x' y' ->
  IsLinearExtension (fun a b => R (proj1_sig a) (proj1_sig b)) L' ->
  let L'_lift := fun a b =>
        exists ha hb, L' (exist _ a ha) (exist _ b hb) in
  IsPoset A (clos_trans A
    (fun a b => R a b \/ L'_lift a b \/ (a = x' /\ b = y'))).
```

### Proof strategy

Path invariant: for any path `a -→* b` in TC(R ∪ L'_lift ∪ {(x',y')}), one of these holds:

- `R a b`
- `R a x' ∧ R y' b`
- `L'_lift a b`
- `R a x' ∧ L'_lift y' b`
- `L'_lift a x' ∧ R y' b`
- `L'_lift a x' ∧ L'_lift y' b`  (only if y' ∈ S', vacuous since y' ∉ S')

The invariant is proved by induction on TC then case analysis on each step. Antisymmetry: if both `a -→* b` and `b -→* a` hold, combining the invariants forces `R y' x'`, contradicting `critical_incomparable`. L'_lift-only cycles are impossible since L' is antisymmetric. The structure mirrors `add_incomparable_general` in `Szpilrajn.v`.

---

## Component B: `extension_through_critical_pair` (proof)

### Construction

Given d'-element sub-realizer `r'` of `R|_{S'}`:

1. **Lift map:** For each `L' ∈ r'`, define `L'_lift a b := ∃ ha hb, L' ⟨a,ha⟩ ⟨b,hb⟩`.
2. **Extend to total order:** By `lift_and_force_is_poset`, `TC(R ∪ L'_lift ∪ {(x',y')})` is a valid poset. Apply `szpilrajn_theorem` to obtain total order `L'_full`.
3. **Lifted set:** `r_lifted := image r' (fun L' => L'_full)` — d' total orders, each with x' < y'.
4. **Extra extension:** `L_extra := szpilrajn_theorem(TC(R ∪ {(y',x')}))` — total order with y' < x'.
5. **Result:** `r := Add r_lifted L_extra`, cardinality `d' + 1`.

### Cardinal proof

- The lift map `L' ↦ L'_full` is injective: `L'_full` restricted to S'×S' equals `L'`. Justification: any TC-path between elements a,b ∈ S' either stays within R|_{S'} ∪ L'_lift (giving R(a,b) or L'(a,b)) or passes through the forced edge x'→y' (giving R(a,x') ∧ R(y',b); by `critical_down`, R(a,x') implies R(a,y'), and then transitivity gives R(a,b), which is already in L'). So `TC(R ∪ L'_lift ∪ {(x',y')})|_{S'×S'} = L'|_{S'×S'}`. Since L'_full extends this TC, `L'_full|_{S'×S'} = L'`. Distinct L'₁ ≠ L'₂ therefore give distinct L'₁_full ≠ L'₂_full.
- `L_extra ∉ r_lifted`: every element of `r_lifted` has `x' < y'` (forced by the TC base); `L_extra` has `y' < x'` (forced by `TC(R ∪ {(y',x')})`).
- `cardinal (Add r_lifted L_extra) (d' + 1)` follows from `cardinal r_lifted d'` (image of d'-element set under injection) and `L_extra ∉ r_lifted` via `card_add_gen` (Stdlib Finite_sets).

### Realizer proof via `critical_pair_realizer_iff`

For every critical pair `(p,q)` of R, some `L ∈ r` has `q <_L p`:

- **`(p,q) = (x',y')`:** `L_extra ∈ r` has `y' <_{L_extra} x'`. ✓
- **`(p,q)` with `p,q ∈ S'`:** The pair is also critical in `R|_{S'}` (critical_down and critical_up involve only S'-elements via the subtype embedding). Since `r'` is a realizer of `R|_{S'}`, some `L' ∈ r'` has `q' <_{L'} p'`. The lift `L'_lift` preserves this, and `szpilrajn_theorem` extends it: `L'_full` has `q <_{L'_full} p`. ✓
- **`(p,q)` with `p = x'` or `p = y'` (or `q = x'` or `q = y'`):** By `critical_up` of `(x',y')`: anything strictly above `y'` is above `x'`. By `critical_down`: anything strictly below `x'` is below `y'`. These conditions imply that any critical pair of R involving `x'` or `y'` is either `(x',y')` itself or reduces to a pair in `S'` (since crossing the x'-y' boundary in both directions requires R(y',x'), which is false). Formal argument: if `(x',s)` is a critical pair with `s ∈ S'`, then `x' ∥_R s`. `critical_up` of `(x',y')` applied to s: `R(y',s) → R(x',s)`. So `¬R(y',s)` (otherwise x' < s, contradicting x' ∥ s). This means in `L_extra` (which extends TC(R ∪ {(y',x')})) the ordering of x' and s depends only on R ∪ {(y',x')}. Similarly for pairs involving y'. A case analysis using `critical_down` and `critical_up` shows every such cross-pair is separated by some L'_full or by L_extra. ✓

---

## Component C: `small_hiraguchi` (new lemma)

### Statement

```coq
Lemma small_hiraguchi :
  forall n d,
  cardinal A (Full_set A) n ->
  (n = 4 \/ n = 5) ->
  PosetDimension R d ->
  d <= 2.
```

### Proof

**Case 1 — no incomparable pair:** R is a total order. `{R}` is a 1-element realizer. `d ≤ 1 ≤ 2`. ✓

**Case 2 — incomparable pair exists:**

1. Lift to critical pair `(x',y')` via `incomparable_lifting_to_critical_pair`.
2. `R1 := TC(R ∪ {(x',y')})` — valid poset by `add_incomparable_general`.
3. `L_extra := szpilrajn_theorem(TC(R ∪ {(y',x')}))`.
4. Classical case split on comparability of each remaining element-pair in `S'` under `R1`:

   **Sub-case: all pairs in S' are comparable in R1** (S' is a chain in R1):
   - `L1 := szpilrajn_theorem(R1)`.
   - `{L1, L_extra}` is a 2-element realizer: by `critical_pair_realizer_iff`,
     - `(x',y')` is separated by `L_extra`. ✓
     - All pairs in S' are comparable in R, hence in every extension of R. ✓
   - `d ≤ 2`. ✓

   **Sub-case (n=4): exactly one pair (a,b) incomparable in R1:**
   - `R2 := TC(R1 ∪ {(a,b)})` — valid by `add_incomparable_general` (a ∥_{R1} b).
   - `L1 := szpilrajn_theorem(R2)`.
   - `{L1, L_extra}` is a 2-element realizer: by `critical_pair_realizer_iff`,
     - `(x',y')`: L_extra. ✓
     - `(a,b)`: L1 has `a <_{L1} b` (since R2 forces it). ✓
     - Cross pairs `(x',a)`, `(x',b)`, `(y',a)`, `(y',b)` etc.: each is either
       (i) a comparable pair in R (handled by both extensions), or
       (ii) separated by L1 or L_extra via the critical pair axioms and R1/R2 structure. Detailed case analysis by `critical_down`/`critical_up` applied to each. ✓
   - `d ≤ 2`. ✓

   **Sub-case (n=5): up to three pairs in S' (3-element subposet):**
   - Same structure as n=4, iterated: apply `add_incomparable_general` for each incomparable pair in S' under the current R_i. At most 2 applications (3-element poset has at most 3 incomparable pairs, but each application may resolve others via transitivity).
   - `L1 := szpilrajn_theorem(R_final)`.
   - `{L1, L_extra}` is a 2-element realizer by the same `critical_pair_realizer_iff` argument, with the critical pair axioms handling cross-pairs. ✓

---

## Component D: Restructured induction

In both `hiraguchi_bound` and `hiraguchi_thm`, replace the `n=4,5` admit branch with an early guard:

```coq
(* At the top of the induction body, before the incomparable/chain split: *)
destruct (Nat.lt_ge_cases n 6) as [Hlt6 | Hge6].
- (* n ∈ {4, 5}: use small_hiraguchi directly *)
  assert (Hn45 : n = 4 \/ n = 5) by lia.
  exact (small_hiraguchi n d Hcard Hn45 Hdim).
- (* n ≥ 6: the existing incomparable/chain case split proceeds unchanged.
     IH is always applicable since pred(pred n) ≥ 4 when n ≥ 6. *)
  ...existing proof body...
```

This removes the `admit` at lines 864 and 971 entirely.

---

## New definitions and lemmas (summary)

| Name | Kind | Location | Depends on |
|------|------|----------|------------|
| `lift_and_force_is_poset` | Lemma | `Theorems.v` (before `extension_through_critical_pair`) | `IsCriticalPair`, `IsLinearExtension`, `add_incomparable_general` structure |
| `extension_through_critical_pair` | Lemma (replace Admitted) | `Theorems.v` line 797 | `lift_and_force_is_poset`, `szpilrajn_theorem`, `critical_pair_realizer_iff` |
| `small_hiraguchi` | Lemma | `Theorems.v` (before `hiraguchi_bound`) | `add_incomparable_general`, `szpilrajn_theorem`, `critical_pair_realizer_iff`, `incomparable_lifting_to_critical_pair` |
| Restructured guard in `hiraguchi_bound` | Edit | `Theorems.v` line 810ff | `small_hiraguchi` |
| Restructured guard in `hiraguchi_thm` | Edit | `Theorems.v` line 927ff | `small_hiraguchi` |

---

## Risk areas

- **`lift_and_force_is_poset`:** The path invariant has more cases than `add_incomparable_general` (because L'_lift adds many edges, not just one). The induction on TC paths must handle combinations of R-steps, L'_lift-steps, and the forced (x',y') step. Each case combination needs to be closed, which could be 10–15 sub-cases.

- **Injectivity of lift map:** Showing distinct L'₁,L'₂ give distinct L'₁_full,L'₂_full requires either direct restriction or a functional extensionality argument. May need to add a lemma that `szpilrajn_theorem` produces an extension that, when restricted to S', agrees with its input — this depends on how Szpilrajn is formulated (it may produce an arbitrary Zorn-maximal element, making restriction equality hard to prove).

- **Cross-pairs in `small_hiraguchi`:** The case analysis for pairs involving x' or y' in `critical_pair_realizer_iff` may require enumerating all pairs and applying critical_down/critical_up. For n=5 with 3-element S', this is up to 12 ordered cross-pairs. Tedious but mechanical.

- **`small_hiraguchi` n=5 multiple-incomparable-pair subcase:** The iterated `add_incomparable_general` applications must each verify incomparability in the *current* R_i, not just in R. Need lemmas that incomparability in R1 is preserved when adding unrelated pairs.

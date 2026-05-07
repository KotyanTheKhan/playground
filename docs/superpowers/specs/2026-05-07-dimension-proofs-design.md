# Design: Prove All Admits in `posets/dimension`

**Date:** 2026-05-07  
**Goal:** Close all ~27 `Admitted` lemmas in the `posets/dimension` submodule, with the primary objective of proving known theorems about poset dimension bounds.

---

## Overview

The `posets/dimension` submodule contains definitions and theorems about the Dushnik–Miller dimension of a poset: the minimum size of a realizer (a set of linear extensions whose intersection is the partial order). The admits span 6 files and range from trivial infrastructure to research-grade combinatorics. We use **Approach B: parallel tracks** to close them efficiently.

The four parallel tracks are:

1. **Foundation** — install `coq-zorns-lemma` and prove `szpilrajn_theorem` + `add_incomparable_is_poset`
2. **Infrastructure chain** — fix `subrelation_is_poset` and prove all supporting lemmas in `Theorems.v`
3. **Linear Sum + Critical Pairs** — self-contained combinatorial track
4. **Product + Subposet bounds** — `product_dimension_le` + `subposet_dimension_le`

`hiraguchi_bound` and `critical_pairs_reversible_iff_no_alternating_cycle` are developed last (deepest proofs, built on all prior infrastructure).

---

## Section 1: Setup & Foundation

### coq-zorns-lemma installation

- Run `mise exec -- opam install coq-zorns-lemma`
- Add `ZornsLemma` to `(theories Stdlib Posets Dilworth ZornsLemma)` in `posets/dimension/dune`
- Add `-R` mapping to `_CoqProject` for the zorns-lemma install path

### `szpilrajn_theorem` (Szpilrajn.v)

Consider the poset `(S, ⊆)` where `S` = all partial orders on A that extend R. Every chain in S has an upper bound (point-wise union). By Zorn's lemma (from `coq-zorns-lemma`), S has a maximal element M. If M is not total, there exist incomparable x, y in M; then `TC(M ∪ {(y,x)})` is a partial order extending M (by a helper lemma `add_incomparable_general` proved inline in `Szpilrajn.v`, identical in structure to `add_incomparable_is_poset` but parameterized over any base relation M rather than the fixed section R), contradicting maximality. Therefore M is a total order — a linear extension of R.

**Note:** `add_incomparable_is_poset` in `Theorems.v` is scoped to the section's R. For `szpilrajn_theorem`, prove `add_incomparable_general` as a free-standing lemma in `Szpilrajn.v` with signature `forall (A : Type) (M : A -> A -> Prop) (HP : IsPoset A M) x y, Incomparable M x y -> IsPoset A (TransitiveClosure (fun a b => M a b \/ (a = y /\ b = x)))`. The proof structure is identical.

### `add_incomparable_is_poset` (Theorems.v)

**Path invariant:** For any path `a →* b` in `TC(R ∪ {(y,x)})` where `Incomparable R x y`:

```
PathInv(a, b) := R a b  ∨  (R a y ∧ R x b)
```

**Proof of invariant by induction on the transitive closure:**
- Base: direct R-step gives left disjunct; the (y,x) edge gives R y y ∧ R x x (reflexivity), so right disjunct with a=y, b=x.
- Trans: given `a→*m` and `m→*b`, case-split on which disjunct holds for each half. The only problematic case is `R a y ∧ R x m` + `R m y ∧ R x b`, which requires `R x y` (transitivity via m). But `Incomparable R x y` means `¬R x y`, so this case is vacuous.

**Antisymmetry from invariant:** If `a→*b` and `b→*a`, each pair of disjuncts yields either `R a b ∧ R b a` (antisymmetry of R gives a=b) or forces `R x y` (contradiction). So a = b.

**Reflexivity and transitivity** are immediate from `tc_step` + `tc_trans`.

---

## Section 2: Infrastructure Chain (Theorems.v)

### Fix: `subrelation_is_poset`

Change the restricted relation from `fun x y => In S x ∧ In S y ∧ rel x y` to:

```coq
fun x y => x = y ∨ (In A S x ∧ In A S y ∧ rel x y)
```

This is reflexive (x=x always), antisymmetric (both disjuncts reduce to rel antisymmetry or eq), and transitive (case-split on which disjunct each step uses). All callers receive this fix automatically.

### `exists_minimal`

Three inline admits close as follows:
- **A0 empty case** (`exists x`): x is minimal in {x} because no other element is in {x}.
- **x not strictly below m** (`exists m`): show m is minimal in `Add A0 x` by case-split: y ∈ A0 uses IH minimality; y = x uses the negation of strict inequality.
- **x < m but x not minimal** (`exfalso`): ∃y ∈ A0 with y <_rel x; by transitivity y <_rel m; by minimality of m in A0, y = m; then rel m x and rel x m gives m = x by antisymmetry, contradicting x ≠ m.

### `add_minimal_to_linear_extension`

Construct `L` from `L'` (which extends rel on S\{m}) by placing m first:

```
L a b := (a = m) ∨ (b ≠ m ∧ L' a b)
```

Show L is a total order and extends the restriction of rel to S. Minimality of m ensures that placing m first is consistent with the poset order on S.

### `at_least_one_linear_extension_finite`

- `Finite A S` from `cardinal A S n`: use `cardinal_finite` from Stdlib.
- `Inhabited A S` when n = S(n'): cardinality S(n') means S is non-empty.
- `cardinal A (Subtract A S m) n'`: use `cardinal_Subtract_singleton` (m ∈ S, cardinal S (n'+1)).
- Base case (S empty): any total order (e.g., the section R itself extended by Szpilrajn) works — or construct the empty extension directly.

### `at_least_one_linear_extension`

Directly applies `szpilrajn_theorem` from `Szpilrajn.v` to R' with `HP'`.

### `all_linear_extensions_intersection`

- **Backward** (R x y → ∀L, L x y): immediate from `linear_extends`.
- **Forward** (∀L, L x y → R x y): by contrapositive. If ¬R x y:
  - If R y x and x ≠ y: any linear extension L has L y x; antisymmetry of L means ¬L x y; contradiction.
  - If Incomparable x y: by `incomparable_extension`, get L with L y x; antisymmetry gives ¬L x y; contradiction.

### `all_linear_extensions_finite`

Construct an injection from `AllLinearExtensions` into the finite set of permutations of A's elements:
1. From `cardinal A (Full_set A) n`, extract an enumeration `e : Fin.t n → A`.
2. Each linear extension L determines a unique permutation `σ : Fin.t n → Fin.t n` (the sorted order under L).
3. Show this map is injective: distinct linear extensions produce distinct permutations.
4. The set of permutations of `Fin.t n` is finite (proved by induction on n).
5. Apply `Finite_downward_closed` or injection-into-finite to conclude.

### `dushnik_miller_exists`

1. `AllLinearExtensions` is a finite realizer (by `all_linear_extensions_is_realizer` + `all_linear_extensions_finite`).
2. Let m be the cardinal of `AllLinearExtensions`. We have a realizer of size m.
3. Use strong induction (`Nat.strong_induction_on`) to find the minimum d ≤ m such that a realizer of size d exists.
4. Construct the `PosetDimension R d` instance: the witnessing realizer is the minimum-size one found; minimality of d follows by definition.

---

## Section 3: Main Bounds

### `subposet_dimension_le`

Given realizer `{L₁,...,L_d}` for P:
1. For each Lᵢ, define `Lᵢ|_S := fun x y => In S x ∧ In S y ∧ Lᵢ x y` — this is a linear extension of Q = R|_S (extends R|_S by construction; totality on S follows from totality of Lᵢ).
2. The set `{L₁|_S,...,L_d|_S}` has cardinality ≤ d (subset of a d-element set).
3. It is a realizer of Q: the intersection condition follows from `all_linear_extensions_intersection` applied to Q.
4. By minimality of d_q: d_q ≤ d = d_p.

### `hiraguchi_bound` (developed last)

Proof by strong induction on n.

**Base cases** n = 0,1,2,3: dimension is trivially ≤ 1 ≤ n/2 (for n ≤ 2, the poset is a chain or antichain; for n=3, direct case analysis gives dim ≤ 2 but n/2 = 1, so need n ≥ 4).

**Inductive step** (n ≥ 4): Take any incomparable pair (x, y) in R (exists since if all pairs comparable, P is a chain and dim = 1 ≤ n/2). Form:
- P' = TC(R ∪ {(x,y)}) — x ≤ y now added
- P'' = TC(R ∪ {(y,x)}) — y ≤ x now added

Key sub-lemmas:
- `dim(P) ≤ max(dim(P'), dim(P''))`: any critical pair of P that isn't in P' is in P''; combine their realizers.
- P' has at most n−1 incomparable pairs in "interesting" direction → dim(P') ≤ (n−1)/2 by applying induction to a subposet of size n−1 (removing the now-comparable x from the "antichain witness").
- Similarly for P''.
- So dim(P) ≤ (n−1)/2 + 1 when handled carefully; for n ≥ 4 this is ≤ n/2.

---

## Section 4: Critical Pairs (CriticalPairs.v)

### `incomparable_lifting_to_critical_pair`

Given incomparable (x, y), we need x' ≤ x, y ≤ y' with (x', y') a critical pair.

Define x' as a minimal element of `{a | R a x ∧ ¬R a y}` (elements below x that do NOT go below y). This set is non-empty (x itself is in it: R x x by reflexivity, and ¬R x y by incomparability). By `exists_minimal` applied to this finite set (or by classical choice in the infinite case), get x'.

Show x' is critical: `critical_down` holds by minimality; `critical_up` requires analogous argument on the "upward" side — define y' dually as a maximal element above y incomparable with x'.

### `critical_pair_realizer_iff`

**Forward** (realizer → separates critical pairs): Every realizer separates all incomparable pairs, and critical pairs are incomparable.

**Backward** (separates critical pairs → realizer): Given arbitrary incomparable (x, y), use `incomparable_lifting_to_critical_pair` to get (x', y') critical with R x' x and R y y'. The extension L that reverses (x', y') satisfies L y' x'; since R x' x and R y y', L also has L y x (transitivity via x' and y'). So the intersection is exactly R.

### `critical_pairs_reversible_iff_no_alternating_cycle`

**Forward** (cycle → no single linear extension reverses all pairs): An alternating cycle `(x₀,y₀),...,(xₖ,yₖ)` with `R xᵢ yᵢ₋₁` for each i creates a forced chain: any L reversing all pairs must have `L yₖ xₖ ... L y₀ x₀ ... L xₖ yₖ...`, giving a cycle in L which contradicts L being a partial order.

**Backward** (no cycle → extension exists): If S has no alternating cycle, then the relation `TC(R ∪ {(yᵢ, xᵢ) | (xᵢ,yᵢ) ∈ S})` is acyclic (a cycle would give an alternating cycle in S — proved by tracing the path structure). Therefore it's a partial order, and Szpilrajn gives the desired linear extension.

---

## Section 5: Linear Sum & Product Dimension

### `linear_sum_critical_pairs`

Inter-summand pairs (inl a, inr b) are always comparable (SumAB), so never critical. Critical pairs of A+B are exactly critical pairs within A (inl-inl) or within B (inr-inr). The `IsCriticalPair` conditions reduce exactly under the LinearSumRel inversion lemmas.

### `linear_sum_realizer_lifting`

Pad the smaller realizer with repeated copies of an arbitrary extension to match size `max(na, nb)`. For index i, combine `LA_i` and `LB_i` into:

```
L (inl a1) (inl a2) := LA_i a1 a2
L (inr b1) (inr b2) := LB_i b1 b2
L (inl _) (inr _)   := True
L (inr _) (inl _)   := False
```

Totality and extension follow directly. Realizer intersection: any pair in `A+B` that is incomparable in `LinearSumRel` must be inl-inl or inr-inr (inl-inr are always comparable); the corresponding A or B realizer then separates it.

### `linear_sum_dimension`

- **Upper bound** `dSum ≤ max(dA, dB)`: directly from `linear_sum_realizer_lifting` + minimality of `dSum`.
- **Lower bound** `dA ≤ dSum` and `dB ≤ dSum`: any realizer of A+B projects onto a realizer of A (by restricting each extension to inl-inl pairs) with the same size. So dA ≤ dSum; symmetrically dB ≤ dSum; hence max(dA,dB) ≤ dSum.

### `product_dimension_le`

Build a realizer of A×B of size dA+dB. Fix arbitrary `LA₀` (extension of A) and `LB₀` (extension of B).

For i = 1..dA, define:
```
Li(a1,b1)(a2,b2) := LA_i a1 a2  ∨  (a1 = a2  ∧  LB₀ b1 b2)
```

For j = 1..dB, define:
```
Lj'(a1,b1)(a2,b2) := LA₀ a1 a2  ∨  (a1 = a2  ∧  LB_j b1 b2)
```

Each is a total order on A×B (lex order). Together they form a realizer: for any incomparable pair (a1,b1)‖(a2,b2) in ProductRel, either RA a1 a2 fails (some LA_i reverses it, handled by the Li set) or RB b1 b2 fails (some LB_j reverses it, handled by the Lj' set). The combined collection has size dA+dB; by minimality dProd ≤ dA+dB.

---

## Implementation Strategy

- **Parallel tracks** (Tracks 1–4 above) are independent and can be executed in parallel agents.
- `hiraguchi_bound` and `critical_pairs_reversible_iff_no_alternating_cycle` are developed in a final sequential pass after all infrastructure is in place.
- Run `mise build` after each track completes to catch cross-module import errors.
- Use `rocq_query` MCP tool for `Search`/`Check` to surface Stdlib lemmas during implementation.

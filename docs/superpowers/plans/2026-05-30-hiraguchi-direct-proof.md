# Hiraguchi's bound `dim(P) ≤ ⌊n/2⌋` — direct proof (no removable pairs)

> REQUIRED SUB-SKILL: long-running-formalization. Multi-session, research-grade.

**Goal:** Replace the current `hiraguchi_bound` proof (which routes through
`non_antichain_removable_pair_exists` = the OPEN Removable Pair Conjecture) with
the *independent* proof of Hiraguchi's inequality (Hiraguchi/Kimble/Trotter), so
`hiraguchi_bound` becomes admit-free.

**Architecture:** The "modern proof" (Trotter, "Dimension for Posets and
Chromatic Number for Graphs", Thm 5.2) reduces `dim ≤ ⌊n/2⌋` to two lemmas:

- **Lemma 5.4** `dim(P) ≤ width(P)`.  ✅ ALREADY PROVEN: `dimension_le_width`
  in `posets/dimension/WidthBound.v` (Qed).
- **Lemma 5.6** `dim(P) ≤ max{2, |P − A|}` for a **maximal** antichain `A`.
  ← the SOLE new mathematical content. Refs: Kimble thesis [33]; Trotter,
  "Inequalities in dimension theory for posets", Proc. AMS 1975 [46].

**Combination (pure arithmetic, airtight).** Let `N = |P| ≥ 4`, `w = width(P)`,
`A` = a maximum antichain (`|A| = w`, and maximum ⟹ maximal). Then `|P−A| = N−w`.
- 5.4 ⟹ `dim ≤ w`.
- 5.6 ⟹ `dim ≤ max{2, N−w}`.
- If `w ≤ ⌊N/2⌋`: `dim ≤ w ≤ ⌊N/2⌋`.
- Else `w ≥ ⌊N/2⌋+1` ⟹ `N−w ≤ ⌈N/2⌉−1 ≤ ⌊N/2⌋`, and since `N≥4 ⟹ ⌊N/2⌋≥2`,
  `max{2,N−w} ≤ ⌊N/2⌋`.
- Either way `dim ≤ ⌊N/2⌋`. ∎

**Why this is sound (vs. the deleted approach):** Hiraguchi's bound is a proven
theorem; the Removable Pair Conjecture "would imply it" but the bound does NOT
depend on it. This route uses only proven lemmas. (Verified against West's
open-problems list + Trotter's survey, 2026-05-30.)

---

## Tech stack / existing infrastructure

- `PosetDimension R d`, `IsRealizer`, `IsLinearExtension`, `IsTotalOrder`
  (`DimDefs.v`).
- `dimension_le_width : cardinal (Full A) n → PosetDimension R d →
  Width R (Full A) w → d ≤ w` (`WidthBound.v`, Qed).
- `Width`, `IsAntichain`, `largest_antichain_is_maximum` (`dilworth/Definitions.v`);
  Dilworth (`dilworth/`).
- Antichain dimension ≤ 2 facts + small-case `hiraguchi_small_case`
  (`RemovablePairs.v`).
- Szpilrajn (`Szpilrajn.v`); `subposet_dimension_le` (`Theorems.v`).

---

## Tasks

### Task 0: Obtain the exact proof of Lemma 5.6  ✅ DONE (2026-05-30)

Got the full primary source: **Trotter 1975** (AMS free PDF, saved to
`docs/references/trotter-1975-inequalities-dimension.pdf`; the JSTOR DOI
10.2307/2039736 redirects to AMS `S0002-9939-1975-0369192-2`). The proof is
SIMPLE and inductive — NOT the "split all points" simultaneous construction.
Trotter's actual argument (his Theorem 2 = our Lemma 5.6):

- **Inequality (1)** [one-point removal]: `dim X ≤ 1 + dim(X − x)` for any point
  `x`. Construction: let `{L_1,…,L_d}` realize `Q = X − x`, `D(x)`=points `< x`,
  `U(x)`=points `> x` (in `Q`). Take `M_i` (`i∈[d−1]`) = any linear extension of
  `X` restricting to `L_i`; and
    `M_d     = L_d(D(x)) < x < L_d(Q − D(x))`   (x as LOW as possible),
    `M_{d+1} = L_d(Q − U(x)) < x < L_d(U(x))`   (x as HIGH as possible).
  Then `{M_1,…,M_{d+1}}` realizes `X`. (d+1 extensions.)
- **Lemma 3** [base case]: if `A` is an antichain and `|X − A| = 2`, then
  `dim X = 2` (`≤ 2`). Trotter: such `X` embeds in one of finitely many posets,
  all of dimension 2 (Figure 1). Formalize via a direct 2-realizer OR the
  finite analysis.
- **Theorem 2** [our 5.6]: if `A` antichain and `|X − A| ≥ 2`, then
  `dim X ≤ |X − A|`. Induct on `|X − A|`: remove a point `x ∈ X − A` (keeps `A`
  an antichain, `|(X−x) − A| = |X−A| − 1`); base case `|X−A| = 2` is Lemma 3;
  step uses inequality (1): `dim X ≤ 1 + dim(X−x) ≤ 1 + (|X−A|−1) = |X−A|`.
  Tight because the induction stops at 2 (dim 2), not 0.

(Note: `max{2, |X−A|}` only matters for `|X−A| ≤ 1`, i.e. `X` is an antichain or
antichain+1 point — both `dim ≤ 2`, already in repo.)

### Task 1: Formalize the pieces (new file e.g. `AntichainDimBound.v`)
In dependency order, each a small Qed lemma:
1. **`dim_le_succ_remove_point`**: `dim X ≤ 1 + dim(X − x)` via the realizer
   construction above (insert `x` low/high into one extension; the rest extend
   arbitrarily). The genuine plumbing: point-insertion into a linear extension +
   proving the d+1 extensions intersect to `P`. Work in the subtype framework
   (`{a | In (Full ∖ {x}) a}`) used by `subposet_dimension_le`.
2. **`antichain_plus_two_dim_le_2`** (Lemma 3): `A` antichain, `|X−A|=2` ⟹
   `dim ≤ 2`. Build an explicit 2-realizer (2 linear extensions) of such an `X`.
3. **`antichain_complement_dim_bound`** (Theorem 2): induction on `|X−A|`.

### Task 2: New `hiraguchi_bound` proof
In a new section/file, prove `dim ≤ ⌊n/2⌋` from `dimension_le_width` + Lemma 5.6
+ the arithmetic above. Wire `hiraguchi_bound` to it; drop the dependency on
`non_antichain_removable_pair_exists` and `hiraguchi_helper`'s removable-pair
induction.

### Task 3: Verify & cleanup
- `Print Assumptions hiraguchi_bound` → only standard classical axioms (NO
  `non_antichain_removable_pair_exists`).
- Keep `RemovablePairConjecture` as the documented open problem (used by nothing).
- Whole-project build green; update INDEX.md (`hiraguchi_bound` now independent).

---

## Risk register
- **Lemma 5.6 construction is the genuine content** and is error-prone; a wrong
  construction = another false admit. Mitigation: Task 0 gate + example checks +
  proof-skeptic review BEFORE Coq.
- Critical-pair / realizer bookkeeping in Coq is heavy; keep `AntichainDimBound.v`
  decomposed into small Qed lemmas (<500 lines/file).
- Sources: Trotter [46] Proc AMS 1975, Kimble [33] MIT thesis 1973 may be
  paywalled; survey `trotter.math.gatech.edu/papers/149` (downloaded to ~/tmp)
  gives the lemma statements + the combination but states 5.6 as an exercise.

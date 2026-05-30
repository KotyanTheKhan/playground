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

### Task 0: Obtain & verify the exact proof of Lemma 5.6  ← GATING

Do NOT write Coq for 5.6 until the construction is pinned down from a primary
source (Trotter [46] / Kimble [33]) or reconstructed AND verified on the standard
example `S_k` and on small posets. The realizer construction "splits all points
of `P − A`": one linear extension per element of `P − A`, reusing them to reverse
the antichain `A`'s internal pairs (needs `max{2, n}`, not `n+2` — iterating
one-point removal Thm 5.1 is OFF BY ONE for Hiraguchi, so the tight `5.6` is
essential).
- Deliverable: a written, example-checked statement + proof skeleton of 5.6 in
  this plan, reviewed by `proof-skeptic` before any Coq.

### Task 1: Formalize Lemma 5.6 (new file `AntichainDimBound.v`)
`forall A maximal antichain, n=|P−A| → dim(P) ≤ max{2, n}` (realizer form:
build a size-`max{2,n}` realizer of `R`). Decompose into:
- partition `P = A ⊔ D(A) ⊔ U(A)` for a maximal antichain (Qed plumbing);
- the per-element linear-extension construction + verification it reverses every
  critical/incomparable pair (the deep part);
- assemble realizer + cardinality `max{2,n}`.

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

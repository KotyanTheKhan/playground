# Finish `dimension_finish`: prune to the sound core, then squash-merge

**Date:** 2026-05-31
**Branch:** `dimension_finish` → `main`
**Status:** approved (design)

## Goal

The `posets/dimension` module has grown to 217 files / ~81K lines. The bulk of
that — the N5/RemovablePairs investigation — exists only to support a
*superseded* proof of Hiraguchi's bound that depends on the **OPEN** Removable
Pair Conjecture. The sound, current result `hiraguchi_bound_direct` does not
need any of it.

Eliminate the compile-time/memory problem by **deleting the superseded heavy
subtree** (preserved first on a backup tag), removing dead code, leaving a
minimal **fully-sound** dimension theory. Then squash-merge to `main`.

## Verified dependency facts

- `RemovablePairs.v` is a **leaf**: nothing `Require`s it. It pulls in
  `N4Realizers N5Realizers N5Dispatcher CriticalPairDigraph` (the whole heavy
  machinery).
- The sound `hiraguchi_bound_direct` (`HiraguchiDirect.v`) closure is 12 small
  files; none import `RemovablePairs` or any N5 module.
- Nothing **outside** `posets/dimension` imports any delete-set module.
- `AntichainDimBound.v` defines two lemmas: `hiraguchi_combine` (Qed, **used**
  by the sound proof) and `dim_le_antichain_complement` (Admitted, **unused** —
  0 references anywhere). The latter is dead.
- The keep/delete partition has **no cross-edges** (no kept file depends on a
  deleted file).

## KEEP — 12 files, ~5.5K lines (theory `Dimension`)

`DimDefs · Szpilrajn · CriticalPairs · Theorems · WidthBound ·
AntichainDimBound* · AntichainComplement · WidthExists · OnePointRemoval ·
HiraguchiDirect · LinearSum · ProductDimension`

Retained results: `hiraguchi_bound_direct`, `dimension_le_width`,
`one_point_removal`, `antichain_complement_dim_bound`, `width_exists`,
linear-sum & product dimension bounds, Szpilrajn realizer existence.

**Exactly one honest admit remains:** `small_complement_le_2`
(`AntichainComplement.v`, Trotter Lemma 3 finite base case — TRUE).

\* `AntichainDimBound.v` is kept, but the dead `dim_le_antichain_complement`
admit lemma is deleted in-place; `hiraguchi_combine` stays.

## DELETE — 205 files, ~75.5K lines

The entire `RemovablePairs` closure:
`N5Realizers` (28K), `N4Realizers` (7K), 76 `N5Dispatcher*` (24.5K), all of
`N5Exhaustive/`, `CriticalPairDigraph`, `TrotterCounterexample`,
`RemovablePairs` itself.

This carries away the superseded `hiraguchi_bound`, the `RemovablePairConjecture`
statement, and its OPEN-conjecture admit `non_antichain_removable_pair_exists`.

## Preservation (BEFORE any deletion)

Annotated tag at current `dimension_finish` HEAD:
`archive/dimension-n5-full`, **pushed to origin**. The full N5 work stays
recoverable.

## Build / structure changes

- Remove `posets/dimension/N5Exhaustive/` directory entirely.
- Simplify `posets/dimension/dune`: drop `(include_subdirs qualified)` once no
  subdirs remain; keep `(theories Stdlib Posets Dilworth ZornsLemma)`.
- No `very-all` target needed — with the heavy subtree gone the default build is
  fast, so the simpler outcome wins.
- Update `docs/INDEX.md` dimension section: drop deleted theorems and the
  Open-problems rows tied to deleted files; mark `hiraguchi_bound_direct` as the
  headline result with its single admit.

## Optional optimization (measure-first, may defer)

`Theorems.v` is 2,429 lines (over the 500-line fast-compile guideline). After
the prune, measure its compile time; split only if it is an actual bottleneck.

## Verification

- Whole-project build via `bash .claude/scripts/timed-build.sh 1800 @all 4`;
  confirm green and record the new wall-clock vs. the old.
- `Print Assumptions hiraguchi_bound_direct` → standard classical axioms +
  `small_complement_le_2` only (no Removable Pair Conjecture).

## Merge

Squash-merge `dimension_finish` → `main` with a comprehensive message
summarizing the sound result and the prune. (User pauses here for final
confirmation before the merge — it is the irreversible, outward-facing step.)

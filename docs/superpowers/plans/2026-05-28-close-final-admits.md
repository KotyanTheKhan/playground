# Plan: Close the 2 Remaining Admits — Session-by-Session

**Date:** 2026-05-28
**Goal:** Reduce admit count from 2 to 0 across multiple multi-hour sessions.
**Constraint:** Each new file must compile in <5 minutes. No file >500 lines.

## Live status

See `docs/superpowers/specs/2026-05-28-status.md` for live progress tracking.

**Track N**: N1 ✅, N2 ✅, N3 ✅, N4 ✅, N5 ⚠️ BLOCKED (admit placeholder), N6-N9 ⏸ TODO
**Track T**: T1-T5 ⏸ TODO
**Current admit count**: 3 (target: 0)

---

## Session-based structure

Each session below is **2-4 hours of focused work** with a SINGLE clear deliverable. Sessions are designed so that:
- Each ends with a committed, building Coq state.
- The next session can start cold with only the plan + commit hash.
- Sessions within a track build on each other; sessions across tracks are independent.

---

## Brainstorming summary

### Target admits

1. **`trotter_coverage_via_extremality`** (RemovablePairs.v:1688)
   - Claims: for every `(p, q) ∈ boundary`, there exists `L' ∈ r'` with `(p, q) ∈ greedy_acyclic_subset S' x' y' L' nil boundary`.
   - Trotter Ch.6 Theorem 6.1 coverage step.

2. **`n5_residual_classes_two_realizer`** (N5DispatcherShapes.v:38)
   - Catch-all for n=5 non-antichain non-chain configurations the dispatcher cascade doesn't enumerate.
   - 276 call sites across N5Dispatcher_*.v files.

### Approaches chosen

- **For Trotter:** CP-refinement chain. If (p, q) excluded by greedy for L', there's a "shadow" CP (p', q') with R p' p ∧ R q q' already in the accumulator. By extremality, this chain terminates at (x', y'). Coverage follows.

- **For n5_residual:** Edge-count exhaustiveness. Count strict edges, exhaustively case-split into named iso classes for each count.

---

## File structure

```
posets/dimension/
  Trotter/                           ← NEW subdirectory
    CoverageRefinement.v
    GreedyExcluded.v
    CycleStructure.v
    ExtremalityContradiction.v
    CoverageProof.v
  N5Exhaustive/                      ← NEW subdirectory
    EdgeCount.v
    EdgeCount1.v
    EdgeCount2.v
    EdgeCount3.v
    EdgeCount4.v
    EdgeCount5.v
    EdgeCount6_9.v
    Exhaustive.v
```

Each file independent (parallel compilation), each <500 lines, no Qed exceeds 30 min.

---

# Track N (n5_residual) — 9 sessions

**Per-session time: 2-3 hours.** Sessions can be done in any order EXCEPT N9 (must be last).

## Session N1: Edge counter + bounds (2 hours)

**Goal:** Define `edge_count_5` and prove its basic properties.

**File:** `posets/dimension/N5Exhaustive/EdgeCount.v` (~150 lines)

**Deliverables (all Qed):**
- [ ] `edge_count_5 : (B -> B -> Prop) -> B -> B -> B -> B -> B -> nat` — sums 20 indicators for ordered pairs (a,b), (b,a), (a,c), etc.
- [ ] `edge_count_5_le_10`: with antisymmetry, count ≤ 10 (each unordered pair contributes at most 1).
- [ ] `non_antichain_iff_edge_count_pos`: `~ (forall a b, R2 a b -> a = b) <-> edge_count_5 R2 a b c d e >= 1`.
- [ ] `non_chain_iff_edge_count_lt_10`: similar.

**Exit criteria:**
- File compiles in <5 min.
- 4 Qed lemmas committed.
- `mise build` green.

**Session entry:** Read commit `0b7eb2b` plan. Start fresh, no context needed beyond Coq Stdlib + project headers.

**Session commit:** `feat(N5Exhaustive): edge counter for 5-element posets`.

---

## Session N2: Edge count = 1 case (1 hour)

**Goal:** Prove that with exactly 1 strict edge, R2 matches `n5_one_edge_two_realizer`.

**File:** `posets/dimension/N5Exhaustive/EdgeCount1.v` (~100 lines)

**Deliverables:**
- [ ] Lemma `n5_edge_count_1_two_realizer` (Qed): if `edge_count_5 = 1`, applies `n5_one_edge_two_realizer`.

**Exit criteria:** File compiles in <5 min. 1 Qed.

**Session commit:** `feat(N5Exhaustive): edge_count = 1 closes via one_edge`.

---

## Session N3: Edge count = 2 case (3 hours)

**Goal:** With 2 strict edges, R2 is V-shape, ∧-shape, or 2 disjoint edges.

**File:** `posets/dimension/N5Exhaustive/EdgeCount2.v` (~250 lines)

**Deliverables:**
- [ ] Sub-lemma: 2 edges sharing source → V-shape → apply `n5_V_plus_2isolated_two_realizer`.
- [ ] Sub-lemma: 2 edges sharing target → ∧-shape.
- [ ] Sub-lemma: 2 disjoint edges → `n5_disjoint_chains_plus_isolated_two_realizer`.
- [ ] Main lemma `n5_edge_count_2_two_realizer` combining them.

**Exit criteria:** File compiles in <5 min. 4 Qed lemmas.

**Session commit:** `feat(N5Exhaustive): edge_count = 2 case complete`.

---

## Session N4: Edge count = 3 case (3 hours)

**Goal:** With 3 strict edges, R2 is chain-3, N-shape, 3-claw-up, or 3-claw-down.

**File:** `posets/dimension/N5Exhaustive/EdgeCount3.v` (~400 lines)

**Deliverables:**
- [ ] 4 sub-lemmas (one per iso class).
- [ ] Main `n5_edge_count_3_two_realizer`.

**Exit criteria:** File compiles in <10 min. Multiple Qed lemmas.

**Session commit:** `feat(N5Exhaustive): edge_count = 3 case complete`.

---

## Session N5: Edge count = 4 case (3 hours)

**Goal:** 4 edges → bowtie, chain3+below, chain3+above, or other shapes.

**File:** `posets/dimension/N5Exhaustive/EdgeCount4.v` (~400 lines)

**Same structure as N4.**

**Session commit:** `feat(N5Exhaustive): edge_count = 4 case complete`.

---

## Session N6: Edge count = 5 case (3 hours)

**Goal:** 5 edges → diamond, Y-shapes, etc.

**File:** `posets/dimension/N5Exhaustive/EdgeCount5.v` (~400 lines)

**Session commit:** `feat(N5Exhaustive): edge_count = 5 case complete`.

---

## Session N7: Edge counts 6-9 combined (3 hours)

**Goal:** Handle denser posets (close to chain).

**File:** `posets/dimension/N5Exhaustive/EdgeCount6_9.v` (~400 lines)

**Deliverables:**
- [ ] Case ec=6: usually chain4 + variant.
- [ ] Case ec=7-9: progressively denser; use existing per-class lemmas (chain4_pendant, etc.).

**Session commit:** `feat(N5Exhaustive): edge_count 6-9 cases complete`.

---

## Session N8: Compose into exhaustiveness theorem (2 hours)

**Goal:** Combine N1-N7 into the final lemma.

**File:** `posets/dimension/N5Exhaustive/Exhaustive.v` (~150 lines)

**Deliverables:**
- [ ] `n5_residual_exhaustive` (Qed): the main exhaustiveness theorem.
  - Statement: same as `n5_residual_classes_two_realizer`'s claim.
  - Proof: extract elements, compute `edge_count_5`, case-split on value, apply N2-N7 sub-lemmas.

**Session commit:** `feat(N5Exhaustive): main exhaustiveness theorem (Qed)`.

---

## Session N9: Replace the admit (1 hour)

**Goal:** Replace `n5_residual_classes_two_realizer` Admitted with Qed via N8.

**Files modified:** `posets/dimension/N5DispatcherShapes.v`.

**Deliverables:**
- [ ] Remove `Admitted.` of `n5_residual_classes_two_realizer`.
- [ ] Replace with `Proof. exact n5_residual_exhaustive. Qed.` (or direct port).
- [ ] Verify `mise build` green.
- [ ] Verify the 276 call sites still resolve.

**Session commit:** `refactor(N5DispatcherShapes): close residual admit via N5Exhaustive`.

**MAJOR MILESTONE:** N5 admit closed. 2 → 1 admit.

---

# Track T (Trotter) — 5 sessions

**Per-session time: 2-4 hours.** Sessions T1-T4 must be done in order. T5 last.

## Session T1: CP-refinement preorder + well-foundedness (3 hours)

**Goal:** Set up the structural framework for Trotter's termination argument.

**File:** `posets/dimension/Trotter/CoverageRefinement.v` (~200 lines)

**Deliverables (all Qed):**
- [ ] `cp_le_strict`: strict variant of `cp_le` (use existing `cp_le` from CriticalPairDigraph.v).
- [ ] `cp_le_strict_irreflexive`: `cp_le_strict x y -> x <> y`.
- [ ] `cp_le_strict_finite_chain_terminates`: any chain x1 ≺ x2 ≺ ... in `cp_le_strict` on a finite poset is finite.
- [ ] (Optional) `well_founded cp_le_strict`.

**Strategy:** Use `Finite` + induction on cardinality. Each step in a `cp_le_strict` chain strictly reduces the count of unvisited CPs above (or below) the current pair.

**Exit criteria:** File compiles in <5 min. ≥3 Qed.

**Session commit:** `feat(Trotter): CP-refinement preorder + finite termination`.

---

## Session T2: Greedy exclusion characterization (3 hours)

**Goal:** Show `greedy_acyclic_subset` excludes `(p, q)` only when adding it would create a cycle.

**File:** `posets/dimension/Trotter/GreedyExcluded.v` (~250 lines)

**Deliverables:**
- [ ] `greedy_excluded_iff_cycle`: `(p, q) ∉ greedy ... boundary ↔ adding (q, p) creates a cycle in aug_step acc`.
- [ ] `cycle_at_step_implies_witness`: when a cycle exists, there's a concrete path through the augmented relation.

**Strategy:** Induction on the boundary list in the Fixpoint definition.

**Exit criteria:** File compiles in <10 min. ≥2 Qed.

**Session commit:** `feat(Trotter): greedy exclusion ↔ cycle characterization`.

---

## Session T3: Cycle structure analysis (4 hours)

**Goal:** Characterize the structure of cycles in `aug_step L' acc`.

**File:** `posets/dimension/Trotter/CycleStructure.v` (~300 lines)

**Deliverables:**
- [ ] `cycle_implies_shadow_cp`: a cycle through `(q, p)` in aug_step exposes a CP `(p', q')` with `R p' p ∧ R q q'`.
- [ ] `shadow_cp_in_accumulator`: the shadow CP was already added to acc by the greedy step.

**Strategy:** Case-analyze the cycle's edges. R-edges go "up", L'-lift edges respect L'-order, the `(x', y')` edge is fixed. Any cycle must contain at least one R-edge and one L'-lift edge crossing the boundary CP.

**Exit criteria:** File compiles in <15 min. ≥2 Qed.

**Session commit:** `feat(Trotter): cycle structure via shadow CP`.

---

## Session T4: Extremality contradiction (3 hours)

**Goal:** Close the loop: shadow CP chain + extremality → False.

**File:** `posets/dimension/Trotter/ExtremalityContradiction.v` (~250 lines)

**Deliverables:**
- [ ] `shadow_chain_terminates_at_extremal`: iterating the shadow CP relationship hits `(x', y')` (via extremality).
- [ ] `excluded_by_all_iff_chain_to_extremal`: `(p, q)` excluded by every L' iff there's a chain from `(p, q)` to `(x', y')` in CP-refinement.
- [ ] `cp_chain_to_extremal_means_eq`: by extremality, any chain ending at `(x', y')` started at `(x', y')`.
- [ ] Final contradiction: `(p, q) ∈ boundary` excludes `(x', y')`, so the chain has length > 0, but extremality forces `(p, q) = (x', y')`. Contradiction.

**Exit criteria:** File compiles in <10 min. ≥3 Qed.

**Session commit:** `feat(Trotter): extremality contradiction for excluded-by-all`.

---

## Session T5: Main coverage proof (2 hours)

**Goal:** Compose T1-T4 into the main lemma.

**File:** `posets/dimension/Trotter/CoverageProof.v` (~150 lines)

**Deliverables:**
- [ ] `trotter_coverage_main` (Qed): the statement of `trotter_coverage_via_extremality` proven via T1-T4.

**Then:** modify `posets/dimension/RemovablePairs.v`:
- [ ] Replace the `Admitted.` of `trotter_coverage_via_extremality` with `Proof. exact trotter_coverage_main. Qed.`
- [ ] Update imports.

**Session commit:** `refactor(RemovablePairs): close trotter_coverage_via_extremality (Qed)`.

**MAJOR MILESTONE:** Trotter admit closed. 1 → 0 admits.

---

# Cross-track session N8/T5 (final integration, 1 hour)

After BOTH tracks complete:

**Goal:** Verify everything is clean.

**Deliverables:**
- [ ] `grep -rn "Admitted\.$" posets/dimension/` returns nothing.
- [ ] `mise build` green.
- [ ] Update INDEX.md or top-level documentation.
- [ ] Commit final state with explicit Qed verification.

---

# Session execution playbook

## Per-session checklist (start of session)

1. `git pull` (or sync with last session's commit).
2. `git status` clean.
3. `mise build` should be green at start.
4. Open the session's target file path; create with header.
5. Read sibling files for context (e.g., relevant per-class lemmas).

## Per-session checklist (end of session)

1. Compile target file: `opam exec -- dune build <file>.vo` with 5-min timeout.
2. If exceeds 5 min, split the file further.
3. Run `mise build` (full project) — must remain green.
4. Commit with the session's commit message.
5. Update this plan: check off completed deliverables.

---

# Risk register & mitigations

### Risk T-1: cp_le chain doesn't terminate
**Mitigation:** Show termination via finite cardinality + acyclicity. Worst case: split T1 into 2 sessions.

### Risk T-3: Cycle structure analysis is hairy
**Mitigation:** Use case analysis on edge type. Each case ~30 lines. If T3 grows beyond 500 lines, split into T3a/T3b.

### Risk N-3/4/5/6/7: Edge-count cases don't cleanly map to iso classes
**Mitigation:** Use Phase A1's Python enumeration data (already in `scripts/iso_classes_all.txt`) as ground truth. For each edge-count bucket, list the iso classes upfront.

### Risk N-9 / T-5: Final composition reveals signature mismatches
**Mitigation:** Each track ends with a "compose" session that's only 1-2 hours. Plenty of margin to adapt signatures.

---

# Total effort estimate

| Track | Sessions | Hours |
|-------|----------|-------|
| N (n5) | 9 | 23 hours |
| T (Trotter) | 5 | 15 hours |
| Final | 1 | 1 hour |
| **Total** | **15** | **~39 hours** |

**At 1-2 sessions per day:** 8-15 days of focused work.

**Each session is independently committable** — partial progress always lands a green build.

---

# Stopping criteria

- **Hard stop:** any session that exceeds its time budget by 2x → restructure (split into more sessions).
- **Soft stop:** if 3 consecutive sessions in one track fail to converge → revisit the approach for that admit.
- **Success:** `grep -rn "Admitted\.$" posets/dimension/` empty → DONE.

---

# Execution kickoff

Start with **Session N1** (lowest-risk, foundational): build the edge counter.

After N1 lands, parallel work possible: any N2-N7 can be done independently.

After N9 lands (n5 admit closed), start Track T from T1.

Document each session's completion in this file (check the boxes).

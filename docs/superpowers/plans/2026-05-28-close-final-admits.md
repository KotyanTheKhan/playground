# Plan: Close the 2 Remaining Admits

**Date:** 2026-05-28
**Goal:** Reduce admit count from 2 to 0.
**Constraint:** Each new file must compile in <5 minutes. No file >500 lines.

---

## Brainstorming summary

### Target admits

1. **`trotter_coverage_via_extremality`** (RemovablePairs.v:1688)
   - Claims: for every `(p, q) ∈ boundary`, there exists `L' ∈ r'` with `(p, q) ∈ greedy_acyclic_subset S' x' y' L' nil boundary`.
   - This is the deep Trotter Ch.6 Theorem 6.1 coverage step.

2. **`n5_residual_classes_two_realizer`** (N5DispatcherShapes.v:38)
   - Catch-all for n=5 non-antichain non-chain configurations the dispatcher cascade doesn't enumerate.
   - 276 call sites across N5Dispatcher_*.v files.

### Approaches considered

**For Trotter:**
- **Direct Trotter Ch.6 formalization** — long path, multi-week.
- **Structural induction on boundary list** — recursive contradiction.
- **CP-refinement chain argument** — uses extremality directly.

**Chosen approach:** CP-refinement chain. Trotter's actual argument: if (p, q) is excluded by greedy for some L', then there's a CP (p', q') with R p' p AND R q q' that was already in the accumulator. By extremality, this chain of refinements must terminate, contradicting "excluded by every L'".

**For n5_residual:**
- **Per-call-site closure** — 276 sites, infeasible manually.
- **Edge-count exhaustiveness theorem** — single meta-lemma routing all call sites.
- **Direct construction of removable pair** — circular with Hiraguchi.

**Chosen approach:** Edge-count exhaustiveness. Define a counter function, prove `forall R2 on 5 elements with ≥2 strict edges, edge_count(R2) ∈ {2, 3, ..., 9}` and for each count exhaustively case-split into named iso classes.

---

## File structure (avoid long compiles)

```
posets/dimension/
  Trotter/                           ← NEW subdirectory
    CoverageRefinement.v             — CP-refinement preorder lemmas (~200 lines)
    GreedyExcluded.v                 — Greedy exclusion implies cycle (~250 lines)
    CycleStructure.v                 — Cycle analysis under acyclicity invariant (~300 lines)
    ExtremalityContradiction.v       — Termination via extremal CP (~250 lines)
    CoverageProof.v                  — Main Qed proof of trotter_coverage_via_extremality (~150 lines)
  
  N5Exhaustive/                      ← NEW subdirectory
    EdgeCount.v                      — Define edge_count + bounds (~150 lines)
    EdgeCount1.v                     — n=5, ec=1 case: route to n5_one_edge (~100 lines)
    EdgeCount2.v                     — n=5, ec=2 case: V/inv-V/disjoint (~250 lines)
    EdgeCount3.v                     — n=5, ec=3 case (~400 lines)
    EdgeCount4.v                     — n=5, ec=4 case (~400 lines)
    EdgeCount5.v                     — n=5, ec=5 case (~400 lines)
    EdgeCount6_9.v                   — n=5, ec=6..9 case (smaller — denser posets) (~400 lines)
    Exhaustive.v                     — Main Qed of n5_residual_classes_two_realizer (~150 lines)
```

Each file independent (parallel compilation), each <500 lines, no Qed exceeds 30 min.

---

## Phase T (Trotter) — 5 sub-files

### Phase T1: CoverageRefinement.v

**Goal:** Formalize the CP-refinement preorder needed for termination.

- Re-import `cp_le`, `cp_le_refl`, `cp_le_trans` from `CriticalPairDigraph.v`.
- Prove `cp_le_finite_chain_terminates`: any chain of `cp_le`-strict refinements on a finite poset terminates.
- Prove `cp_le_strict_irreflexive_under_extremality`: under `IsExtremalCP R x' y'`, the strict refinement preorder has no cycle.

**Tasks:**
- [ ] Define `cp_le_strict` (strict version of `cp_le`).
- [ ] Prove `cp_le_strict_acyclic_via_extremality` (Qed).
- [ ] Prove well-foundedness of `cp_le_strict`.

### Phase T2: GreedyExcluded.v

**Goal:** Characterize when greedy excludes a pair.

**Statement:** `greedy_acyclic_subset` excludes `(p, q)` iff adding `(p, q)` to the current accumulator creates a cycle in `aug_step L' acc`.

**Tasks:**
- [ ] Prove `greedy_excludes_iff_creates_cycle` (Qed).
- [ ] Prove a cycle in `aug_step` implies existence of a specific structural pattern (involving R-paths + L'-lift paths).

### Phase T3: CycleStructure.v

**Goal:** Analyze the structure of cycles in `aug_step`.

**Statement:** A cycle in `aug_step L' acc` with `(p, q)` involves a "shadow" CP `(p', q')` such that `R p' p ∧ R q q'`.

**Tasks:**
- [ ] Define `shadow_cp` predicate.
- [ ] Prove `cycle_implies_shadow_cp` (Qed).
- [ ] Prove `shadow_cp_in_accumulator`: the shadow CP is already in `acc`.

### Phase T4: ExtremalityContradiction.v

**Goal:** Use extremality to bound shadow-CP chains.

**Statement:** If `(p, q)` is excluded by every `L'`, the shadow-CP chain leads to `(x', y')`, which by extremality means `(p, q) = (x', y')` — but `(x', y') ∉ boundary` (excluded).

**Tasks:**
- [ ] Prove `shadow_chain_terminates_at_extremal` (Qed).
- [ ] Prove `(x', y') ∉ boundary` (definitionally).
- [ ] Derive `False` from excluded-by-every-L' assumption.

### Phase T5: CoverageProof.v

**Goal:** Compose T1-T4 into the main lemma.

**Tasks:**
- [ ] Replace `trotter_coverage_via_extremality` Admitted with Qed proof using sub-lemmas.
- [ ] Update RemovablePairs.v to import the new module.
- [ ] Verify `mise build` green.

---

## Phase N (n5_residual) — 8 sub-files

### Phase N1: EdgeCount.v

**Goal:** Define edge counter for 5-element posets.

```coq
Definition edge_count_5 (R2 : B -> B -> Prop) (a b c d e : B) : nat :=
  (if excluded_middle_informative (R2 a b /\ a <> b) then 1 else 0) +
  (if excluded_middle_informative (R2 a c /\ a <> c) then 1 else 0) +
  ... (* 20 ordered pairs *)
```

**Tasks:**
- [ ] Define `edge_count_5`.
- [ ] Prove `edge_count_5_bounds`: `0 <= edge_count_5 <= 20`.
- [ ] Prove `edge_count_5_antisym`: with antisymmetry, count ≤ 10 (10 unordered pairs).
- [ ] Prove `non_antichain_iff_edge_count_pos`.

### Phase N2-N6: EdgeCount<k>.v for k ∈ {1, 2, 3, 4, 5}

Each file proves: if `edge_count_5 R2 a b c d e = k` and `≥2 strict edges`, then ∃ realizer (2 elements).

For each `k`, case-split on the structural pattern (V, ∧, disjoint, chain, etc.) and apply the matching per-class lemma from N5Realizers.v.

**Tasks per file:**
- [ ] State the lemma `n5_edge_count_<k>_two_realizer`.
- [ ] Enumerate structural patterns at edge count k.
- [ ] For each pattern, apply existing per-class lemma.

### Phase N7: EdgeCount6_9.v

Goal: handle edge counts 6, 7, 8, 9. These correspond to denser posets (close to chain).

**Tasks:**
- [ ] Combined enumeration for high edge counts.
- [ ] Use chain-like routing.
- [ ] Show 10 edges = chain (excluded by non-chain).

### Phase N8: Exhaustive.v

**Goal:** Compose N1-N7 into the main lemma.

**Tasks:**
- [ ] Restate `n5_residual_classes_two_realizer` here.
- [ ] Extract 5 elements, compute edge_count_5.
- [ ] Case-split: for each value in {2, 3, 4, 5, 6, 7, 8, 9}, apply corresponding sub-lemma.
- [ ] Exclude impossible values (0 = antichain, 1 = excluded by hypothesis, 10 = chain).
- [ ] Replace `N5DispatcherShapes.v` admit with import of this Qed lemma.

---

## Build-time discipline

**Per-file budget:** ≤5 min compile.

**Strategies to keep files fast:**
- Each Lemma's proof body ≤200 lines.
- Avoid `n5_split_witness` / `n5_close_forall_via` (slow Ltac combinators — caused 100x slowdown earlier).
- Use explicit `destruct (classic ...)` patterns.
- One Qed per "task" listed above.

**Verification protocol:**
- After each Qed addition: `opam exec -- dune build <file>.vo` with 5-min timeout.
- If exceeds 5 min, split the Qed further.

---

## Risk register

### Risk T-1: Trotter chain doesn't terminate in finite CP digraph
The `cp_le_strict` chain might be infinite without additional hypotheses.
**Mitigation:** finite cardinality + acyclicity of `cp_le` gives well-foundedness.

### Risk T-2: Greedy exclusion ≠ cycle creation
The exact characterization might differ from the stated equivalence.
**Mitigation:** prove the direction we need (excluded → cycle exists) rather than iff.

### Risk N-1: Edge-count classification misses iso classes
Some edge counts may have iso classes that don't match any per-class lemma.
**Mitigation:** Phase A1's Python enumeration already identified all 61 iso classes. Each edge-count bucket maps to a finite list of iso classes; verify completeness.

### Risk N-2: Per-class lemma application requires permutation
The per-class lemmas take canonical element orderings; routing may need element permutation.
**Mitigation:** Use `exists` with the right permutation, leverage the per-class lemma's existential witness.

---

## Execution order

**Track T (Trotter)** and **Track N (n5)** are INDEPENDENT and can be done in parallel via separate worktrees if desired.

**Recommended:** Track N first (more mechanical, faster wins). Then Track T.

**Phase ordering within each track:**
- Track T: T1 → T2 → T3 → T4 → T5
- Track N: N1 → (N2 through N7 in any order) → N8

---

## Estimated effort

- **Track N:** 8 files × ~30 min each = 4 hours.
- **Track T:** 5 files × ~45 min each = ~4 hours.
- **Total:** ~8 hours focused work.

If both tracks succeed: admit count drops 2 → 0.

If partial: each phase that closes is incremental progress (smaller admit).

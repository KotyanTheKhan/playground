# Closing the 2 Remaining Admits — Implementation Plan

> **For agentic workers:** Each phase is independently dispatchable. Build via `mise build`.

**Goal:** Close `n5_residual_classes_two_realizer` and `trotter_boundary_existence`, reducing admit count to 0.

**Architecture:** Two independent tracks. Track A enumerates missing n=5 isomorphism classes systematically. Track B formalizes Trotter Ch.6's combinatorial argument.

**Tech stack:** Coq 9.1.0, mise, dune.

---

## Track A: Close `n5_residual_classes_two_realizer`

**Current state:** 105+ n=5 per-class Qed lemmas; dispatcher routes most iso classes; ~5-15 missing classes need handling.

**Problem with brute-force enumeration:** Diminishing returns — duplicate detection cost exceeds new-class production rate.

### Phase A1: Systematic iso-class enumeration

**Goal:** Identify the precise missing iso classes.

**Files:** New `scripts/enum_posets_n5.py` (Python helper, not Coq).

- [ ] **Step 1: Generate all 63 unlabeled n=5 posets**

Use a Python script with `networkx` to:
1. Enumerate all 5-element DAGs up to isomorphism.
2. Transitively close each.
3. Filter to non-antichain, non-chain.
4. Output a canonical representative for each iso class.

Reference: OEIS A000112 = 63 unlabeled posets on 5 elements.

```python
# Sketch
import networkx as nx
from itertools import combinations

def all_posets_n(n):
    # Generate edges, filter via transitive closure + antisymmetry,
    # canonicalize via nx.isomorphism.
    pass

posets = all_posets_n(5)
non_trivial = [p for p in posets if not is_antichain(p) and not is_chain(p)]
print(f"Non-trivial n=5 iso classes: {len(non_trivial)}")  # Expected: 61
```

- [ ] **Step 2: Extract dispatcher predicates from N5Realizers.v**

Parse the dispatcher cascade in `n5_nonantichain_nonchain_two_realizer` to extract each predicate's edge set.

```python
# Pseudo-script: read N5Realizers.v, parse each `destruct (classic (exists a b c d e, R2 X Y /\ ...))`,
# extract the edge tuples.
covered_iso_classes = {parse_predicate_to_iso(predicate) for predicate in dispatcher_branches}
```

- [ ] **Step 3: Identify missing iso classes**

```python
missing = set(non_trivial_iso_classes) - covered_iso_classes
print(f"Missing classes: {len(missing)}")
for cls in missing:
    print(f"  - {canonical_name(cls)}: {cls.edges()}")
```

Expected output: a list of ~5-15 specific iso classes with their edge structures.

### Phase A2: Implement missing per-class lemmas

**Files:** `posets/dimension/N5Realizers.v`

For each missing iso class:

- [ ] **Step 4: Hand-compute rank tables L1, L2**

For each missing class with edge set E:
- Determine incomparable pairs.
- Try rank assignment (rk1, rk2) such that L1, L2 both extend E and intersection equals E.
- Use the framework template.

- [ ] **Step 5: Write per-class lemma via `n5_two_realizer_framework`**

Each lemma is ~30 lines + rank tables:

```coq
Lemma n5_<class_name>_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 5 ->
  (exists a b c d e : B,
     [distinctness] /\ [edge set] /\ [HR_only clause]) ->
  exists r, IsRealizer R2 r /\ cardinal _ r 2.
Proof.
  intros ... [a [b [c [d [e [...rest...]]]]]].
  apply (@n5_two_realizer_framework ... a b c d e ...).
  - exact rk1.
  - exact rk2.
  - (* rank monotonicity + intersection enumeration *)
  ...
Qed.
```

- [ ] **Step 6: Wire into dispatcher cascade**

Add a `destruct (classic (exists a b c d e, [predicate]))` branch.

- [ ] **Step 7: Run `mise build` after each lemma**

### Phase A3: Delete the admit

- [ ] **Step 8: Once all missing iso classes have per-class lemmas + cascade branches**, attempt deletion of `n5_residual_classes_two_realizer`.

- [ ] **Step 9: If deletion fails, investigate what's still routed there and patch.**

### Phase A estimated effort

- Phase A1: 4-8 hours (Python script + dispatcher parsing).
- Phase A2: ~30 minutes per missing class × ~10 classes = ~5 hours.
- Phase A3: 1-2 hours of integration.
- **Total: ~1-2 days.**

---

## Track B: Close `trotter_boundary_existence`

**Current state:** Trotter Theorem 6.1's per-L' boundary set existence is admitted. This is the genuine deep combinatorial step.

### Phase B1: Build critical-pair digraph infrastructure

**Files:** New `posets/dimension/CriticalPairDigraph.v` (or extend existing).

- [ ] **Step 1: Define the critical-pair digraph**

```coq
Definition CP_digraph (A : Type) (R : A -> A -> Prop) `{IsPoset A R} :
  A -> A -> Prop := fun x y => IsCriticalPair R x y.
```

- [ ] **Step 2: Prove finite CP digraph properties**

- For finite R, the CP digraph has finitely many edges.
- For non-antichain non-chain R with n ≥ 4, at least one CP exists.

- [ ] **Step 3: Define extremality**

Trotter's argument hinges on extremal vertices in the CP digraph. Define:

```coq
Definition IsExtremalCP (R : A -> A -> Prop) (x' y' : A) : Prop :=
  IsCriticalPair R x' y' /\
  (* x' is "extremal" w.r.t. some structural condition Trotter uses *)
  ...
```

The precise extremality condition needs careful translation from Trotter's text.

### Phase B2: Prove extremal CP existence

- [ ] **Step 4: Prove that every non-antichain non-chain finite poset has an extremal CP.**

Trotter's argument: use a max-min selection in the CP digraph. The extremal CP has properties that make the boundary set construction work.

### Phase B3: Build the boundary set construction

- [ ] **Step 5: For an extremal CP (x', y'), construct the per-L' boundary set.**

```coq
Lemma extremal_cp_boundary_set :
  forall (x' y' : A),
  IsExtremalCP R x' y' ->
  forall L', IsLinearExtension ... L' ->
  exists B : list (A * A),
    IsBoundaryReversalSet R x' y' B /\
    [acyclicity holds] /\
    [coverage holds].
Proof.
  (* Multi-page proof following Trotter Ch.6 *)
  ...
Qed.
```

This is the substantive work.

### Phase B4: Replace `trotter_boundary_existence` with composition

- [ ] **Step 6: Once `extremal_cp_boundary_set` is Qed**, replace `trotter_boundary_existence`'s admit with:

```coq
Lemma trotter_boundary_existence :
  ... (as currently stated) ...
Proof.
  intros ...
  destruct (extremal_cp_exists ...) as [x' [y' Hext]].
  (* Use Hext + extremal_cp_boundary_set *)
  ...
Qed.
```

### Phase B estimated effort

- Phase B1: 1-2 days (digraph infrastructure + finite properties).
- Phase B2: 2-3 days (extremal CP existence — combinatorial).
- Phase B3: 3-5 days (boundary set construction — the deep work).
- Phase B4: 1 day (composition).
- **Total: ~1-2 weeks.**

### Risk areas

- **Risk B1:** Trotter's extremality argument may not transfer cleanly to constructive Coq. May need to use classical logic + indefinite description.
- **Risk B2:** The "acyclicity holds" precondition for the boundary set is exactly the hard combinatorial claim. Trotter's text uses a maximal-chain argument that may require auxiliary lemmas about alternating cycles.
- **Risk B3:** The Coq proof may balloon to thousands of lines. Consider factoring into many small lemmas.

---

## Track ordering

**Recommended order:** Track A first (more tractable), then Track B.

**Reason:** Closing Track A removes a noisy admit and lets us focus on Trotter Ch.6 without distraction. Track A is mechanical; Track B is research-level.

**Alternative:** Run both tracks in parallel via separate worktrees.

---

## Verification

After each phase:
- `mise build` (full project) must be green.
- No new admits introduced.
- Top-level Hiraguchi theorems (`hiraguchi_thm`, `hiraguchi_bound`, `hiraguchi_helper`) must remain Qed transitively.

Final check: `grep -rn "Admitted\.$" posets/dimension/` returns empty.

---

## Stopping criteria

If Track B exceeds 2 weeks of focused effort:
- Document the precise sub-claim that's blocking.
- Factor into smaller named Admitted sub-lemmas.
- Stop and re-evaluate.

If Track A's Python helper turns out infeasible:
- Fall back to manual iso-class enumeration via OEIS A000112 references.
- Each missing class is mechanical Coq work.

---

## Out of scope

- Re-proving any of the existing 100+ per-class Qed lemmas.
- Refactoring beyond what's needed to support new lemmas.
- Extending to n ≥ 6 (Trotter handles this via induction; n=5 base case + induction step is sufficient).

---

## Build discipline

- All work on branch `dimension_finish` unless explicitly worktreed.
- Build via `mise build` (full project — single-file build is unreliable).
- Commit each lemma + wiring separately for bisectability.
- No Co-Authored-By lines in commits.

## Execution

The user can:
1. Execute Track A via subagent-driven development (dispatch implementer subagents per phase).
2. Execute Track B via plan-driven development with frequent checkpoint review.
3. Or execute both in parallel via separate worktrees.

After this plan is approved, invoke `superpowers:subagent-driven-development` to begin.

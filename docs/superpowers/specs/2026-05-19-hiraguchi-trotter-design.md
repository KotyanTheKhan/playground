# Design: Sound Proof of Hiraguchi's Theorem via Trotter's Removable-Pair Lemma

**Date:** 2026-05-19
**Files:** `posets/dimension/Theorems.v` (primary), possibly new file `posets/dimension/RemovablePairs.v`
**Targets:** `hiraguchi_thm`, `hiraguchi_bound`, `hiraguchi_helper`, `small_hiraguchi`, `small_two_realizer_incomp` — all currently honestly Admitted.

---

## Why the previous design failed

The previous design (`2026-05-14-hiraguchi-hard-admits-design.md`) relied on a lemma **"there exists a critical pair (x', y') such that every other critical pair has both endpoints in `S' = Full \ {x', y'}`"** (`extremal_critical_pair_exists` / `exists_critical_pair_no_boundary`).

**This lemma is false.** Counter-example: the n-element antichain (n ≥ 2). With `R = identity`, every ordered pair of distinct elements is a critical pair. Whichever (x', y') you pick, the pair (x', z) for any other z is also critical and has p = x', violating the conclusion.

Multiple agents independently produced "Qed" derivations from this false axiom; the soundness of the whole Hiraguchi chain was compromised. We are restarting with a structurally different approach.

---

## Mathematical strategy: Trotter's removable-pair lemma

Source: Trotter, *Combinatorics and Partially Ordered Sets*, Chapter 6.

### High-level structure

```
hiraguchi_helper (n ≥ 4)
├── if R has no incomparable pair → dim = 1 (chain case)
└── else
    ├── find a removable pair {x, y} via removable_pair_exists
    ├── apply IH to P − {x, y} (size n - 2 ≥ 2)
    └── apply removable_pair_dimension_bound:
          dim(P) ≤ dim(P − {x, y}) + 1
```

The two key new lemmas:

- **`removable_pair_exists`:** every finite poset `P` with `|P| ≥ 4` and at least one incomparable pair has a removable pair.
- **`removable_pair_dimension_bound`:** if `{x, y}` is removable, then `dim(P) ≤ dim(P − {x, y}) + 1`.

These replace the false `exists_critical_pair_no_boundary` / `extension_through_critical_pair` chain.

### Definition: "removable pair" (Trotter realizer-existence form)

**Update (2026-05-19, after Task 4 warm-up):** The original draft of this definition required a single linear extension `L` to reverse all "boundary" critical pairs in clause 3. That formulation is **unsatisfiable in any antichain** (both directed CPs `(p, q)` and `(q, p)` exist for any p ≠ q, but L can only reverse one direction). Revised to Trotter's actual formulation:

A pair `{x, y}` (with `x ≠ y`) in a finite poset `P` is **removable** iff:
- `x ≠ y`, and
- for every `d'`-element realizer of `P \ {x, y}`, there exists a `(d' + 1)`-element realizer of `P`.

This makes `removable_pair_dimension_bound` definitionally true (essentially an unfolding). The hard mathematical content moves entirely to `removable_pair_exists`, where it belongs.

**Why this is satisfiable for antichains:** the n-antichain has `dim = 2`. The (n-2)-antichain also has `dim = 2`. So `dim(antichain on n) ≤ 2 ≤ 2 + 1 = dim(antichain on n-2) + 1` holds, and any pair `{x, y}` of distinct elements is removable.

### Why Trotter's lemma is true (informal)

For any finite poset, build the critical-pair digraph `G_R`: vertices are elements of `P`, edges are critical pairs (directed). `G_R` may have cycles (e.g., in an antichain, every pair gives both directed edges). Trotter shows: **there always exist x ≠ y such that the critical pairs touching `{x, y}` can be linearized in a single extension**. The standard argument uses a maximal "chain of forced relations" in `G_R` and a careful choice at the boundary.

### Why Trotter's lemma is hard to formalize

- Requires reasoning about the critical-pair digraph as a Coq object.
- Requires the "fully reverses boundary CPs in a single L" step, which is exactly what the previous design tried (and got wrong) with `Hboundary_extension`.
- Requires correct handling of the antichain case as a non-degenerate edge case, not as an excluded case.

---

## Architecture

### File layout

```
posets/dimension/
  Theorems.v        — top-level theorem + induction skeleton (existing, modify)
  RemovablePairs.v  — NEW: definitions, removable_pair_exists,
                      removable_pair_dimension_bound, supporting lemmas
```

A new file `RemovablePairs.v` keeps the substantial new infrastructure
(definitions, ~10–15 lemmas, ~1500 lines) separate from `Theorems.v`.
`Theorems.v` will be slimmer after the cleanup: it imports `RemovablePairs`
and uses its main theorem.

### Definitions (in `RemovablePairs.v`)

```coq
(* The critical-pair digraph: directed edges are critical pairs of R. *)
Definition cp_digraph (A : Type) (R : A -> A -> Prop) `{IsPoset A R} :
  A -> A -> Prop := fun x y => IsCriticalPair R x y.

(* REVISED definition (Trotter realizer-existence form, post-Task 4 warm-up).
   Original "single-L joint-consistency" form was unsatisfiable in antichains. *)
Definition IsRemovablePair (A : Type) (R : A -> A -> Prop) `{IsPoset A R}
                           (x y : A) : Prop :=
  x <> y /\
  forall (d' : nat)
         (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                          {a : A | In A (Residual x y) a} -> Prop)),
    IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                   R (proj1_sig a) (proj1_sig b)) r' ->
    cardinal _ r' d' ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
```

### Key lemmas

1. **`removable_pair_exists`:** for every finite `R` on `n ≥ 4` elements with an incomparable pair, `exists x y, IsRemovablePair R x y`.

2. **`removable_pair_dimension_bound`:** if `IsRemovablePair R x y` and `PosetDimension (R restricted to P \ {x, y}) d'`, then `PosetDimension R d` for some `d ≤ d' + 1`.

3. **`hiraguchi_helper`:** standard induction on n, using the two above.

Total estimated new lemmas: ~15, including supporting infrastructure for the critical-pair digraph, lexicographic ordering on element pairs, and the linear-extension construction.

---

## Risk areas (read carefully)

This is a multi-day formalization. Specific risk points:

### Risk A: `removable_pair_exists` may need substantial new combinatorial infrastructure.

Trotter's existence argument uses the critical-pair digraph + an extremal-element selection within it. Formalizing "extremal vertex in a finite digraph" cleanly may require new utility lemmas (`extremal_element_exists`, `acyclic_subgraph_has_source`, etc.). Estimate: ~200–400 lines.

**Mitigation:** if the digraph machinery becomes unwieldy, fall back to a direct extremal argument using `Finite A (Full_set A)` and well-founded induction over critical pairs. May be uglier but more tractable.

### Risk B: `removable_pair_dimension_bound`'s construction.

The "fully reverses boundary CPs in one L" step (condition 3 in the definition) is where the previous design's `Hboundary_extension` lived. We have to produce a SINGLE linear extension `L` that:
- extends `L'` (the input subtype realizer)
- reverses every "boundary" critical pair

The previous design produced one `L_b` per boundary CP, breaking cardinality. Trotter's insight: when `{x, y}` is chosen carefully, **the boundary CPs are jointly consistent** — there's a single ordering that reverses them all without creating a cycle.

**Mitigation:** the existence of such a single L is exactly the condition we'll bake into `IsRemovablePair`'s definition. Then we prove `removable_pair_exists` by showing the chosen pair satisfies the consistency condition.

### Risk C: Soundness under the antichain edge case.

The n-element antichain (which broke the previous design) should pass cleanly: every (x, y) is removable (every pair is critical, but boundary CPs are pairwise consistent in any antichain's natural ordering).

**Verification step:** as part of testing, explicitly instantiate the proof on a 4-element antichain to verify `removable_pair_exists` and `removable_pair_dimension_bound` both produce sound witnesses. (Or at least sketch by hand that they do.)

### Risk D: Engineering complexity exceeds the time budget.

If the proof spans 5+ sessions and we hit walls similar to the previous design, the right action is to step back, write up the gap precisely, and stop adding unsound code. Do NOT repeat the cycle of "agent produces Qed via false axiom."

---

## Verification strategy

Each new lemma should be:

1. **Stated precisely** before its proof is attempted.
2. **Sanity-checked** on the n-antichain (the canonical pathological case) before being declared Qed.
3. **Used only after Qed** — no dispatching "use as opaque" agents on unstable lemmas.

For the top-level theorem, the verification is `mise build` + manual review that no admit cycle re-emerges.

---

## Out of scope

- Re-proving lemmas already honestly Qed in the file (e.g., `lift_and_force_is_poset`, `dushnik_miller_exists`, `subposet_dimension_le`).
- Re-introducing the false `extremal_critical_pair_exists` / `exists_critical_pair_no_boundary` lemmas. These will be REMOVED entirely in favor of `IsRemovablePair`.

---

## Estimated effort

- **Definitions and minor lemmas:** 1 day.
- **`removable_pair_dimension_bound`** (the construction):  1–2 days.
- **`removable_pair_exists`** (the existence argument): 2–3 days.
- **Top-level `hiraguchi_helper` induction:** 0.5 day.
- **Testing, cleanup, integration:** 1 day.

Total: 5–8 days of focused formalization work.

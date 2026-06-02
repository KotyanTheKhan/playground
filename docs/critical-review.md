# Critical review of the NomaDB execution-poset formalization

**Date:** 2026-06-02 · **Branch:** `execution_poset`

This is an adversarial review of the paper (NomaDB TechReport) and our Coq formalization,
hunting for unsoundness, incompleteness, controversies, and false statements — followed by the
work done to address each finding. Every claim below was checked against the source (theorem
statements, proof terminators, and `Print Assumptions`), not taken on faith from green builds.

## Soundness baseline (verified)

- **Exactly one real `Admitted` in the whole repository:** `small_complement_le_2`
  (`posets/dimension/AntichainComplement.v:90`), Trotter's Lemma 3 finite base case. Confirmed by
  `grep -rnE "^[[:space:]]*Admitted[[:space:]]*\.[[:space:]]*$"` over `posets/**` and `execution/**`.
- **No execution-layer result depends on it.** `Print Assumptions` on every headline result
  (`fully_sync_dim_le2`, `two_chain_cover_dim_le2`, `disjoint_chains_dim_le2`,
  `frontier_block_dim_le2`, `layered_chains_dim_le2`, `barrier_execution_dim_le2`,
  `fully_synchronizing_dim2`, `fully_sync_dimension`, `desugar_wf`) shows **zero** occurrences of
  `small_complement_le_2` — only standard classical axioms (`classic`,
  `constructive_definite_description`, `proof_irrelevance`, `Extensionality_Ensembles`, and, for
  some, `relational_choice`/`functional_extensionality_dep`/`propositional_extensionality`).
- **Hygiene precedent:** `Theorems.v:137` records that two lemmas
  (`extremal_critical_pair_exists`, `exists_critical_pair_no_boundary`) were found **FALSE** (the
  n-element antichain is a counter-example) and deleted. False statements have been hunted before.
- **No false `iff`** between `dim ≤ 2` and `no_alt_cycle` is claimed (see finding 4).

**Bottom line:** nothing in the formalization is unsound; the execution arc is admit-free. The
issues are about the **scope** being narrower than the headlines suggest, and the faithfulness of
the transformation slices. Everything is **classical** (not constructive).

---

## Findings and status

### Finding 1 — *(Critical) the matching model cannot express N-way barriers; dim≤2 only reached N≤4* — **ADDRESSED**

A frontier is a `list (Pid * Pid)` (sender→receiver pairs) = a partial matching, one op per
process per frontier. A path from index `k` to `k+1` uses only frontiers `k`,`k+1` (index is
non-decreasing along `hb`), and each matching gives ≤1 hop, so `(p,k)` reaches at most
`{p, σ_k(p), σ_{k+1}(p), σ_{k+1}(σ_k(p))}` — **≤4 processes** — at level `k+1`. Hence
`FullySynchronizing`/`IsFullySync` (which need *every* consecutive pair ordered) are **provably
unsatisfiable for N>4**, and `fully_synchronizing_dim2` is vacuous there. The pairwise `hb`
structurally cannot order all of layer `k` before layer `k+1` for N>4.

**Resolution** (`execution/BarrierExecDim.v`): model a *true* barrier. The fully-synchronized
order `blo` makes *every index a full barrier* (all of layer `i` precedes all of layer `j`, `i<j`)
with the real intra-layer matching as the within-layer order. `blo ⊇ hb` — it strengthens `hb`
with the barrier edges (synchronization *reduces* dimension). `layered_chains_dim_le2` (one
explicit 2-realizer; no finiteness/width) + `barrier_execution_dim_le2` give
`dim (blo s) ≤ 2` for **arbitrary N**; `bar5_dim_le2` is a concrete **N=5** witness. *Honest
scope:* `blo` models the barrier synchronization primitive (the paper's "synchronization"), not
arbitrary pairwise-message executions (which genuinely are not dim≤2). The pairwise `hb` model and
its N>4 limitation remain on record alongside `blo`.

### Finding 2 — *(Critical) the per-block dim≤2 hypothesis of `fully_sync_dim_le2` was never discharged* — **CLOSED**

`fully_sync_dim_le2` is conditional on "every frontier block has dim ≤ 2." Frontier blocks can
have **width > 2** (e.g. 3 disjoint message pairs ⟹ width 3), so `two_chain_cover_dim_le2`
(width ≤ 2) does NOT apply. The bound was only checked on concrete examples.

**Resolution** (`execution/DisjointChainsDim.v`): `disjoint_chains_dim_le2` — a disjoint union of
chains has dim ≤ 2 (explicit 2-realizer, no width/finiteness). `hb_same_index_msg` (via the rank
`2·idx+c`) shows a frontier block's comparability is exactly the message matching, so
`frontier_block_dim_le2` proves **every** frontier block of a well-formed schedule has dim ≤ 2
unconditionally; `fully_sync_frontier_dim_le2` makes the per-block obligation automatic.

### Finding 3 — *(Critical) Transformations A and B are content-light* — **PARTIALLY ADDRESSED**

- **Transformation A** is a dim-1 → dim-1 chain swap: it demonstrates dimension *preservation*,
  not the *reduction* one might expect. This is **faithful to the paper**, whose A also only
  *preserves* the critical-pair/dimension property (the reduction in NomaDB comes from the overall
  synchronization pattern, not from A). Recorded as an honest caveat in the TransformA spec; not a
  defect, but genuinely thin. **Not further strengthened** — it would require inventing reduction
  content the paper does not specify.
- **Transformation B**: `transform_B_preserves_dim2` is `fully_sync_dim_le2` restated (no new
  content). However its genuine lemma `two_chain_cover_dim_le2` (width ≤ 2 ⟹ dim ≤ 2) is now
  backed by **finding 5** (`B2` has exactly 2 critical pairs), so B faithfully renders the paper's
  "2 processes ⟹ ≤2 critical pairs ⟹ the block stays 2-dimensional." B's content is therefore
  no longer hollow, though the "transformation/swap" framing remains a thin wrapper over
  `fully_sync_dim_le2`.

### Finding 4 — *(Concerning) the `no_alt_cycle` dimension bridge is sound but inapplicable to execution posets* — **DOCUMENTED & SUPERSEDED**

`exec_dim_le_2_of_no_alt_cycle` is honest (`DimCriticalPairs.v` states the converse is FALSE), but
`no_alt_cycle` "FAILS for any poset containing an antichain" (the code comment) — and execution
posets always contain concurrency (antichains). So that early sub-arc (tasks B1–B3) is **dead
machinery for the actual goal**.

**Resolution:** the real dim≤2 levers used everywhere are `barrier_dim_le2` / `fully_sync_dim_le2`
and now `disjoint_chains_dim_le2` / `layered_chains_dim_le2`, which **do** work on posets with
antichains — they **supersede** the `no_alt_cycle` route. The bridge is retained as documented,
honestly-labelled weak machinery (it is the faithful critical-pairs ⟺ no-alternating-cycle
characterization, just not useful for 2-dimensional execution posets). Not removed (it is correct
and re-used by the critical-pair interface), but its limited applicability is on record.

### Finding 5 — *(Concerning) "≤2 critical pairs" was never formalized* — **CLOSED**

The paper's Transformation B is stated via *critical pairs*; we had substituted width ≤ 2 / 2
chains and asserted the link informally.

**Resolution** (`execution/TransformB.v`): `B2_critical_pair_iff` proves the 2-process block `B2`
has **exactly two** critical pairs — `(a0,b1)` and `(b0,a1)` — and `B2_at_most_two_critical_pairs`
states the ≤2 bound. With `B2_dim_le2` this is the faithful rendering of the paper's claim. (Uses
the project's `IsCriticalPair` from `Dimension.CriticalPairs`.) Note the earlier informal worry
that `B2` "has 4 incomparable pairs, not 2" is resolved: it has 4 *incomparable* pairs but exactly
2 *critical* pairs — which is the paper's actual quantity.

### Finding 6 — *(Concerning) `fully_sync_dimension` inherits the unsatisfiable precondition* — **ADDRESSED (satisfiability)**

`fully_sync_dimension` (exact `dim = max(1, maxᵢ dim Bᵢ)`) is sound but, like
`fully_synchronizing_dim2`, needs `IsFullySync` — unsatisfiable for N>4 in the pairwise model
(finding 1).

**Resolution:** finding 1's `blo` provides a genuinely fully-synchronized structure for **any N**,
so the fully-sync hypotheses are now *satisfiable* at arbitrary process count, not just N≤4. The
exact-dimension equality itself was already sound. The **exact** dimension of `blo` is now also
proven: `blo_dim_eq_2` (`execution/BarrierExecDim.v`) gives `dim (blo s) = 2` whenever `blo s` is
not a chain (has an incomparable pair) — combining `barrier_execution_dim_le2` (≤2) with
`dim_ge_2_of_incomparable` (≥2). `bar5_dim_eq_2` is the N=5 witness (dimension *exactly* 2).

---

## Residual / not addressed (deliberately)

- **Transformation A reduction content** (finding 3, A): the paper does not specify reduction
  geometry for A; we faithfully formalize preservation. No further work warranted.
- **Universal `no_alt_cycle` removal** (finding 4): kept as correct, documented, weak machinery.
- **Exact dimension of `blo`** (finding 6): now proven — `blo_dim_eq_2` gives `dim = 2` when
  `blo` is not a chain (the ≤2 bound plus the incomparable-pair lower bound).
- **The single dimension-library admit** `small_complement_le_2` (Trotter Lemma 3): a true but
  unproven finite base case; no execution result depends on it.
- **Classicality:** all results use classical axioms; no constructive versions.
- **Non-paper items:** the universal YAML round-trip theorem and OCaml file-I/O extraction remain
  unproven/unbuilt (tracked, out of scope of this review).

## Verdict

The formalization is **sound** (no false theorems; admit-free execution arc). After this review's
work, the central scope gaps are closed: **finding 1** (true N-way barriers ⟹ dim≤2 for any N) and
**finding 2** (per-block bound discharged) are addressed, **finding 5** (critical pairs) is
formalized, and **findings 3/4/6** are precisely documented with their resolutions/supersessions.
The honest residual is that Transformation A is preservation-only (as in the paper), the
`no_alt_cycle` bridge is correct-but-weak, and the dim≤2 story is faithful to the *barrier*
synchronization primitive rather than to arbitrary message passing.

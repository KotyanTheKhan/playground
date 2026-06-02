# True N-way barriers ⟹ dim ≤ 2 for arbitrary N — Design (addresses review finding 1)

**Date:** 2026-06-02
**Branch:** `execution_poset`
**Addresses:** critical-review **finding 1** — synchronization modeled as pairwise matchings makes `FullySynchronizing`/`IsFullySync` unsatisfiable for N>4 (a single transition reaches ≤4 processes), so the "synchronized execution ⟹ dim ≤ 2" story only covered N ≤ 4.
**Depends on:** `DimDefs` (`PosetDimension`, `IsRealizer`, `IsLinearExtension`, `dimension_is_minimum`), `DisjointChainsDim` (finding 2: `disjoint_chains_dim_le2`, `hb_same_index_msg`, `fb_comp`), `Rank` (`rank_hb_le`), `Schedule` (`desugar_rank_form`), `ScheduleWf`, `SyncShape` (`frontier_block`), `Ordinal`.

## The fix, conceptually

The pairwise-message `hb` cannot order all of layer `k` before all of layer `k+1` for N>4. A
**true barrier** does exactly that. We model the **fully-synchronized execution order** `blo`:
every index is a *full* barrier — *all* of layer `i` precedes *all* of layer `j` for `i<j` — with
the real intra-layer message matching as the within-layer order. This is the paper's synchronized
regime as a first-class poset (the pairwise `hb` could only approximate it for N≤4). We prove
`dim (blo s) ≤ 2` for **arbitrary N**, finally formalizing the paper's general dim-2 claim for
genuinely synchronized executions.

`blo ⊇ hb`: it strengthens `hb` with the barrier (cross-layer) edges. So `dim(blo) ≤ 2` even
where `dim(hb)` could be larger — synchronization *reduces* dimension, which is the paper's point.

## Component 1 — the math core (`execution/BarrierExecDim.v`)

A "layered disjoint-chains" poset: a `lay : A -> nat` (layer) and `comp : A -> nat` (within-layer
chain), with full barriers between layers and disjoint chains within. dim ≤ 2 by a single explicit
2-realizer (lexicographic `(lay, comp, R)`, component forward in `L1`, reversed in `L2`) — **no
finiteness, no width** (generalizes `disjoint_chains_dim_le2`, which is the one-layer case).

```coq
Lemma layered_chains_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (lay comp : A -> nat),
    (forall x y, lay x < lay y -> R x y) ->               (* full barrier between layers *)
    (forall x y, R x y -> lay x <= lay y) ->              (* R respects layers *)
    (forall x y, R x y -> lay x = lay y -> comp x = comp y) ->  (* within a layer R respects comp *)
    (forall x y, lay x = lay y -> comp x = comp y -> R x y \/ R y x) -> (* each within-layer comp is a chain *)
    forall d, PosetDimension R d -> d <= 2.
```
Realizer:
```
L1 x y := lay x < lay y \/ (lay x = lay y /\ (comp x < comp y \/ (comp x = comp y /\ R x y)))
L2 x y := lay x < lay y \/ (lay x = lay y /\ (comp y < comp x \/ (comp x = comp y /\ R x y)))
```
Both linear extensions (lex order); `R x y <-> L1 x y /\ L2 x y` (cross-layer ⟹ both true and `R`
by the barrier hyp; same-layer ⟹ the disjoint-chains argument; `lay x > lay y` ⟹ both false and
`¬R` by the respects-layers hyp). `dimension_is_minimum` ⟹ `d ≤ 2`.

## Component 2 — the barrier execution order from a schedule (`BarrierExecDim.v`)

```coq
Definition blo (s : Schedule)
  : ep_carrier (exec_of_schedule s) -> ep_carrier (exec_of_schedule s) -> Prop :=
  fun x y => snd (proj1_sig x) < snd (proj1_sig y)
          \/ (snd (proj1_sig x) = snd (proj1_sig y) /\ ep_order (exec_of_schedule s) x y).

Lemma hb_idx_le :   (* hb respects the index (from the rank 2*idx+c) *)
  forall s (x y : ep_carrier (exec_of_schedule s)),
    ep_order (exec_of_schedule s) x y -> snd (proj1_sig x) <= snd (proj1_sig y).

#[export] Instance blo_IsPoset : forall s, IsPoset _ (blo s).
  (* refl/antisym/trans: index-lex with ep_order tiebreak; antisym uses hb_idx_le + poset_antisym *)

Theorem barrier_execution_dim_le2 :
  forall s, wf_schedule s -> forall d, PosetDimension (blo s) d -> d <= 2.
```
Proof of the theorem: `apply (layered_chains_dim_le2 (blo s) (fun x => snd (proj1_sig x))
(fun x => fb_comp s (proj1_sig x)))` and discharge the four hypotheses:
- **barrier** (`lay x < lay y -> blo x y`): the first disjunct of `blo`. ✓ (this is the N-way
  barrier the pairwise model lacked).
- **respects-layers** (`blo x y -> lay x <= lay y`): `blo` def (`hb_idx_le` for the tiebreak case).
- **respects-comp within layer** (`blo x y -> lay x = lay y -> comp x = comp y`): `blo x y` with
  equal index ⟹ `ep_order x y` (same index) ⟹ `x = y` or `hb_same_index_msg` ⟹ `fb_comp` equal
  (finding 2's H1 reasoning).
- **within-layer chain** (`lay x = lay y -> comp x = comp y -> blo x y \/ blo y x`): finding 2's H2
  (same `fb_comp` ⟹ same matched pair/event ⟹ `ep_order`-comparable) ⟹ `blo`-comparable (tiebreak).

`hb_idx_le`: `rank_hb_le` gives `rank x ≤ rank y`; `desugar_rank_form` (`rank = 2·idx + c`, `c ≤ 1`)
⟹ `idx x ≤ idx y` (else `2·idx x ≥ 2·idx y + 2 > rank y ≥ rank x`).

## Component 3 — the punchline example (`execution/BarrierExecDimExamples.v`, test-only)

A concrete **N = 5** barrier execution (5 processes — beyond the ≤4 reach of the pairwise model)
with `dim ≤ 2`, demonstrating the fix covers exactly the regime finding 1 excluded. Either:
- instantiate `barrier_execution_dim_le2` on a 5-process schedule (e.g. `{ nprocs := 5;
  frontiers := [[]; []] }` — two barrier layers, each a 5-event antichain), or
- if the schedule plumbing is heavy, a bare 5-wide / 2-layer `layered_chains_dim_le2` instance.
Include a one-line note contrasting it with `FullySynchronizing` (unsatisfiable here for the
pairwise model). Optionally state `FullySynchronizing`-vs-`blo`: `blo` makes the barrier ordering
hold by construction, which `FullySynchronizing s` cannot for `s` with N>4.

## Files, wiring, testing
- New: `execution/BarrierExecDim.v` (exported), `execution/BarrierExecDimExamples.v` (test).
- `execution/dune` + `_CoqProject`: add both. `Execution.v`: export `BarrierExecDim`.
- `docs/INDEX.md`: subsection; note it addresses finding 1 (dim ≤ 2 for arbitrary-N synchronized
  executions, via the true-barrier order `blo`).
- Whole-project green; **zero `Admitted`**; files <500 lines; each `Qed` <5 min.
- `Print Assumptions layered_chains_dim_le2 barrier_execution_dim_le2` recorded.

## Acceptance criteria
1. `layered_chains_dim_le2` (generic, no finiteness). Zero admits.
2. `blo`, `hb_idx_le`, `blo_IsPoset`, `barrier_execution_dim_le2` (wf schedule ⟹ barrier execution
   dim ≤ 2, **arbitrary N**). Zero admits.
3. An N=5 example with dim ≤ 2. Whole-project green; INDEX updated; assumptions recorded.

## Honest scope / what this does and doesn't claim
- **Does:** formalize that *fully-synchronized* executions (every index a true N-way barrier) have
  dim ≤ 2 for any process count — closing the N>4 gap of finding 1 for the synchronized regime.
- **Does not:** claim arbitrary pairwise-message executions are dim ≤ 2 (they aren't), nor that
  `blo` is the `hb` of a message-passing program (it is `hb` strengthened by barrier edges —
  faithful to the *barrier* synchronization primitive, which is what the paper's "synchronization"
  means). The pairwise `hb` model and its `FullySynchronizing` limitation remain on record; `blo`
  is the honest model of true barriers alongside it.

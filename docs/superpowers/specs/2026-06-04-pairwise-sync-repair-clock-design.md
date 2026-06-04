# A 2-coordinate online logical clock for repairing-sync–connected executions

*Design spec. Status: approved for spec review. Coq proof is an explicit
future follow-on — out of this spec's scope.*

## North-star connection

This serves the project goal ([CLAUDE.md](../../../CLAUDE.md)): a logical clock
whose per-event memory is **below** the vector clock's Θ(N). Order dimension is
the lever — a poset of dimension `d` needs only `d` clock coordinates
(Charron-Bost). We already have, separately:

- the **fully-synced side** — an online, local 2-coordinate clock for a *single*
  barrier block (`execution_clock/RoundSem.v`, `rhb_iff_rclock`); and
- the **repair side** — the offline dimension dichotomy
  (`families/FrontierCompose.v`: `threshold_dim_le2` vs `crown3_dim_ge_3`) plus
  the empirical **fan law** (`nomadim/data/frontier-sync`: recovery length =
  `N − #cycles`, one repairing sync per transposition).

What does **not** exist yet, and what this spec designs: the **2-coordinate
clock + online protocol for the *composed* object** `[block A] ; [connector] ;
[block B]` in the literal **pairwise-sync model**, with the **repairing-sync
connector as a permanent, load-bearing middle layer** — validated empirically
against nomadim's z3 / brute-force dimension oracle, for N = 4 and generalized to
any N.

## Decisions locked in (from brainstorming)

| Question | Decision |
|----------|----------|
| Deliverable | Doc-first derivation, with an implementation (validation harness) gated behind it. |
| Model | **Literal pairwise-sync (nomadim)** — executions are lists of pairwise syncs `(i,j)`; the connector is a real sequence of syncs. |
| Correctness bar | **Construction + empirical validation** against nomadim's z3 / brute-force oracle. Coq proof deferred. |
| Construction approach | Within-block: **exact 2-realizer** extracted from the z3 model (the raw depth+tag engine was found sound-but-not-exact and dropped). Composition: seam `φ/ψ` interleave (`M1/M2`), driven by the connector. Any-N via the fan law. |
| Connector | **First-class**: composition is *always* `A ; CONNECTOR ; B`; the connector is its own block layer, never invisible glue. |

## Honest scope boundary

A *general* pairwise-sync execution is **not** dimension 2 (that is why vector
clocks exist). The 2-coordinate clock is faithful only on the **structured
family**: fully-synced blocks joined by a non-crossing (or fan-repaired) seam.
The protocol is therefore "valid on this family"; its repairing-sync connector is
exactly what keeps the family inside dimension 2. We do not claim a universal
2-coordinate clock.

---

## §1 — Model and event poset

- An execution is `E = (N, [s₁, …, s_m])` where each `sₜ = (i, j)` is an
  unordered pair of distinct processes (a meeting).
- **Poset elements** = the sync events. Generating relation: `sₜ → s_u` when
  `t < u` and `{iₜ,jₜ} ∩ {i_u,j_u} ≠ ∅` (knowledge passes through a shared
  participant). Happened-before `→hb` = the transitive (reflexive) closure.
- A **block** is a fully-frontier-synchronized sub-execution: every process's
  opening event lies in the causal past of every process's closing event.
- A **connector** is a short sync sequence inserted at a seam between blocks.

**Obligation:** the validation harness uses **nomadim's own poset builder** for
`→hb` and dimension. Our only modeling obligation is to *agree* with it; the
validation checks enforce agreement, so any discrepancy in this definition is
caught rather than assumed away. If nomadim's builder differs (e.g. it includes
explicit opening/closing frontier nodes), the harness adopts nomadim's poset as
ground truth and the clock is checked against that.

---

## §2 — The clock: the two coordinates of a 2-realizer

```
clock(e) = ( c₁(e) , c₂(e) )                       -- "two elements"
c₁(e) = rank of e in L₁                             -- a linear extension of →hb
c₂(e) = rank of e in L₂                             -- a second linear extension
e →hb f   ⟺   c₁(e) ≤ c₁(f)  ∧  c₂(e) ≤ c₂(f)       -- componentwise
```

`(L₁, L₂)` is a **2-realizer** of the composed poset: two total orders whose
intersection is exactly `→hb`. The clock is each event's rank in the two orders.
This exists iff the poset has dimension ≤ 2 — the whole point.

**Correction from planning (block-index is *not* a clean barrier).** An earlier
draft prepended a block-index `block(e) ∈ {A, CONNECTOR, B}` as an outer
lexicographic coordinate, treating each block boundary as a full barrier. That is
**unsound**: running block A then block B on the same processes leaves an idle
process's A-head event *concurrent* with B's first sync (it is not in that sync's
causal past), yet block-index ordering would assert `A-head →hb (B's first
sync)`. The true composition is `compose_le F` (`FrontierCompose.v`): cross-block
order is governed by the **frontier relation `F`**, and a threshold `F` realizes
as the `M1/M2` **frontier interleave** — A- and B-events interleaved by their
`φ/ψ` value, *not* "all A before all B". So `L₁, L₂` are genuine realizers of the
*whole* composed poset; the block structure shows up as the §4 seam interleave,
not a lexicographic prefix.

**Building blocks (compositional construction).** `L₁, L₂` are assembled from:
each block's own exact 2-realizer (§3, the within-block coordinates) + the seam
`φ/ψ` interleave that the connector installs (§4). The `M1/M2` formulas of
`threshold_dim_le2` are the seam-stitch recipe in Coq form.

"Two elements" = the two coordinates `c₁, c₂` (small integers / short tuples,
mirroring `OnlineClock`'s `nat³ × nat³`). Memory is **2 coordinates per event,
independent of N** — strictly below the vector clock's `N` for `N ≥ 3`.

---

## §3 — Constructing the coordinates (within a block) and the online question

**Within-block exact 2-realizer.** Each block, being dimension 2, has an exact
2-realizer `(L₁ᵇ, L₂ᵇ)` of its internal `→hb`. We extract it directly and
exactly from the **z3 model** already used as the oracle: `confirm_dim.build_smt`
at `t = 2` declares position variables `p0_v`, `p1_v` constrained to be two
linear extensions whose intersection is the poset; when SAT, those two position
vectors **are** `(L₁ᵇ, L₂ᵇ)`. The within-block coordinates are the ranks
`u₁(v) = p0_v`, `u₂(v) = p1_v`. (Blocks are small — ≤ `N + 3·S` vertices,
e.g. 19 for N=4/S=5 — so extraction is instant.) This is exact by construction
for any dim-2 block, sidestepping the `depth+tag` over-ordering trap below.

**Why not the raw `depth+tag` engine.** A candidate online engine assigned each
process `(depth, tag)` with `c = (depth, ±tag)`. Planning showed it is **sound
but not exact**: any two events with different `depth` are forced comparable by
the clock, so exactness needs incomparable events to share a depth — true only
for strict barrier/weak-order blocks, false for a general dim-2 block (e.g.
`DimExampleN3`'s `a ∥ e` cross-layer concurrency). It is therefore *not* the
within-block engine; the exact z3-extracted realizer is.

**The online question (deliberately deferred, named).** A 2-realizer extracted
post-hoc is an *offline* clock. A vector clock earns its `Θ(N)` by being
maintainable *on the fly*. Whether the composed 2-coordinate clock can be
maintained online with `O(1)` per-process state is exactly the open problem of
`DIM2_CLOCK.md §6`, now in the harder pairwise model. This spec's deliverable is
the **construction + empirical exactness** of the offline composed clock and the
composition/repair law; the online per-process protocol is future work. The
memory payoff we *do* establish: the clock is **2 coordinates per event,
independent of N** — below the vector clock's `N` for `N ≥ 3`.

---

## §4 — The repairing-sync connector (the load-bearing middle layer)

**Composition is always `A ; CONNECTOR ; B`** — connecting two fully-synced
executions *means* routing them through repairing syncs. The connector is block
layer 1; its syncs are ordinary events with ordinary stamps.

The seam wires A's output frontier (N channels) to B's input frontier
(N channels) — a **matching** `F`, i.e. a permutation of channels. The composed
cross-block order is `compose_le F` (cf. `FrontierCompose.v`).

- **Threshold (non-crossing) seam:** `F a b ⟺ φ(a) ≤ ψ(b)` for scalars `φ` on
  A-outputs, `ψ` on B-inputs. Then `threshold_dim_le2`'s `M1/M2` realize the
  composition, and `φ/ψ` is exactly a **consistent monotone tag alignment** that
  the within-block tag `g` extends across the seam. The connector here is the
  **trivial (empty) fan** — `N − #cycles = 0` syncs — but it still exists as the
  layer that carries the tag alignment.
- **Crossing seam (crown):** no monotone `φ/ψ` exists ⟹ dimension 3 ⟹ no
  2-coordinate clock. The connector is the **fan**: one repairing sync per
  transposition, `N − #cycles` total, rooted at one channel per cycle
  (`(1,2)(1,3)…(1,d)` for a d-cycle). Those syncs **re-route the crossed channels
  through a shared event**, installing the monotone `φ/ψ` that block B needs and
  restoring dimension 2 (so a 2-realizer, hence the clock, exists again).

Thus there is **one uniform mechanism**: the connector layer's syncs realign the
seam so block B's channels line up monotonically with block A's outputs. The
empty fan and the repair fan are the same construction at `length 0` and
`length N − #cycles`. The repairing sync is the device that "buys back the second
coordinate."

---

## §5 — N = 4 instantiation

Two block archetypes from `COMPOSE_N4.md`:

- **Star `B1`** `(0,1)(0,2)(0,3)(0,2)(0,1)` — gather to hub 0, scatter back.
- **Two-pairs `B9`** `(0,1)(2,3)(0,2)(0,1)(2,3)`.

Both are dim 2 (the gather/scatter hourglass = the X-cross of `DIM2_CLOCK.md
§4`); each has an exact 2-realizer extracted per §3.

Demonstrations (each a falsifiable check in §7):

1. **Single block exact** — the extracted 2-realizer realizes each block's `→hb`.
2. **Threshold composition exact** — identity-matching glue stays 2 coords.
3. **Crown is a negative control** — a crossing matching (e.g. swap 2↔3 on
   `B1;B1`) needs a 3rd coordinate; the 2-coord clock provably *fails* exactness.
4. **Fan-repaired exact again** — inserting the crossed-pair connector
   (`(2,3)` or `(1,2)` per the crossed-pair table) restores 2 coords. Marquee
   witness: `N4_connector1_rescue_dim2.yaml`
   = `(0,1)(0,2)(0,3)(0,2)(0,1) · (1,2) · (0,2)(0,1)(0,3)(0,1)(0,2)`.

The 5 crown classes and their rescuing connectors come straight from the
`COMPOSE_N4.md` crossed-pair table.

---

## §6 — Generalization to any N

The **fan law** is N-independent: a matching decomposes into cycles; the minimal
connector is `Σ_cycles (len − 1) = N − #cycles` repairing syncs, a fan rooted per
cycle. The protocol applies one tag-realignment per transposition; the connector
layer absorbs them regardless of N. Composing many blocks keeps the clock at 2
coordinates as long as **every seam is threshold or fan-repaired** — by induction
over the block sequence, with `block(e)` providing the outer barrier coordinate
at every seam.

Validation extends to N = 5, 6, 7, 8 using the stored `frontier-sync` witnesses
and the existing scan scripts (`scan_connector_multi.py`,
`compose_n5_connector.py`).

---

## §7 — Empirical validation plan (the correctness bar)

A Python harness living alongside the existing `nomadim/data/frontier-sync/*.py`
tooling. For each execution under test it:

1. Reads the execution (and its known block boundaries / matching).
2. Extracts the §3 2-realizer to assign every event a `clock = (c₁, c₂)`.
3. Builds `→hb` via nomadim's poset (ground truth).
4. **Checks exactness:** for all event pairs `(e, f)`,
   `clock(e) ≤ clock(f)  ⟺  e →hb f`.
5. **Cross-checks coordinate count** against the YAML's z3 / brute-force
   `dimension` field (2 where expected, 3 for the crown negative control).

Four assertions, mapped to §5:

| # | Family | Expected |
|---|--------|----------|
| a | the 10 N=4 single blocks | clock exact at 2 coords |
| b | threshold (non-crossing) compositions | clock exact at 2 coords |
| c | crown compositions (crossing, **no** connector) | clock **fails** exactness at 2 coords; oracle says dim 3 |
| d | fan-repaired compositions (`A ; fan ; B`) | clock exact at 2 coords again |

Corpus: the 10 blocks, the 2400 N=4 compositions
(`compose_n4.py` / `compose_n4_connector.py` outputs), the 52 witnesses in
`connector_examples/`, `N4_connector1_rescue_dim2.yaml`, and the N5–N8 witnesses.
Assertion (d) over the full corpus is the headline result: **the repairing-sync
connector restores the two-coordinate clock at every N tested.**

Negative control (c) is essential — it proves the clock is *exact*, not merely
sound: it must genuinely break where the dimension genuinely rises.

---

## Out of scope (named, not silently dropped)

- **Coq formalization** of the composed clock (a `ComposedClock`/connector
  extension of `RoundSem` with a `clock_iff_hb` theorem) — a future follow-on
  spec, after the construction is empirically validated.
- **Fully asynchronous** executions — not dim 2, need vector clocks; the
  2-coordinate clock deliberately lives only on the synchronized family.
- **Block boundary auto-detection** from a raw sync list with no provenance —
  here the boundaries are given by how the composed execution was built; inferring
  them from scratch is not needed for the validation.

---

## Deliverables

1. This design doc (the derivation/protocol contract).
2. A Python validation harness (`nomadim/data/frontier-sync/clock_validate.py`
   or sibling) implementing §3 and the §7 checks.
3. A short results note recording the four assertions' outcomes across the corpus
   (the empirical correctness evidence).

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
| Construction approach | **A (within-block depth+tag, comp-flip) as the engine; C (block-index + seam scalar φ/ψ) for composition and any-N generalization.** B (offline `M1/M2` ranks) used only as a validation oracle. |
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

## §2 — The clock: two lexicographic keys, O(1), N-independent

```
clock(e) = ( c₁(e) , c₂(e) )                       -- "two elements"
c₁(e) = ( block(e),  u₁(e) )                        -- lexicographic
c₂(e) = ( block(e),  u₂(e) )                        -- lexicographic
e →hb f   ⟺   c₁(e) ≤ c₁(f)  ∧  c₂(e) ≤ c₂(f)       -- componentwise
```

- `block(e) ∈ {0 (A), 1 (CONNECTOR), 2 (B), …}` — the block-layer index. Because
  each block is fully synced, the layer boundary is a **true barrier**: all of
  layer `k` precedes all of layer `k+1`. This is the coarse, sound-and-exact
  outer coordinate, and it is shared by both keys.
- `(u₁(e), u₂(e))` — the **within-block 2-realizer** produced by the
  depth+tag engine (§3): `u₁ = (depth, tag)`, `u₂ = (depth, Cmax − tag)`.
- The **comp-flip** — only `tag`'s direction reverses between `u₁` and `u₂` — is
  the established dimension-2 device (`BarrierExecDim`): two events with equal
  `depth` but different `tag` disagree across the two keys, hence come out
  **incomparable**, exactly as concurrent chains in a layer require.

"Two elements" = the two lexicographic keys `c₁, c₂` (each a short fixed-width
tuple, mirroring `OnlineClock`'s `nat³ × nat³`). Memory is **2 keys per event,
independent of N** — strictly below the vector clock's `N` for `N ≥ 3`.

---

## §3 — The online protocol

Per-process state: `(blk_p, d_p, g_p)` = (block counter, depth, tag).
Initialize `blk_p = 0`, `d_p = 0`, `g_p = p` (each process is its own initial
tag/channel).

At sync `sₜ = (i, j)`:

1. **Depth (2-way barrier advance):** `d := max(d_i, d_j) + 1; d_i := d_j := d`.
2. **Tag merge:** `g := merge(g_i, g_j)` (a canonical representative, e.g.
   `min`); `g_i := g_j := g`. Events that synced share a tag.
3. **Stamp:** `stamp(sₜ) := ( (blk, d, g), (blk, d, Cmax − g) )`.

At a **block boundary** (the current fully-synced block has completed): every
participant performs `blk += 1` and resets `d`, `g` for the new layer. The
boundary is detected from the execution's block structure (the harness knows
where A ends, the connector begins, and B begins — this is given by how the
composed execution was built).

**Message budget:** each sync exchanges only the two keys (a handful of integers)
— **O(1) per sync, independent of N** — versus a vector clock's `N` entries per
message. This is the concrete "cheaper than vector clocks" payoff.

The depth+tag engine runs *within* each block, where the block's internal
structure makes `(u₁, u₂)` a genuine 2-realizer of the block's internal `→hb`.
It is **not** used across block boundaries — those are handled by `block(e)` and
the connector (§4), avoiding the Lamport over-ordering trap (a raw global depth
would wrongly order genuinely-concurrent cross-layer events).

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
  (`(1,2)(1,3)…(1,d)` for a d-cycle). Running those syncs through the depth+tag
  engine **re-mixes the crossed tags through a shared event**, installing the
  monotone `φ/ψ` that block B needs and restoring dimension 2.

Thus there is **one uniform mechanism**: the connector layer's syncs realign
`tag`/`g` so block B's tags line up monotonically with block A's outputs. The
empty fan and the repair fan are the same construction at `length 0` and
`length N − #cycles`. The repairing sync is the device that "buys back the second
coordinate."

---

## §5 — N = 4 instantiation

Two block archetypes from `COMPOSE_N4.md`:

- **Star `B1`** `(0,1)(0,2)(0,3)(0,2)(0,1)` — gather to hub 0, scatter back.
- **Two-pairs `B9`** `(0,1)(2,3)(0,2)(0,1)(2,3)`.

Both are dim 2 with an explicit depth+tag within-block clock (the gather/scatter
hourglass = the X-cross of `DIM2_CLOCK.md §4`; `tag` = which leaf/group).

Demonstrations (each a falsifiable check in §7):

1. **Single block exact** — the within-block clock realizes each block's `→hb`.
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
2. Runs the §3 protocol to assign every event a `clock = (c₁, c₂)`.
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

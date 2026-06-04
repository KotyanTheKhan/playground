# Dimension-2 executions and the 2-coordinate logical clock

*How the dim-2 executions in `execution/` are built, the structural rule behind
them, and the logical-clock algorithm that rule induces.*

This note serves the project's [north-star goal](../CLAUDE.md): a logical clock
whose per-event memory is **below** the vector clock's Θ(N). The lever is order
dimension — the minimum number of scalar coordinates a clock needs to capture
the happened-before order **is** the order dimension of the execution poset
(Charron-Bost 1991: vector clocks need N entries precisely because that
dimension can reach N). Every dim-2 execution therefore admits a **2-integer**
clock regardless of the process count N.

---

## 1. The exact equivalence (what "dim 2" buys you)

For an execution poset `(E, →hb)`:

> `dim(E, →hb) ≤ 2` **iff** there exist two total orders `L₁, L₂` on `E` with
> `e →hb f  ⟺  e ≤_{L₁} f  ∧  e ≤_{L₂} f`.

The pair of ranks **is** the clock:

```
clock(e) := ( rank_{L₁}(e) , rank_{L₂}(e) )          -- two integers
e →hb f   ⟺   clock(e) ≤ clock(f)  componentwise     -- causality test
```

This is proven, end to end, on a concrete execution in
[`DimExampleN3.v`](dimension/examples/DimExampleN3.v): `key1_n3` and `key2_n3` (lines 25–34) are the
two coordinates, `hb_n3_realizer` (line 275) proves `→hb = L₁ ∩ L₂`, and
`E_n3_dim_2` (line 332) concludes dimension exactly 2. That execution has 3
processes yet needs only **2** clock coordinates, not 3.

The bridge `dim = 2 ⟺ a 2-realizer exists` is `exec_dim_eq_2_of_realizer`
(`DimBridge.v`); the `≥ 2` half is `dim_ge_2_of_incomparable` (any single
incomparable pair forces dim ≥ 2).

So the research question "which executions beat vector clocks" is exactly:
**which executions have a 2-dimensional happened-before order.** The files in
`execution/` answer this with one structural rule plus a composition law.

---

## 2. The structural rule: barrier-layered chains

The master sufficient condition is `layered_chains_dim_le2`
([`BarrierExecDim.v:14`](barriers/BarrierExecDim.v)). An execution has `dim ≤ 2` whenever
each event carries a **layer** `lay(e) ∈ ℕ` and a **component** `comp(e) ∈ ℕ`
satisfying:

| # | Condition | Meaning |
|---|-----------|---------|
| 1 | `lay x < lay y → x →hb y` | **full barrier**: every event of a lower layer precedes every event of a higher layer |
| 2 | `x →hb y → lay x ≤ lay y` | order never moves down a layer |
| 3 | `x →hb y ∧ lay x = lay y → comp x = comp y` | inside a layer, order only links same-component events |
| 4 | `lay x = lay y ∧ comp x = comp y → x →hb y ∨ y →hb x` | each component **inside** a layer is a chain |

In words: **the execution is a vertical stack of layers; each layer is a
disjoint union of chains; consecutive layers are joined by a complete barrier.**

The proof builds the two coordinates explicitly (`BarrierExecDim.v:23–26`):

```
L₁ : sort by ( lay ↑ , comp ↑ , then →hb )
L₂ : sort by ( lay ↑ , comp ↓ , then →hb )      -- only comp's direction flips
```

`→hb = L₁ ∩ L₂` (`Hcap`, line 87), the realizer has ≤ 2 elements (`Hcard`,
line 107), so `dim ≤ 2`. Flipping **only the component order** between the two
coordinates is the whole trick: two events in the same layer but different
components disagree on which precedes the other across `L₁` vs `L₂`, so they come
out incomparable — exactly as a barrier execution requires.

### The induced clock

```
T₁(e) = ( barrier(e),  comp(e),           step(e) )    -- lexicographic
T₂(e) = ( barrier(e),  Cmax − comp(e),    step(e) )    -- lexicographic
clock(e) = (T₁(e), T₂(e))
e →hb f  ⟺  T₁(e) ≤ T₁(f)  ∧  T₂(e) ≤ T₂(f)
```

- `barrier(e)` = how many barriers precede `e` (a Lamport-style scalar),
- `comp(e)` = which chain/message-group `e` belongs to within its layer,
- `step(e)` = position of `e` along its chain,
- `Cmax` = a per-layer component bound.

Two lexicographic keys — **O(1) keys per event, independent of N** — versus the
vector clock's N entries. For the message-passing model the component is read off
the program directly: `fb_comp` ([`DisjointChainsDim.v:180`](families/DisjointChainsDim.v))
sets `comp` of a receive to its **sender** and of a send/local to its **own
pid**. Lemmas `fb_comp_eq_of_hb` and `hb_or_of_fb_comp_eq` discharge conditions 3
and 4; `barrier_execution_dim_le2` (`BarrierExecDim.v:167`) plugs them into the
master rule for the barrier order `blo`.

---

## 3. The composition law: barriers take the MAX, not the sum

Why the rule is stable under nesting — the key to building large dim-2
executions — is `fully_sync_dimension`
([`FullySyncDimExact.v:18`](sync/FullySyncDimExact.v)):

> For a barrier (ordinal) decomposition into blocks `B₀, …, B_{m-1}`,
> `dim(whole) = max(1, maxᵢ dim(Bᵢ))`.

Stacking blocks through a full barrier composes their dimensions by **maximum**.
A disjoint union of chains has `dim ≤ 2` (`disjoint_chains_dim_le2`,
[`DisjointChainsDim.v:14`](families/DisjointChainsDim.v)), so any stack of such layers
stays at 2 no matter how many layers or processes:

- `blo_dim_eq_2` (`BarrierExecDim.v:187`): a non-trivial barrier execution has
  dimension **exactly 2 for arbitrary N**.
- `bar5_dim_eq_2` (`BarrierExecDimExamples.v:61`): the explicit N=5 witness — a
  genuine 5-way barrier, beyond the pairwise model's reach, still dim 2.
- `fully_sync_frontier_dim_le2` (`DisjointChainsDim.v:582`): any
  fully-synchronized schedule's execution has `dim ≤ 2`.

This MAX law is what makes the structure *fractal-safe* (next section).

---

## 4. Construction rule = a grammar (the "X-cross fractal")

The conditions of §2 + the MAX law of §3 are exactly a small generative grammar.
Every term it produces is a dim-2 execution:

```
Exec   ::=  Layer
         |  Layer  ; barrier ;  Exec          -- stack via a FULL barrier  (MAX-composes dim, §3)
Layer  ::=  Chain
         |  Chain  ∥  Layer                    -- disjoint, mutually incomparable chains (§2 cond. 3–4)
Chain  ::=  event
         |  event  →  Chain                    -- sequential within one component
```

**Geometric reading (the user's X-crosses).** A *full barrier* between two
layers is a synchronization rendezvous: every chain coming up from layer `k` is
ordered below every chain starting in layer `k+1`. Drawn with layers as
horizontal cuts, the chains *fan in* to the barrier and *fan back out* above
it — an **X / hourglass** at each rendezvous. Stacking barriers (the `;` rule)
piles X's vertically.

**The fractal.** Refine the grammar by letting a single `event` inside a `Chain`
expand into a whole nested `Exec`:

```
Chain  ::=  … |  Exec  →  Chain                 -- a chain step is itself a barrier block
```

Because barriers compose by **max** (§3), a nested barrier block of dimension 2
sitting inside a chain keeps the enclosing execution at dimension 2 — at **every**
level of recursion. Expanding each X's strands into smaller X's, ad infinitum,
yields the self-similar X-cross figure, and the MAX law certifies the whole
infinite-depth object never exceeds dimension 2. That is the precise sense in
which "fractal of X-shaped crosses ⟹ dim 2."

**Planarity.** Each layer is a set of parallel chains (planar); a full barrier
realized as one rendezvous event is a single vertex where strands meet (the waist
of the X, planar); series-composition of planar pieces at cut vertices stays
planar. So barrier-grammar executions have planar Hasse diagrams — matching the
observation. (General dim-2 posets need not be planar; the *barrier-structured*
ones are. Planarity is a consequence of this construction, not of dim 2 alone.)

---

## 5. Sufficient vs. necessary — honest scope

- The barrier grammar (§4) is **sufficient**, not necessary. `DimExampleN3.v` is
  dim 2 yet has genuine cross-layer concurrency (`a ∥ e`), so it is *not* a pure
  barrier execution. The **necessary-and-sufficient** condition is just §1: `→hb`
  is 2-dimensional (equivalently, a permutation poset / its incomparability graph
  is transitively orientable).
- The pairwise-message frontier model cannot express an N-way barrier for `N > 4`
  (`FullySynchronizing` is unsatisfiable there); the `blo` order models the
  barrier primitive directly and is what delivers the arbitrary-N dim-2 result.
  See [`../docs/critical-review.md`](../docs/critical-review.md), finding 1.
- Everything cited is **admit-free** (classical axioms only); verified by
  `Print Assumptions` per `RESULTS.md`.

---

## 6. The clock, as an algorithm — and the open online question

**Offline (proven, and now *computable*).** Given a barrier execution, assign each
event the pair `(T₁, T₂)` of §2. Causality is the componentwise ≤ test. Memory:
**2 integers per event, for any N** — strictly below the vector clock's N for
`N ≥ 3`. This is no longer just the abstract realizer: `OnlineClock.v` gives a
concrete `stamp : event → (nat³ × nat³)` and proves `blo s x y ↔ stamp x ≤_prod
stamp y` (`blo_iff_stamp`, **any N**, admit-free), with the comparison on emitted
integers only — never peeking at `hb`. The generic core `stamp_iff` states the
rule abstractly (5 hypotheses: barrier/resp-lay/resp-comp/rank/bound).

**Online (the next research step).** A vector clock earns its Θ(N) by being
*maintainable on the fly*: each process updates its own entry and merges
received entries. For the 2-coordinate clock to be a genuine competitor it must
be assignable causally, without a global post-hoc sort. The grammar of §4 makes
this plausible: `barrier(e)` is a scalar each process can increment at each
rendezvous (Lamport-style), and `comp(e)` is determined locally by the message
group. The open question — the concrete next deliverable toward the north star —
is:

> Maintain `(T₁, T₂)` **online** with O(1) (or O(log) bits) of state per process
> per barrier, proven to satisfy `e →hb f ⟺ clock(e) ≤ clock(f)`, for the
> barrier-grammar executions.

If solved, synchronized workloads get a constant-coordinate causal clock where
the classical bound says vector clocks need N. Two pieces are now machine-checked:
the **characterization** (`blo_iff_stamp`, a computable stamp) and the **stamp
formula's locality** (`OnlineClockLocal.v`) — `local_stamp (N p i : nat) (o : Op)`
takes only `(N, pid, index, op)`, so by its very type it *cannot* consult the
global schedule; `local_stamp_correct` proves it reproduces the global stamp, and
`blo_iff_local_stamp` restates causality through it. Two `reflexivity` interface
lemmas confirm the only cross-process datum the formula reads is a `Recv`'s sender
id — **no clock-value piggybacking** (vs the vector clock's N entries per message),
per-process state `(pid, a local counter)`.

This gap is now **closed operationally** by `RoundSem.v`: an operational
barrier-round model where each process has its **own primitive program**
`rs_prog p : list Op` and its op is `rop S p r = nth r (rs_prog S p)` — a function
of `p`'s own program and counter `r`, with **no `Schedule`/`op_at` projection**.
The clock `rclock S p r = local_stamp (nprocs) p r (rop S p r)` is thus genuinely
local, and `rhb_iff_rclock` proves causality (`rhb`) is exactly its product order,
by instantiating the generic `stamp_iff` (`Print Assumptions` = only
`proof_irrelevance`). So for the barrier-synchronized regime, the "local_obs takes
the schedule" caveat is resolved: `local_obs` is replaced by the process's own
program lookup.

What remains genuinely open is a *fully asynchronous* small-step model with
message channels and arbitrary interleaving — deliberately **not** pursued, since
async executions are not dim-2 (they need vector clocks) and the dim-2 clock lives
on exactly the barrier-synchronized runs the round model captures.

---

### Lemma map (claim → proof)

| Claim | Lemma / file |
|------|--------------|
| dim 2 ⟺ 2 total orders realize →hb | `exec_dim_eq_2_of_realizer` (`DimBridge.v`) |
| concrete 3-proc execution is dim 2 via explicit (key1,key2) | `E_n3_dim_2` (`DimExampleN3.v:332`) |
| barrier-layered-chains ⟹ dim ≤ 2 (the rule) | `layered_chains_dim_le2` (`BarrierExecDim.v:14`) |
| message component = sender of a receive | `fb_comp` + `fb_comp_eq_of_hb` (`DisjointChainsDim.v:180,264`) |
| disjoint union of chains ⟹ dim ≤ 2 (one layer) | `disjoint_chains_dim_le2` (`DisjointChainsDim.v:14`) |
| barriers compose dimension by MAX (the fractal law) | `fully_sync_dimension` (`FullySyncDimExact.v:18`) |
| barrier execution has dim exactly 2 for any N | `blo_dim_eq_2` (`BarrierExecDim.v:187`) |
| explicit N=5 barrier is dim 2 | `bar5_dim_eq_2` (`BarrierExecDimExamples.v:61`) |
| any fully-sync schedule's execution is dim ≤ 2 | `fully_sync_frontier_dim_le2` (`DisjointChainsDim.v:582`) |
| **barrier order = a computable product-of-lex clock (any N)** | **`blo_iff_stamp`** (`OnlineClock.v`); generic rule `stamp_iff` |
| **clock computable from purely local data (no global view)** | **`local_stamp_correct`** / **`blo_iff_local_stamp`** (`OnlineClockLocal.v`) |
| **operational primitive-state model: causality via a schedule-free clock** | **`rhb_iff_rclock`** (`RoundSem.v`); `rop = nth r (rs_prog p)` |
| **connecting two executions by a threshold frontier preserves dim 2** | **`threshold_dim_le2`** (`FrontierCompose.v`) |
| **a crossing (S₃) frontier raises dimension to ≥ 3** | **`crown3_dim_ge_3`** (`FrontierCompose.v`) |

**Composition (when is dim-2 preserved).** Connecting two dim-2 executions by a
frontier does *not* always keep dimension low: `FrontierCompose.v` proves the
dichotomy on antichains — a **threshold** frontier (`F a b ⟺ φ a ≤ ψ b`, the
directly-buildable form of non-crossing) preserves `dim ≤ 2` (`threshold_dim_le2`),
while the **S₃ crown** frontier (`i≠j`) forces `dim ≥ 3` (`crown3_dim_ge_3_closed`:
crown3 *has* a dimension, via Dushnik–Miller, and it is ≥ 3 — unconditional). The
full *Ferrers* (general non-crossing) positive result needs Ferrers⟹threshold and
is deferred. So a dim-2 structure is fragile
under frontier gluing; threshold (non-crossing) connections preserve it.
*(Admit-free; `Print Assumptions`: `threshold_dim_le2` uses `classic` +
`Extensionality_Ensembles`; `crown3_dim_ge_3` additionally uses the Szpilrajn-chain
choice/extensionality axioms via the dimension library.)*

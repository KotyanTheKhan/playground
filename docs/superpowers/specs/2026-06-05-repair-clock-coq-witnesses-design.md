# Concrete Coq witnesses of the 2-coordinate repair-clock

*Design spec. The admit-free follow-on to the empirically-validated repair-clock
([2026-06-04 spec](2026-06-04-pairwise-sync-repair-clock-design.md),
`nomadim/data/frontier-sync/CLOCK_RESULTS.md`).*

## North-star connection

Machine-check, in Coq, the heart of the repair-clock result: on a real
fully-synced pairwise execution the **2-coordinate clock characterizes
happened-before** (so `dim ≤ 2`, sub-vector-clock memory), and the **repairing
sync is what yields such an execution** — the `dim 3` crown loses the 2-coordinate
clock, and adding one sync restores it. This serves the project goal
([CLAUDE.md](../../../CLAUDE.md)): logical clocks below the vector clock's Θ(N).

## What already exists in Coq (do not re-prove)

- `FrontierCompose.threshold_dim_le2` (threshold seam ⟹ `dim ≤ 2`, explicit
  `M1/M2`), `FrontierCompose.crown3_dim_ge_3` (the abstract crown ⟹ `dim ≥ 3`).
- `DimBridge.exec_dim_eq_2_of_realizer` (a 2-element realizer ⟹ `dim = 2`) and
  the `DimExampleN3.v` pattern (concrete execution proven `dim 2` via explicit
  key functions `key1/key2` and `hb = L1 ∩ L2`).
- Generic `posets/dimension` machinery: `PosetDimension`, `IsRealizer`,
  `subposet_dimension_le`, the `CriticalPairs` framework.

So the **abstract dichotomy and the realizer→dimension bridge are done**. The new
contribution is **concrete, machine-checked witnesses in the actual pairwise
execution posets**.

## Decisions locked in (from brainstorming)

| Question | Decision |
|----------|----------|
| What to add | **Concrete `block ; connector ; block` witnesses** (the abstract theorems already exist). |
| Sizing | **Minimized witnesses**, `decide`/`vm_compute` proofs (no exponential reflection). |
| Crown (`dim ≥ 3`) side | **Out of Coq scope**: prove the admit-free **dim-2 positive side**; reuse the abstract `crown3_dim_ge_3` as the named obstruction and cite z3 for the concrete crown's `dim 3`. |
| Poset model | **Literal nomadim PG poset** as a raw finite poset (`Fin.t n` + boolean order = reflexive-transitive closure of the PG edges), so the z3 realizers transfer verbatim. |

## Honest scope boundary

This formalizes the **positive (dim ≤ 2) side**: a real fully-synced execution
(a minimal block, and a crown's one-sync repair) has an exact 2-coordinate clock.
It does **not** prove the concrete 16-event crown has `dim ≥ 3` in Coq (no induced
`crown3`; that needs an alternating-cycle critical-pair certificate — deferred).
The crown's `dim 3` is established empirically by z3 (`CLOCK_RESULTS.md`) and the
*phenomenon* by the abstract `crown3_dim_ge_3`. Everything Coq-proven here is
admit-free; `Print Assumptions` is reported per result.

---

## §1 — Poset model & the reusable bridge

Each witness is a **concrete finite poset**: carrier `Fin.t n`, order given by a
boolean table `leb : Fin.t n -> Fin.t n -> bool` defined as the
reflexive-transitive closure of the execution's PG edge list (the same
`PG.sync = join + 2 heads` model nomadim uses; the edges are extracted from the
harness). `IsPoset` (reflexivity, antisymmetry, transitivity) is discharged by
`vm_compute`/`decide` over the finite carrier — a **bounded, linear table
evaluation** (e.g. `n³ ≈ 6859` triples for `n = 19`), *not* the exponential
pattern-enumeration that caused earlier reflection blowups. This distinction is
explicit and load-bearing for tractability.

**The bridge lemma (reusable, the one piece of new generic infrastructure):**

> `realizer_bool_dim_le2`: given a finite poset `(Fin.t n, le)` with boolean
> `leb` reflecting `le`, and two boolean total orders `L1b, L2b` each reflecting
> a relation that **extends** `le`, such that `leb x y = L1b x y && L2b x y` for
> all `x y` (checked by `vm_compute`), the two-element set `{L1, L2}` is an
> `IsRealizer`, hence `PosetDimension ≤ 2`.

This is the generic, computational analog of `exec_dim_eq_2_of_realizer`. It is
proven once and reused by every dim-2 witness. The boolean inputs `L1b, L2b` are
the **z3-extracted realizer ranks** (`clock_realizer.extract_realizer`),
re-exported as Coq tables by a small generator.

---

## §2 — The witnesses

All three executions are real fully-synced pairwise executions; `W_crown` and
`W_repair` differ by exactly one sync.

- **W_block** — the minimal fully-synced dim-2 execution: `N=2`, syncs `[(0,1)]`,
  PG poset of **5 events**. Prove `PosetDimension W_block ≤ 2` via
  `realizer_bool_dim_le2` with its explicit 2-realizer, and `2 ≤
  PosetDimension W_block` from one incomparable pair (the two post-sync heads).
  Hence `dim = 2`. **Claim machine-checked:** a minimal real execution has an
  exact 2-coordinate clock characterizing `→hb`. (Small enough to also serve as
  the bridge's first test.)

- **W_repair** — `N=4`, syncs `[(0,1),(2,3),(0,3),(0,2),(1,3)]`, PG poset of
  **19 events**, fully synchronized, `dim 2`. Prove `PosetDimension W_repair ≤ 2`
  via `realizer_bool_dim_le2` with the z3 realizer. **Claim machine-checked:**
  the execution obtained by inserting the repairing sync `(0,3)` has an exact
  2-coordinate clock.

- **W_crown** — `N=4`, syncs `[(0,1),(2,3),(0,2),(1,3)]` (= `W_repair` minus the
  `(0,3)` sync), PG poset of **16 events**, fully synchronized, `dim 3`
  (z3-established, the minimal crown). **Not proven dim≥3 in Coq.** Its role: a
  `Definition` + a comment recording that removing the single repairing sync
  yields the crown whose dimension is 3 (z3, `CLOCK_RESULTS.md`), and that the
  *obstruction type* is the abstract `crown3` (`crown3_dim_ge_3`). This closes
  the narrative "remove the repairing sync ⟹ lose the 2-coordinate clock"
  without an admit, by deferring rather than asserting the concrete `dim ≥ 3`.

The `W_crown`/`W_repair` one-sync difference is stated as a Coq `Definition`
(`W_repair = insert_sync 2 (0,3) W_crown` or the explicit list equality), making
the "one repairing sync" precise.

---

## §3 — Files & structure

| File | Responsibility | Size target |
|------|----------------|-------------|
| `execution_clock/witnesses/FinPosetBool.v` | concrete finite poset from a boolean table; `IsPoset` by `vm_compute`; the `realizer_bool_dim_le2` bridge | < 400 lines |
| `execution_clock/witnesses/WitnessData.v` | the three PG edge tables + the two realizer tables for W_block and W_repair (generated from the harness; machine data, mostly `Definition`s) | < 500 lines |
| `execution_clock/witnesses/BlockDim2.v` | `W_block` poset + `block_dim_eq_2` | < 300 lines |
| `execution_clock/witnesses/RepairDim2.v` | `W_repair` poset + `repair_dim_le_2`; `W_crown` definition + narrative comment citing `crown3_dim_ge_3` and z3 | < 400 lines |

A generator script `nomadim/data/frontier-sync/emit_coq_witness.py` emits the
`WitnessData.v` tables (edge lists + realizer ranks → Coq boolean functions)
from `pg_of` + `extract_realizer`, so the Coq data is reproducible, not
hand-transcribed.

---

## §4 — Build, tractability, verification

- Every build via `bash .claude/scripts/timed-build.sh <secs> <target> 1` (the
  `vm_compute` files are memory-heavier; use `-j1`). Each `.v` < 500 lines, each
  `Qed` < 5 min (the table evals are milliseconds; the risk is proof-term size,
  mitigated by `vm_compute`/`Qed`-by-reflection rather than `simpl`).
- **Admit-free:** `Print Assumptions block_dim_eq_2` / `repair_dim_le_2` reported;
  expected to bottom out only at classical axioms used by the dimension library
  (as the existing dimension results do).
- The generator's output is cross-checked: the emitted Coq `leb` table must equal
  the harness reachability, and the emitted realizer must satisfy
  `clock_is_exact` — asserted in the generator before writing the file.

---

## §5 — What this buys (and what it doesn't)

**Buys:** a machine-checked statement, in the real pairwise-execution posets,
that the 2-coordinate clock characterizes `→hb` on a minimal fully-synced
execution and on a crown's one-sync repair — the admit-free Coq core of "the
repairing sync restores the second coordinate."

**Doesn't (named, deferred):** the concrete crown's `dim ≥ 3` in Coq (needs an
alternating-cycle critical-pair certificate); the online per-process maintenance
of the clock; any general (all-N) Coq theorem (these witnesses are specific
instances, as `DimExampleN3` is).

---

## Out of scope

- Re-proving the abstract dichotomy (`threshold_dim_le2`, `crown3_dim_ge_3` —
  already done).
- The schedule/`ExecPoset` model (we use the raw PG poset directly for
  faithfulness to the harness and to reuse the z3 realizers).
- Online clock and async models.

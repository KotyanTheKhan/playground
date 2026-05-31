# Execution Poset Framework — Design

**Date:** 2026-05-31
**Branch:** `execution_poset`
**Paper:** NomaDB TechReport — https://github.com/DePizzottri/NomaDB/blob/master/paper/TechReport_RU.md

## Goal (whole branch)

Build a framework for working with **execution posets of Lamport
happened-before posets**: posets of special shape consisting of `N` chains
(events within the same process) plus message-passing edges between processes.
The framework must let us:

- describe such posets *via rules* (a high-level generative description) **and**
  *via just an edge set*;
- **read and write** these posets to/from files;
- **draw** them in a UI;
- **reduce** them step by step toward the case where every message has *sync
  shape* (send immediately followed by its receive), with the reductions proved
  to **preserve poset dimension**.

Dimension *analysis* of specific sync-shape posets is **out of scope for this
branch** (a later branch), but the reduction machinery proved here is what makes
that analysis possible.

## Framing decisions (agreed)

- **Architecture:** Coq core (verified model + reductions) that **exports
  JSON**; a **separate web UI** (JS/TS) reads JSON and renders an interactive
  Hasse-diagram viewer/editor. Proof obligations live in Coq; drawing lives in
  the UI.
- **Rule representation:** support **both** a paper-style *synchronization
  schedule* and a lower-level *per-process operation sequence*; the schedule
  desugars into operations.
- **Reductions:** each step is proved to preserve poset **dimension** (full
  rigor), reusing `posets/dimension`.

## Decomposition into sub-projects

The branch is too large for one spec. It splits into four largely independent
sub-projects, each with its own spec → plan → implement cycle:

| ID | Sub-project | Depends on |
|----|-------------|------------|
| **A** | **Core model** — events as N chains + messages; the two rule representations and the concrete edge-set poset; agreement theorems; finite/dimension-ready carrier. | — |
| **B** | **Reductions** — step-by-step transformations to sync-shape, *with dimension-preservation proofs* (the hard research part). | A, `posets/dimension` |
| **C** | **Serialization** — Coq ↔ JSON file format covering both representations. | A |
| **D** | **Web UI** — JSON-driven Hasse-diagram viewer/editor. | C |

**Sequencing chosen:** spec and build **A first**, then return to B, C, D each
in turn. This document specifies **A only**. B/C/D get their own specs later.

---

# Sub-project A — Core model (this spec)

## A.0 Module layout

- New library directory `execution/`, added to `_CoqProject` as
  `-R execution Execution`.
- Separate from `happenedBefore/`, which stays as the abstract, *infinite*-history
  causal-order module. `execution/` is the finite, dimension-ready
  specialization the paper requires.
- Reuses `Posets.PosetClasses` (`IsPoset`), `Posets.FinitePoset`
  (`IsFinitePoset`), and `posets/dimension` (`PosetDimension`, `IsRealizer`, …).
- Files kept <500 lines each, each `Qed` <5 min, per the project's
  `coq-fast-compile` rule. Carrier/finiteness proofs split from edge/poset
  proofs. All builds go through `.claude/scripts/timed-build.sh`.

## A.1 The three representation layers

Top desugars to bottom; all three ultimately denote the **same** low-level
poset.

1. **Schedule** (high-level, paper-style "rules"): `N` processes + an ordered
   list of synchronization steps / frontiers (the `Ψ` / `mΨ(N,S)` flavor —
   "these processes synchronize here, then those there").
2. **Operation sequence** (mid-level): per process, an ordered list of ops —
   `Local`, `Send target tag`, `Recv tag` — with sends/recvs matched by `tag`.
   `desugar : Schedule → Program` lowers a schedule into this.
3. **Concrete edge-set poset** (low-level): a **finite** carrier of events,
   plus a direct-causality edge relation; the execution-poset order is its
   reflexive-transitive closure. This is the "just an edge set" form.

Pipeline: **Schedule → (desugar) → Program → (build) → finite edge-set poset.**

## A.2 The finite carrier

Given process lengths `len : Fin N → nat`, an event is the dependent pair

```
Event := { p : Fin N & Fin (len p) }
```

(`p` = process, `i` = local index within that process). Decision: **dependent
pairs**, not a flat `0..total-1` enumeration. This type is finite with
`cardinal Event (Full_set Event) (Σ_p len p)`, exactly what `IsFinitePoset` and
the dimension theory consume. (`happenedBefore`'s `nat × nat` `Event` is
infinite and cannot be used here.)

## A.3 Edges and order

Direct-causality edge relation `edge : Event → Event → Prop`:

- **program order:** `(p, i) → (p, i+1)` — consecutive events in the same
  process (the N chains);
- **message edge:** `(p_s, i_s) → (p_r, i_r)` when op `i_s` of process `p_s` is
  a `Send` matched (by tag) to op `i_r` of process `p_r` being the
  corresponding `Recv`.

Order: `hb := clos_refl_trans Event edge`.

## A.4 Proofs delivered in A

- `IsPoset Event hb`:
  - reflexivity / transitivity: free from `clos_refl_trans`;
  - **antisymmetry**: holds because every `edge` strictly increases a
    well-founded measure (a topological rank / Lamport-style timestamp computed
    from the program), so `hb` is acyclic *by construction* — no external
    `IsAcyclic` hypothesis (unlike `happenedBefore`).
- `IsFinitePoset Event hb (Σ_p len p)`.

This yields a finite poset that `posets/dimension`'s `PosetDimension` can be
instantiated against. *Computing* the dimension is sub-project B / the later
branch; A only proves the object is well-formed and finite so the machinery
applies.

**Main proof-effort risks in A:** (1) defining the acyclicity measure cleanly
so antisymmetry is short; (2) the dependent-pair carrier making `cardinal`
proofs fiddly. Mitigate by isolating the finiteness proof in its own file.

## A.5 Agreement / equivalence theorems

1. **Desugaring is faithful:** `wf_schedule s → wf_program (desugar s)` — a
   well-formed schedule lowers to a well-formed program (every `Recv` matched by
   exactly one `Send`, lengths consistent).
2. **Schedule ≡ program poset:** `∀ x y, hb_schedule s x y ↔ hb_program
   (desugar s) x y`. Ideally definitional; otherwise a short proof.
3. **Edge-set agreement:** a direct constructor `from_edges : list
   message_edge → ExecPoset` (build from an explicit edge set, no program),
   plus a theorem that the program-generated poset equals
   `from_edges (edges_of program)`. This is what makes "describe via rules" and
   "describe via just an edge set" provably interchangeable.

Public surface: one `ExecPoset` record (carrier + `hb` + `IsFinitePoset` proof)
reachable from any of the three inputs, with theorems that all routes coincide.

## A.6 Testing

- `Examples.v` encoding concrete paper executions — at minimum the `N=3` case
  (always dimension 2) and one `mΨ(4,5)` configuration — each built via **both**
  a schedule and an explicit edge set, with a compile-checked lemma that the two
  constructions yield **equal** posets.
- Small sanity lemmas: specific `hb` / concurrency facts (`e ∥ e'`, `e ≺ e'`) on
  those examples, fully proven.
- Whole-`execution/` build green through the `timed-build.sh` wrapper before A
  is considered done.

## A.7 Out of scope for A

Reduction steps + dimension-preservation proofs (B), JSON serialization (C), web
UI (D), and *computing* actual dimensions. The `docs/INDEX.md` index is updated
when `execution/` definitions land.

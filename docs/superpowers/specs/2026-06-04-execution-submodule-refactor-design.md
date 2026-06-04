# Execution submodule refactor — design

**Date:** 2026-06-04
**Branch (start):** `dev`
**Status:** approved design, pre-plan

## Goal

The `execution/` directory has grown to a flat 69-file Coq library (one theory
`Execution`). This refactor reorganizes it into thematic submodules, peels two
genuinely-separable concerns into their own theories, and does bounded
content-level cleanup — without changing any proven result. It connects to the
[north star](../../../CLAUDE.md) only indirectly (maintainability of the
execution-poset / low-dimension-clock work), so it is explicitly a **hygiene /
infrastructure** task, not a new result.

## Context / constraints discovered

- **One flat theory.** `execution/dune` is a single `coq.theory (name
  Execution)` with an explicit 69-entry `(modules …)` list; `_CoqProject` has
  `-R execution Execution` plus one line per file. No `include_subdirs`.
- **Imports resolve by suffix.** All 66 cross-module imports use `From Execution
  Require …`. Coq resolves `From Execution Require X` to any module whose
  logical path is under `Execution` and ends in `X`; all 69 base names are
  unique. **Consequence:** moving a file into a subdirectory of the *same*
  theory does not require editing a single import. Moving a file to a
  *different* theory (a peel) does.
- **Dependency graph is a clean DAG** (validated 2026-06-04). Layering: core →
  dimension → {sync, barriers, families}; clock and yaml are leaf consumers.
- **Only 3 files exceed 500 lines:** `DisjointChainsDim.v` (602),
  `FinPosetDimSurgery.v` (574), `ExtremumReduction.v` (558).
- **Build is heavy.** Every build goes through
  `bash .claude/scripts/timed-build.sh <secs> <target> [jobs] [mem_mb]`. A full
  `@all` is the cross-module correctness gate.
- `docs/INDEX.md` references execution definitions (~88 hits) but by
  logical/theorem name, not file path, so most references survive a move.

## Decisions (locked with user)

- **Scope:** restructure **+ light cleanup + deep refactor** (full scope).
- **Architecture:** **hybrid** — keep one `Execution` theory with thematic
  subdirectories for most modules; peel Yaml I/O and the online-clock /
  operational-semantics cluster into their own theories.
- **Examples placement:** **per-subdir `examples/` folder** (each theme owns its
  demonstrations, visually separated from the proof modules).

## Target layout

### Theory `Execution` (`-R execution Execution`, `include_subdirs qualified`)

| Subdir | Modules |
|--------|---------|
| `core/` | Op, Event, Edges, Rank, Finite, Poset, Schedule, ScheduleWf, FromEdges, Frontier, Agreement |
| `dimension/` | DimBridge, DimCriticalPairs, DimIso, ChainDim, DimTwoGeneric, FinPosetDimSurgery, FinPosetDim, FinExtremumDim, Ordinal, Reduction, ExtremumReduction |
| `sync/` | FullySync, FullySyncDim2, FullySyncDimExact, FinFullySync, FinFullySyncDim, SyncShape |
| `barriers/` | BarrierDim2, BarrierExecDim, ConnSync, WindowSync |
| `families/` | DisjointChainsDim, TransformA, TransformB, FrontierCompose |

Each subdir gets an `examples/` folder:

- `core/examples/`: FrontierExamples, ScheduleWfExamples
- `dimension/examples/`: DimExamples, DimExampleN3, Examples, FinPosetDimExamples,
  FinExtremumDimExamples, ReductionExamples, ExtremumReductionExamples,
  EminBlockDimExamples
- `sync/examples/`: FinFullySyncExamples, FinFullySyncDimExamples,
  SyncShapeExamples
- `barriers/examples/`: BarrierDim2Examples, BarrierExecDimExamples,
  ConnSyncExamples, WindowSyncExamples
- `families/examples/`: DisjointChainsDimExamples, TransformAExamples,
  TransformBExamples, FrontierComposeExamples

> **Sibling, not nested.** Because `Execution` uses `(include_subdirs
> qualified)`, that theory claims its *entire* subtree — a `coq.theory` stanza
> cannot live in a subdirectory of `execution/`. The peeled theories therefore
> live in **top-level sibling directories** `execution_yaml/` and
> `execution_clock/`, parallel to `execution/` (and to `posets/`, `list/`, …).

### Theory `ExecYaml` (`-R execution_yaml ExecYaml`)

Modules: Yaml, YamlLex, YamlParse. Examples: YamlExamples, YamlParseExamples.
Depends on `Execution` (only `core/Schedule`). Clean leaf — nothing in
`Execution` imports Yaml except the old aggregator.

### Theory `ExecClock` (`-R execution_clock ExecClock`)

Modules: OnlineClock, OnlineClockLocal, RoundSem. Examples: OnlineClockExamples,
OnlineClockLocalExamples, RoundSemExamples. Depends on `Execution` (core +
`sync/SyncShape`). `RoundSem` is the operational semantics consuming the clock;
it travels with the cluster.

Both peeled theories depend on `Execution` one-directionally → no cycles.

## Build wiring

- `execution/dune`: change the `Execution` stanza to use
  `(include_subdirs qualified)` and **remove** the explicit `(modules …)` list
  (let dune auto-discover the subtree). Keep `(theories Posets Dimension
  Stdlib)`.
- Add `execution_yaml/dune` (`coq.theory (name ExecYaml) (theories Execution
  Posets Dimension Stdlib)`) and `execution_clock/dune` (`coq.theory (name
  ExecClock) (theories Execution Posets Dimension Stdlib)`) as **top-level
  sibling directories** (see the "Sibling, not nested" note above). These may
  also use `(include_subdirs qualified)` if their own `examples/` subfolders are
  wanted.
- `_CoqProject`: `-R execution Execution`, `-R execution_yaml ExecYaml`,
  `-R execution_clock ExecClock`; rewrite the per-file path lines to the new
  subdir paths.

## Import churn

- **Inside `Execution`:** zero import edits (suffix resolution).
- **Peeled clusters:** update `From Execution Require …` → `From ExecYaml
  Require …` / `From ExecClock Require …` inside those ~5 + ~3 files and in
  `RoundSem`'s consumers. Cross-theory deps (e.g. `From Execution Require
  Schedule` inside ExecYaml) stay as `From Execution`.
- `execution/Execution.v` aggregator: drop the re-export of Yaml/YamlLex/
  YamlParse/OnlineClock/OnlineClockLocal/RoundSem (now in peeled theories);
  optionally add `Execution_all.v`-style umbrella files per theory.

## Phases (separate commits, green gate between each)

1. **Restructure (move-only).** Create subdirs, `git mv` files, switch dune to
   `include_subdirs qualified`, peel the two theories with import-prefix edits,
   update `_CoqProject`. **No proof content changes.** Gate: full `@all` build
   through `timed-build.sh` is green. Commit.
2. **Light cleanup.** Update `docs/INDEX.md` paths/sections; tidy the public
   surface (aggregators); normalize any obviously-off module/section naming.
   Gate: `@all` green. Commit.
3. **Deep refactor — file splits.** Split each >500-line file
   (DisjointChainsDim, FinPosetDimSurgery, ExtremumReduction) following the
   `coq-cascade-split-pattern` / `coq-fast-compile` discipline (each resulting
   `.v` < 500 lines, each Qed < 5 min). One file per commit, `@all` green after
   each.
4. **Deep refactor — dedup.** Discovery pass for duplicated lemmas/definitions
   across the new subdirs; **report candidates and get sign-off before
   editing.** Extract shared lemmas into the lowest common subdir. Gate: `@all`
   green. Commit.

## Verification

- Correctness gate after every phase: `bash .claude/scripts/timed-build.sh
  <secs> @all <jobs>`. Exit 0 required before commit.
- No result may change: the set of theorems/`Qed`s proven before and after must
  be identical (spot-check with `rocq_assumptions` / `PrintAssumptions` on key
  results; no new axioms).
- Each phase is independently revertible (separate commits, green checkpoints).

## Non-goals (YAGNI)

- No new theorems, no strengthening of existing results.
- No change to proof *strategy* except where a >500-line split forces lemma
  extraction.
- No aggressive dead-code removal — every current module is reachable from the
  aggregator; "pruning" is limited to the aggregator surface, not deleting
  proof modules.
- No reorganization of sibling top-level libraries (`posets/`, `list/`, etc.).

## Open items to confirm during planning

- Peeled theory names `ExecYaml` / `ExecClock` and sibling dir names
  `execution_yaml/` / `execution_clock/` (approved as defaults).
- Phase 1 starts with a **throwaway build of one moved file** to confirm
  `include_subdirs qualified` + suffix-resolution behave as predicted before the
  bulk `git mv`.

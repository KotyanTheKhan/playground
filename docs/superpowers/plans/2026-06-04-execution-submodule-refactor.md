# Execution Submodule Refactor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Reorganize the flat 69-file `execution/` Coq library into thematic subdirectories under one `Execution` theory, peel the Yaml and online-clock clusters into their own sibling theories, then split the three >500-line files — changing zero proven results.

**Architecture:** Hybrid. One `Execution` theory using dune `(include_subdirs qualified)` with subdirs `core/ dimension/ sync/ barriers/ families/` (each with an `examples/` folder). Two peeled sibling theories `ExecYaml` (`execution_yaml/`) and `ExecClock` (`execution_clock/`), both depending one-directionally on `Execution`. Within-theory moves need no import edits (Coq's `From Execution Require X` resolves by module-name suffix); only the peeled clusters and the aggregator change import prefixes.

**Tech Stack:** Coq/Rocq 9.1, dune (coq lang 0.8), the `timed-build.sh` wrapper. There are no unit tests — **the verification gate for every task is a green build** via `bash .claude/scripts/timed-build.sh`. Exit code 0 = pass; 124 = timeout, 137 = OOM, other = build error.

**Spec:** `docs/superpowers/specs/2026-06-04-execution-submodule-refactor-design.md`

---

## File → destination map (authoritative)

Within **`execution/`** (theory `Execution`):

- `core/`: Op, Event, Edges, Rank, Finite, Poset, Schedule, ScheduleWf, FromEdges, Frontier, Agreement
- `core/examples/`: FrontierExamples, ScheduleWfExamples
- `dimension/`: DimBridge, DimCriticalPairs, DimIso, ChainDim, DimTwoGeneric, FinPosetDimSurgery, FinPosetDim, FinExtremumDim, Ordinal, Reduction, ExtremumReduction
- `dimension/examples/`: DimExamples, DimExampleN3, Examples, FinPosetDimExamples, FinExtremumDimExamples, ReductionExamples, ExtremumReductionExamples, EminBlockDimExamples
- `sync/`: FullySync, FullySyncDim2, FullySyncDimExact, FinFullySync, FinFullySyncDim, SyncShape
- `sync/examples/`: FinFullySyncExamples, FinFullySyncDimExamples, SyncShapeExamples
- `barriers/`: BarrierDim2, BarrierExecDim, ConnSync, WindowSync
- `barriers/examples/`: BarrierDim2Examples, BarrierExecDimExamples, ConnSyncExamples, WindowSyncExamples
- `families/`: DisjointChainsDim, TransformA, TransformB, FrontierCompose
- `families/examples/`: DisjointChainsDimExamples, TransformAExamples, TransformBExamples, FrontierComposeExamples
- root stays: `Execution.v` (aggregator)

Moved out to **`execution_yaml/`** (theory `ExecYaml`):
- root: Yaml, YamlLex, YamlParse
- `examples/`: YamlExamples, YamlParseExamples

Moved out to **`execution_clock/`** (theory `ExecClock`):
- root: OnlineClock, OnlineClockLocal, RoundSem
- `examples/`: OnlineClockExamples, OnlineClockLocalExamples, RoundSemExamples

Total: 58 (Execution) + 5 (ExecYaml) + 6 (ExecClock) = 69. ✓

---

## Phase 0 — De-risk dune behaviour (throwaway, not committed)

Confirms that `(include_subdirs qualified)` + suffix import resolution work as predicted before any bulk move. Done on a scratch branch and reverted.

### Task 0: Single-file subdir smoke test

**Files:**
- Modify: `execution/dune`
- Move (temporary): `execution/ChainDim.v` → `execution/dimension/ChainDim.v`

- [ ] **Step 1: Create scratch branch**

```bash
cd /Users/maxstarling/code/research/playground
git checkout -b execution-refactor-phase0
```

- [ ] **Step 2: Add include_subdirs and drop the modules list**

Edit `execution/dune`. Replace the whole stanza with:

```
(include_subdirs qualified)

(coq.theory
 (name Execution)
 (package playground)
 (theories Posets Dimension Stdlib))
```

(Removing the explicit `(modules …)` list makes dune auto-discover the subtree.)

- [ ] **Step 3: Move one leaf module into a subdir**

`ChainDim.v` has no `From Execution` dependencies and few consumers — safest probe.

```bash
mkdir -p execution/dimension
git mv execution/ChainDim.v execution/dimension/ChainDim.v
```

- [ ] **Step 4: Build the consumer that imports ChainDim**

ChainDim is imported via `From Execution Require … ChainDim`. Build the whole theory to confirm suffix resolution still finds it at its new path:

```bash
bash .claude/scripts/timed-build.sh 1800 execution 4
```

Expected: exit 0. If it fails with "Cannot find a physical path bound to logical name ChainDim", the suffix-resolution assumption is wrong — STOP and reassess (fallback: each subdir becomes its own `-Q`-mapped theory).

- [ ] **Step 5: Discard the scratch branch**

```bash
git checkout dev
git branch -D execution-refactor-phase0
```

Phase 0 produces no commit — it only validates the mechanism.

---

## Phase 1 — Restructure (move-only, no proof content changes)

One commit. The repo must be green at the end.

### Task 1: Create the working branch

**Files:** none

- [ ] **Step 1: Branch from dev**

```bash
cd /Users/maxstarling/code/research/playground
git checkout dev
git checkout -b execution-refactor
```

### Task 2: Create directory skeleton

**Files:** new directories under `execution/`, `execution_yaml/`, `execution_clock/`

- [ ] **Step 1: Make all destination dirs**

```bash
cd /Users/maxstarling/code/research/playground
mkdir -p execution/core/examples execution/dimension/examples \
         execution/sync/examples execution/barriers/examples \
         execution/families/examples \
         execution_yaml/examples execution_clock/examples
```

### Task 3: Move the Execution-theory modules

**Files:** `git mv` of 57 files (Execution.v stays at root)

- [ ] **Step 1: Move core/**

```bash
cd /Users/maxstarling/code/research/playground/execution
for m in Op Event Edges Rank Finite Poset Schedule ScheduleWf FromEdges Frontier Agreement; do git mv $m.v core/$m.v; done
for m in FrontierExamples ScheduleWfExamples; do git mv $m.v core/examples/$m.v; done
```

- [ ] **Step 2: Move dimension/**

```bash
cd /Users/maxstarling/code/research/playground/execution
for m in DimBridge DimCriticalPairs DimIso ChainDim DimTwoGeneric FinPosetDimSurgery FinPosetDim FinExtremumDim Ordinal Reduction ExtremumReduction; do git mv $m.v dimension/$m.v; done
for m in DimExamples DimExampleN3 Examples FinPosetDimExamples FinExtremumDimExamples ReductionExamples ExtremumReductionExamples EminBlockDimExamples; do git mv $m.v dimension/examples/$m.v; done
```

- [ ] **Step 3: Move sync/**

```bash
cd /Users/maxstarling/code/research/playground/execution
for m in FullySync FullySyncDim2 FullySyncDimExact FinFullySync FinFullySyncDim SyncShape; do git mv $m.v sync/$m.v; done
for m in FinFullySyncExamples FinFullySyncDimExamples SyncShapeExamples; do git mv $m.v sync/examples/$m.v; done
```

- [ ] **Step 4: Move barriers/**

```bash
cd /Users/maxstarling/code/research/playground/execution
for m in BarrierDim2 BarrierExecDim ConnSync WindowSync; do git mv $m.v barriers/$m.v; done
for m in BarrierDim2Examples BarrierExecDimExamples ConnSyncExamples WindowSyncExamples; do git mv $m.v barriers/examples/$m.v; done
```

- [ ] **Step 5: Move families/**

```bash
cd /Users/maxstarling/code/research/playground/execution
for m in DisjointChainsDim TransformA TransformB FrontierCompose; do git mv $m.v families/$m.v; done
for m in DisjointChainsDimExamples TransformAExamples TransformBExamples FrontierComposeExamples; do git mv $m.v families/examples/$m.v; done
```

- [ ] **Step 6: Verify only Execution.v remains at execution/ root**

```bash
ls /Users/maxstarling/code/research/playground/execution/*.v
```

Expected: exactly `execution/Execution.v`.

### Task 4: Move the peeled clusters

**Files:** `git mv` into sibling dirs

- [ ] **Step 1: Move Yaml cluster**

```bash
cd /Users/maxstarling/code/research/playground
git mv execution/Yaml.v       execution_yaml/Yaml.v
git mv execution/YamlLex.v    execution_yaml/YamlLex.v
git mv execution/YamlParse.v  execution_yaml/YamlParse.v
git mv execution/YamlExamples.v       execution_yaml/examples/YamlExamples.v
git mv execution/YamlParseExamples.v  execution_yaml/examples/YamlParseExamples.v
```

- [ ] **Step 2: Move Clock cluster**

```bash
cd /Users/maxstarling/code/research/playground
git mv execution/OnlineClock.v       execution_clock/OnlineClock.v
git mv execution/OnlineClockLocal.v  execution_clock/OnlineClockLocal.v
git mv execution/RoundSem.v          execution_clock/RoundSem.v
git mv execution/OnlineClockExamples.v       execution_clock/examples/OnlineClockExamples.v
git mv execution/OnlineClockLocalExamples.v  execution_clock/examples/OnlineClockLocalExamples.v
git mv execution/RoundSemExamples.v          execution_clock/examples/RoundSemExamples.v
```

### Task 5: Rewrite dune files

**Files:**
- Modify: `execution/dune`
- Create: `execution_yaml/dune`, `execution_clock/dune`

- [ ] **Step 1: Replace `execution/dune`**

Full new contents:

```
(include_subdirs qualified)

(coq.theory
 (name Execution)
 (package playground)
 (theories Posets Dimension Stdlib))
```

- [ ] **Step 2: Create `execution_yaml/dune`**

```
(include_subdirs qualified)

(coq.theory
 (name ExecYaml)
 (package playground)
 (theories Execution Posets Dimension Stdlib))
```

- [ ] **Step 3: Create `execution_clock/dune`**

```
(include_subdirs qualified)

(coq.theory
 (name ExecClock)
 (package playground)
 (theories Execution Posets Dimension Stdlib))
```

### Task 6: Fix peeled-cluster imports

Only modules that import a *peeled* sibling change prefix. Modules importing
only `Execution`-resident names (Schedule, ScheduleWf, SyncShape, Ordinal,
DisjointChainsDim, BarrierExecDim, …) stay `From Execution`.

**Files:** `execution_yaml/YamlParse.v`, `execution_yaml/examples/*.v`, `execution_clock/RoundSem.v`, `execution_clock/OnlineClockLocal.v`, `execution_clock/examples/*.v`

- [ ] **Step 1: `execution_yaml/YamlParse.v`** — change line 3

From:
```coq
From Execution Require Import Yaml YamlLex.
```
To:
```coq
From ExecYaml Require Import Yaml YamlLex.
```

- [ ] **Step 2: `execution_yaml/examples/YamlExamples.v`** — split line 6

From:
```coq
From Execution Require Import Schedule Yaml.
```
To:
```coq
From Execution Require Import Schedule.
From ExecYaml Require Import Yaml.
```

- [ ] **Step 3: `execution_yaml/examples/YamlParseExamples.v`** — change line 3

From:
```coq
From Execution Require Import Yaml YamlLex YamlParse.
```
To:
```coq
From ExecYaml Require Import Yaml YamlLex YamlParse.
```

- [ ] **Step 4: `execution_clock/OnlineClockLocal.v`** — split the import (lines 6-7)

The current 2-line import ends in `… BarrierExecDim OnlineClock.` Move only
`OnlineClock` to ExecClock. New form:
```coq
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim.
From ExecClock Require Import OnlineClock.
```

- [ ] **Step 5: `execution_clock/RoundSem.v`** — split line 6

From:
```coq
From Execution Require Import Op OnlineClock OnlineClockLocal.
```
To:
```coq
From Execution Require Import Op.
From ExecClock Require Import OnlineClock OnlineClockLocal.
```

- [ ] **Step 6: `execution_clock/examples/OnlineClockExamples.v`** — split (lines 5-7)

Current import ends `… BarrierExecDimExamples OnlineClock.` New form:
```coq
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                             Ordinal DisjointChainsDim BarrierExecDim
                             BarrierExecDimExamples.
From ExecClock Require Import OnlineClock.
```

- [ ] **Step 7: `execution_clock/examples/OnlineClockLocalExamples.v`** — split (lines 4-6)

Current import ends `… BarrierExecDim OnlineClock OnlineClockExamples OnlineClockLocal.` New form:
```coq
From Execution Require Import Op Event Poset Schedule ScheduleWf
                             BarrierExecDim.
From ExecClock Require Import OnlineClock OnlineClockExamples OnlineClockLocal.
```

- [ ] **Step 8: `execution_clock/examples/RoundSemExamples.v`** — change line 4

From:
```coq
From Execution Require Import Op OnlineClock OnlineClockLocal RoundSem.
```
To:
```coq
From Execution Require Import Op.
From ExecClock Require Import OnlineClock OnlineClockLocal RoundSem.
```

- [ ] **Step 9: Sanity-grep for leftovers**

```bash
cd /Users/maxstarling/code/research/playground
grep -rnE "From Execution Require.*(Yaml|OnlineClock|RoundSem)" execution_yaml execution_clock
```
Expected: no output. (Any hit is a missed split.)

### Task 7: Update the aggregator `execution/Execution.v`

**Files:** Modify `execution/Execution.v`

- [ ] **Step 1: Drop peeled modules from the Export line**

Remove `Yaml YamlLex YamlParse OnlineClock OnlineClockLocal RoundSem` from the
`From Execution Require Export …` list. The peeled theories are reachable via
`From ExecYaml Require …` / `From ExecClock Require …` directly; the `Execution`
umbrella no longer re-exports them. New line (single line):

```coq
From Execution Require Export Op Event Finite Edges Rank Poset Schedule FromEdges Agreement DimBridge DimCriticalPairs Frontier DimIso Ordinal FullySync Reduction ExtremumReduction BarrierDim2 FinPosetDimSurgery FinPosetDim FinFullySync FullySyncDim2 FinExtremumDim FinFullySyncDim FullySyncDimExact ChainDim TransformA SyncShape ScheduleWf DimTwoGeneric ConnSync WindowSync TransformB DisjointChainsDim BarrierExecDim FrontierCompose.
```

### Task 8: Update `_CoqProject`

**Files:** Modify `_CoqProject`

- [ ] **Step 1: Add the two sibling `-R` lines**

After the line `-R execution Execution` (line 10), add:
```
-R execution_yaml ExecYaml
-R execution_clock ExecClock
```

- [ ] **Step 2: Regenerate the execution file-path block**

Delete the old `execution/*.v` lines (the contiguous block, currently lines
71-139) and replace with freshly-discovered paths:

```bash
cd /Users/maxstarling/code/research/playground
# print the new block (paste it in place of the old execution/*.v lines)
find execution execution_yaml execution_clock -name '*.v' | sort
```

The per-file lines are for editor tooling only (dune drives the build); they
must list the new paths. Order is not significant for tooling.

### Task 9: Phase-1 build gate + commit

**Files:** none (verification)

- [ ] **Step 1: Full project build**

```bash
cd /Users/maxstarling/code/research/playground
bash .claude/scripts/timed-build.sh 1800 @all 4
```
Expected: exit 0. On timeout (124) raise to 2400; on a real error, fix the
offending import/dune issue before proceeding — do **not** commit red.

- [ ] **Step 2: Confirm no proof content changed**

```bash
cd /Users/maxstarling/code/research/playground
git diff --stat dev -- 'execution*/**/*.v' | grep -vE 'Execution.v|YamlParse.v|YamlExamples.v|YamlParseExamples.v|RoundSem.v|OnlineClockLocal.v|OnlineClockExamples.v|OnlineClockLocalExamples.v|RoundSemExamples.v'
```
Expected: every remaining line shows pure renames (`{old => new}`) with `0`
insertions/deletions. Only the 9 import-edited files may show content churn.

- [ ] **Step 3: Commit**

```bash
cd /Users/maxstarling/code/research/playground
git add -A
git commit -m "refactor(execution): split flat library into core/dimension/sync/barriers/families subdirs; peel ExecYaml + ExecClock theories"
```

---

## Phase 2 — Light cleanup

One commit. Green at the end.

### Task 10: Update docs/INDEX.md

**Files:** Modify `docs/INDEX.md`

- [ ] **Step 1: Find stale path references**

```bash
cd /Users/maxstarling/code/research/playground
grep -nE 'execution/[A-Za-z]+\.v' docs/INDEX.md
```

- [ ] **Step 2: Rewrite each to its new subdir path**

For every hit, update the path using the File→destination map above (e.g.
`execution/Schedule.v` → `execution/core/Schedule.v`, `execution/Yaml.v` →
`execution_yaml/Yaml.v`). If INDEX has an "execution" section grouped by file,
regroup its headings to match the five subdirs + two peeled theories.

- [ ] **Step 3: Verify no stale paths remain**

```bash
cd /Users/maxstarling/code/research/playground
for p in $(grep -oE 'execution[A-Za-z_]*/[A-Za-z/]+\.v' docs/INDEX.md | sort -u); do test -f "$p" || echo "STALE: $p"; done
```
Expected: no `STALE:` lines.

- [ ] **Step 4: Commit**

```bash
cd /Users/maxstarling/code/research/playground
git add docs/INDEX.md
git commit -m "docs(execution): update INDEX paths for submodule layout"
```

---

## Phase 3 — Deep refactor: split files >500 lines

One commit per file. Follow `coq-cascade-split-pattern` / `coq-fast-compile`:
each resulting `.v` < 500 lines, each Qed < 5 min, no result removed. The
mechanic for each: identify a self-contained block of lemmas, move it to a new
sibling file in the same subdir, add `From Execution Require Import <parent>` if
the new file needs the parent's earlier definitions, and have the parent
`Require Import` the new file if it needs the extracted lemmas. Re-run the gate.

### Task 11: Split `families/DisjointChainsDim.v` (602 lines)

**Files:**
- Modify: `execution/families/DisjointChainsDim.v`
- Create: `execution/families/DisjointChainsDimCore.v` (or similarly-named extract)

- [ ] **Step 1: Identify the cut point**

```bash
cd /Users/maxstarling/code/research/playground
grep -nE '^(Lemma|Theorem|Definition|Section|End) ' execution/families/DisjointChainsDim.v
```
Pick a `Section`/lemma-group boundary that splits the file near the middle with
no backward references from the upper half into the lower half.

- [ ] **Step 2: Move the lower group to the new file**

Create `execution/families/DisjointChainsDimAux.v` starting with the same
preamble imports as the parent (copy the `From … Require …` header), then the
moved lemmas. In `DisjointChainsDim.v`, if it now uses those lemmas, add
`From Execution Require Import DisjointChainsDimAux.` after its header.
(If instead the *aux* file depends on the *core* lemmas, reverse the dependency:
aux imports the parent and the parent keeps the upper half.)

- [ ] **Step 3: Build gate**

```bash
cd /Users/maxstarling/code/research/playground
bash .claude/scripts/timed-build.sh 1800 execution 4
```
Expected: exit 0, and both files now < 500 lines (`wc -l`).

- [ ] **Step 4: Commit**

```bash
cd /Users/maxstarling/code/research/playground
git add -A
git commit -m "refactor(execution): split DisjointChainsDim into two <500-line files"
```

### Task 12: Split `dimension/FinPosetDimSurgery.v` (574 lines)

**Files:**
- Modify: `execution/dimension/FinPosetDimSurgery.v`
- Create: `execution/dimension/FinPosetDimSurgeryAux.v`

- [ ] **Step 1: Identify the cut point**

```bash
cd /Users/maxstarling/code/research/playground
grep -nE '^(Lemma|Theorem|Definition|Section|End) ' execution/dimension/FinPosetDimSurgery.v
```

- [ ] **Step 2: Extract the lower lemma group** into `FinPosetDimSurgeryAux.v` with the parent's import header; wire the dependency direction as in Task 11 Step 2.

- [ ] **Step 3: Build gate**

```bash
cd /Users/maxstarling/code/research/playground
bash .claude/scripts/timed-build.sh 1800 execution 4
```
Expected: exit 0, both files < 500 lines.

- [ ] **Step 4: Commit**

```bash
cd /Users/maxstarling/code/research/playground
git add -A
git commit -m "refactor(execution): split FinPosetDimSurgery into two <500-line files"
```

### Task 13: Split `dimension/ExtremumReduction.v` (558 lines)

**Files:**
- Modify: `execution/dimension/ExtremumReduction.v`
- Create: `execution/dimension/ExtremumReductionAux.v`

- [ ] **Step 1: Identify the cut point**

```bash
cd /Users/maxstarling/code/research/playground
grep -nE '^(Lemma|Theorem|Definition|Section|End) ' execution/dimension/ExtremumReduction.v
```

- [ ] **Step 2: Extract the lower lemma group** into `ExtremumReductionAux.v`; wire dependency direction as in Task 11 Step 2.

- [ ] **Step 3: Build gate**

```bash
cd /Users/maxstarling/code/research/playground
bash .claude/scripts/timed-build.sh 1800 execution 4
```
Expected: exit 0, both files < 500 lines.

- [ ] **Step 4: Commit**

```bash
cd /Users/maxstarling/code/research/playground
git add -A
git commit -m "refactor(execution): split ExtremumReduction into two <500-line files"
```

---

## Phase 4 — Deep refactor: dedup (report-first, gated by approval)

The most open-ended phase. **Do not edit before reporting candidates and getting
explicit sign-off** — this prevents scope balloon.

### Task 14: Duplication discovery report

**Files:** none (analysis only)

- [ ] **Step 1: Find repeated lemma/definition statements across subdirs**

```bash
cd /Users/maxstarling/code/research/playground
grep -rhoE '^(Lemma|Definition|Theorem|Fact) [A-Za-z0-9_]+' execution execution_yaml execution_clock \
  | sed -E 's/^(Lemma|Definition|Theorem|Fact) //' | sort | uniq -d
```

- [ ] **Step 2: For each duplicate name, inspect the statements** and classify: true duplicate (same statement, extractable to lowest common subdir) vs. coincidental name reuse (leave alone).

- [ ] **Step 3: Write the candidate list** to `docs/superpowers/specs/2026-06-04-execution-dedup-candidates.md` — each candidate: name, files, identical-or-not, proposed home subdir, risk. **Stop and present to the user.** Proceed to Task 15 only on approval.

### Task 15: Apply approved extractions (one per commit)

**Files:** per approved candidate

- [ ] **Step 1:** For each approved duplicate, move the canonical statement+proof to the lowest common subdir module (or a new `<Theme>Shared.v`), delete the copies, and add `From Execution Require Import <home>` where consumers need it.
- [ ] **Step 2: Build gate** after each extraction:

```bash
cd /Users/maxstarling/code/research/playground
bash .claude/scripts/timed-build.sh 1800 @all 4
```
Expected: exit 0.
- [ ] **Step 3: Commit** each extraction separately:

```bash
git add -A && git commit -m "refactor(execution): dedup <name> into shared module"
```

---

## Final verification

### Task 16: Whole-project green + axiom check

- [ ] **Step 1: Clean full build**

```bash
cd /Users/maxstarling/code/research/playground
bash .claude/scripts/timed-build.sh 2400 @all 4
```
Expected: exit 0.

- [ ] **Step 2: Confirm no new axioms on a key result**

Use the rocq-mcp `rocq_assumptions` tool (or `Print Assumptions blo_iff_stamp`
in `execution_clock/OnlineClock.v`) and compare against the pre-refactor
baseline noted in memory `project_online_clock_done` — the assumption set must be
unchanged (no new axioms introduced by the move).

- [ ] **Step 3: Hand off** per `superpowers:finishing-a-development-branch` (merge to dev / PR decision is the user's).

---

## Self-review notes

- **Spec coverage:** restructure (Tasks 2-9), peel ExecYaml/ExecClock (Tasks 4-7),
  per-subdir examples (Task 2 dirs + Task 3 moves), light cleanup/INDEX (Task 10),
  >500-line splits (Tasks 11-13), dedup report-first (Tasks 14-15), verification
  gates (every phase + Task 16). All spec sections map to a task.
- **Phase 0 is throwaway** and explicitly reverted — it de-risks the one
  empirical unknown (dune `include_subdirs qualified` + suffix resolution) before
  the bulk move, per the spec's open item.
- **No proof strategy changes** except the forced lemma extractions in Phase 3.
- **Naming consistency:** new theories `ExecYaml`/`ExecClock`, sibling dirs
  `execution_yaml/`/`execution_clock/`, extract files suffixed `Aux`, used
  consistently across tasks.

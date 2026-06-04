# Phase 4 Dedup Candidate Report — execution* directories

**Date:** 2026-06-04
**Branch:** `execution-refactor`
**Scope:** `execution/`, `execution_yaml/`, `execution_clock/`

## Summary

**2 TRUE DUPLICATE candidates** (both are in example-only files, zero risk).
**12 COINCIDENTAL name collisions** (same name, different statement / different poset / different scope — leave alone).
**0 production-file name collisions** across any of the three directories.
FrontierCompose placement: **recommend moving to `execution/dimension/`** (one-line justification below).

---

## TRUE DUPLICATE candidates

### 1. `exec_dim2`, `exec_4_canonical`, `poset_s3` (three names, one conflict site)

| Name | File A | File B |
|------|--------|--------|
| `exec_dim2` | `execution_yaml/examples/YamlExamples.v:11` | `execution_yaml/examples/YamlParseExamples.v:7` |
| `exec_4_canonical` | `execution_yaml/examples/YamlExamples.v:12–13` | `execution_yaml/examples/YamlParseExamples.v:8–9` |
| `poset_s3` | `execution_yaml/examples/YamlExamples.v:14–15` | `execution_yaml/examples/YamlParseExamples.v:10–11` |

**Statements:** Byte-for-byte identical in both files.

```coq
(* both files *)
Definition exec_dim2 : YamlExecution := {| ye_nprocs := 2; ye_syncs := [(0,1)] |}.
Definition exec_4_canonical : YamlExecution :=
  {| ye_nprocs := 4; ye_syncs := [(0,1);(1,2);(2,3);(0,2)] |}.
Definition poset_s3 : YamlPoset :=
  {| yp_nverts := 6; yp_edges := [(0,4);(0,5);(1,3);(1,5);(2,3);(2,4)] |}.
```

**Classification:** TRUE DUPLICATE — same records, same intent (shared test fixtures for YAML round-trip and parse examples).

**Proposed resolution:**
- Create `execution_yaml/examples/YamlTestFixtures.v` (or a `Fixtures` section in either file) exporting these three definitions.
- Both `YamlExamples.v` and `YamlParseExamples.v` `Require Import YamlTestFixtures` and drop their local copies.
- **Canonical home:** `execution_yaml/examples/` (both consumers live there).
- **Risk:** Low. These are example-only `vm_compute`-verified `Example`s; no production proof is sensitive to where these records live.
- **Consumer edits needed:** Two files (the two example files themselves).

---

### 2. `wf_frontier_pair`

| File | Line |
|------|------|
| `execution/barriers/examples/ConnSyncExamples.v` | 10 |
| `execution/barriers/examples/WindowSyncExamples.v` | 16 |

**Statements:** Byte-for-byte identical (statement and full proof body).

```coq
Lemma wf_frontier_pair : forall n a b, a < n -> b < n -> a <> b -> wf_frontier n [(a,b)].
```

**Classification:** TRUE DUPLICATE — same utility lemma about a singleton frontier, copied verbatim into two example files that both live in `execution/barriers/examples/`.

**Proposed resolution:**
- Promote to `execution/core/ScheduleWf.v` (where `wf_frontier` is defined) as a named lemma.
- Both example files drop the local copy and rely on the import they already have (`From Execution Require Import ... ScheduleWf`).
- **Canonical home:** `execution/core/ScheduleWf.v`.
- **Risk:** Low. Pure utility lemma; proof is short and independent.
- **Consumer edits needed:** Two example files (delete the local lemma; no proof adjustments needed since downstream uses are the same).

---

## Coincidental name collisions (leave alone)

These names appear in multiple files but refer to **different statements on different posets or different scopes**. Unifying them would be incorrect or misleading.

| Name | File A | File B | Why coincidental |
|------|--------|--------|------------------|
| `M1` | `execution/dimension/examples/EminBlockDimExamples.v:33` — a linear order on a 3-element type `T3` via `kB` | `execution/families/FrontierCompose.v:56` — a bipartite realizer on `Carrier (Fin.t mA) (Fin.t mB)` parameterized by rank functions | Completely different types and semantics |
| `M2` | Same pair of files, line 34 vs 65 | Same pair of files, line 34 vs 65 | Same reason as M1 |
| `s_demo` | `execution/barriers/examples/ConnSyncExamples.v:7` | `execution/sync/examples/SyncShapeExamples.v:28` | Identical schedule *record* (2-proc, frontiers `[(0,1);(1,0)]`), but each example file builds its own `ep_carrier` inhabitants. Merging would require a shared example module spanning two subdirectories — fragile, not worth it for test helpers |
| `hb_a_b` | `execution/sync/examples/SyncShapeExamples.v:123` — `ep_order (exec_of_schedule s_demo) da db`, a sync/message edge | `execution/dimension/examples/DimExamples.v:215` — `ep_order E_min ev_a ev_b`, a program-order edge on a *different* schedule (`sched_min` has `[(0,1);[]]`, not `[(0,1);[(1,0)]]`) | Different posets, different edges, coincidentally same name |
| `hb_a_c` | `SyncShapeExamples.v:109` — `da->dc` on `exec_of_schedule s_demo`, a prog-order edge | `DimExamples.v:221` — `ev_a->ev_c` on `E_min`, a sync edge | Different posets, different edge types |
| `hb_a_d` | `SyncShapeExamples.v:139` — derived `da->dd` on `s_demo` | `DimExamples.v:234` — derived `ev_a->ev_d` on `E_min` | Different posets |
| `valid_a` | `SyncShapeExamples.v:42` — `In (ValidSet (desugar s_demo)) (0,0)` | `DimExamples.v:190` — `In (ValidSet (desugar sched_min)) (0,0)` | Different schedules; the tuple is the same but the `ValidSet` is for a different execution |
| `valid_b` | `SyncShapeExamples.v:44` — `(1,0)` in `s_demo` | `DimExamples.v:192` — `(0,1)` in `sched_min` | Different event coordinates, different schedules |
| `valid_c` | `SyncShapeExamples.v:46` — `(0,1)` in `s_demo` | `DimExamples.v:194` — `(1,0)` in `sched_min` | Same as above |
| `valid_d` | `SyncShapeExamples.v:48` — `(1,1)` in `s_demo` | `DimExamples.v:196` — `(1,1)` in `sched_min` | Coincidentally same pair but different executions |

Note: `s_demo` records are also copied into `ConnSyncExamples.v`; see the `s_demo` row above.

---

## FrontierCompose placement recommendation

**Recommendation: Move `execution/families/FrontierCompose.v` to `execution/dimension/FrontierCompose.v`.**

Justification: The file imports only `From Posets` and `From Dimension` — no `From Execution` at all. Its content is pure abstract dimension theory (the `compose_le` bipartite poset, the Ferrers/threshold dichotomy `threshold_dim_le2`, and the `crown3_dim_ge_3` lower-bound proof). It is a misfit in `families/`, whose other four files (`DisjointChainsDim`, `TransformA`, `TransformB`, `DisjointChainsDimAux`) all import execution-model types (`Op`, `Event`, `Edges`, `Rank`, `Poset`). Moving it aligns it with the pure-abstract files already in `dimension/` (`ChainDim.v`, `DimIso.v`, `FinPosetDim.v`, `Reduction.v`).

Consumer impact: The single consumer outside the file itself is `execution/families/examples/FrontierComposeExamples.v`, which does `From Execution Require Import FrontierCompose`. With `include_subdirs qualified`, this import resolves by module name regardless of subdirectory; the consumer does not need changes. `Execution.v` (the barrel file) also exports `FrontierCompose` by module name and would likewise need no change. The move is transparent.

---

## Recommended actions, in priority order

1. **[High value, Low risk] Extract shared YAML test fixtures.**
   Create `execution_yaml/examples/YamlTestFixtures.v` defining `exec_dim2`, `exec_4_canonical`, `poset_s3`. Update `YamlExamples.v` and `YamlParseExamples.v` to `Require Import YamlTestFixtures` and remove the three local definitions (6 lines deleted from each). Eliminates the only true duplicate in production test contracts.

2. **[Low value, Low risk] Promote `wf_frontier_pair` to `ScheduleWf.v`.**
   Move the lemma (statement + 7-line proof) from the two barrier example files into `execution/core/ScheduleWf.v` just after the `wf_frontier` definition. Both example files already import `ScheduleWf`; delete the local copies. This is a small quality-of-life fix; do it opportunistically if touching those files for another reason.

3. **[Optional, Zero risk] Move `FrontierCompose.v` to `execution/dimension/`.**
   Pure directory hygiene. No consumer edits needed due to `include_subdirs qualified`. Do this only if the reviewer wants the directory structure to strictly separate execution-model files from abstract poset/dimension theory.

---

## What was NOT found

- No production-file (non-example) name collisions across any of `execution/`, `execution_yaml/`, `execution_clock/`.
- No cross-directory collisions between `execution_clock` and any other directory.
- No near-duplicate helper lemmas in non-example files beyond the `IsGlobalMin`/`fin_global_min` pair (which are the same concept parameterized differently — one is execution-specific with an explicit `ExecPoset`, the other is Section-scoped over a generic `R`; consolidation would require a Section refactor with no clear win).
- Overall duplication level: very low. The refactor was clean.

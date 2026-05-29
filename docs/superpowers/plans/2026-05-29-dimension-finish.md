# Finishing the Dimension Submodule — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close all 5 remaining `Admitted` in `posets/dimension/` so `hiraguchi_bound` and the full chain are admit-free.

**Architecture:** Two independent tracks. Track A (n=5 base, counts 5–8) reduces each obligation through the committed bridge `two_realizer_from_fin_ranks` to constructing two rank functions on `Fin.t 5`; a probe decides between a uniform `3^10`-orientation reflection and per-count explicit constructions. Track B closes `trotter_coverage_via_extremality` (general-n inductive keystone) by progressive decomposition. Design: `docs/superpowers/specs/2026-05-29-dimension-finish-design.md`.

**Tech Stack:** Coq 9.1 (Stdlib only), `Fin.t 5` boolean reflection, `native_compute`/`vm_compute`, builds via `.claude/scripts/timed-build.sh <secs> <target> [jobs] [mem_mb]`.

**Build rule (every task):** never bare `dune`/`mise build`; always the wrapper. Reflection/probe builds use `jobs=1` and an explicit `mem_mb` cap.

---

## File Structure

- `N5Exhaustive/N5RealizerTransport.v` — DONE: bridge `two_realizer_from_fin_ranks`.
- `N5Exhaustive/N5Orient.v` — NEW (Track A, if uniform): the `3^10` orientation enumeration, `has_realizer_b` search, `n5_matrix_two_realizable` (reflection), and the wire to "any non-chain n=5 poset has a 2-realizer".
- `N5Exhaustive/EdgeCount{5,6,7,8,9}.v`, the per-count dispatch in `N5DispatcherShapes.v` — DELETED if uniform succeeds (else `EdgeCount{5,6,7,8}.v` get explicit proofs).
- `RemovablePairs.v` — Track B: `trotter_coverage_via_extremality` + new focused sub-lemmas.
- Status doc: `docs/superpowers/specs/2026-05-28-dimension-replan-status.md` (update each session).

---

## Track A — n=5 base case

### Task A1: Feasibility probe for the 3^10 orientation enumeration (Session 1)

**Files:** Create scratch `N5Exhaustive/ZZProbe.v` (deleted after).

- [ ] **Step 1: Write the probe.** Enumerate orientation-assignments of the 10 unordered pairs of `Fin.t 5` (each → none/fwd/bwd), build the strict matrix, count those that are posets (`is_poset_b`) and non-total, and (for a sample / all) run a `has_realizer_b` search over candidate rank pairs. Concretely, first measure just the enumeration + poset filter:

```coq
From Dimension.N5Exhaustive Require Import N5Reflect.
From Stdlib Require Import List.
(* 10 unordered pairs as (i,j) with i<j among f0..f4; assignment : list (option bool) of length 10.
   Reuse N5Reflect's all_pairs / from_edges if convenient, or a fresh generator. *)
Definition orientations : list <assignment> := (* 3^10 = 59049 *) ...
Definition probe_posets : nat := length (filter (fun o => is_poset_b (mat_of o)) orientations).
Time Eval vm_compute in length orientations.   (* expect 59049 *)
Time Eval vm_compute in probe_posets.
```

- [ ] **Step 2: Build with watchdog.** Run: `bash .claude/scripts/timed-build.sh 180 posets/dimension/N5Exhaustive/ZZProbe.vo 1 20000`. Record `length` and `probe_posets` and their `Time` outputs.
- [ ] **Step 3: Probe the realizer search cost.** Add `Definition probe_realizable : bool := forallb (fun o => negb (is_poset_b (mat_of o)) || is_total_b (mat_of o) || has_realizer_b (mat_of o)) orientations.` and `Time Eval vm_compute in probe_realizable.` Rebuild (same wrapper). Expected: `true` in tractable time (target < 120 s; if killed → infeasible).
- [ ] **Step 4: Decide.** If Step 3 is green and tractable → proceed to A2 (uniform). If killed/slow → delete A2/A3, jump to A4 (per-count). Record the decision in the status doc and commit it. Delete `ZZProbe.v`.

### A1 OUTCOME (Session 1, 2026-05-29): uniform-with-SEARCH is infeasible.

`is_poset_b` is ~2 ms/item under vm_compute → the poset filter alone over the
59049 assignments exceeds 120 s; a 120×120 realizer SEARCH per poset is
hopeless. Decision: do NOT search. Two live options for S2 (A5 recommended):

- **A5 (recommended): candidate realizer-compute + chunked reflection verify.**
  Define a CHEAP, deterministic `compute_realizer (M:M5) : (rank * rank)` —
  candidate: `L1 := toposort M` (index tie-break); `L2 := toposort` of M with
  every incomparable pair forced OPPOSITE to its L1 order (i.e. M ∪ {(j,i) :
  i <_L1 j, incomparable}); if that augmentation is acyclic, `{L1,L2}` realizes
  M. Then `realizes_b M (compute_realizer M)` is a cheap check. Prove
  `forall o, is_poset_b (mat_of o) = true -> is_total_b (mat_of o) = false ->
  realizes_b (mat_of o) (compute_realizer (mat_of o)) = true` by native_compute,
  CHUNKED (~25 chunks of ~2360, mirroring EdgeCount4's 5-chunk pattern; build
  each `-j1`, pre-`pkill dune`). The reflection VERIFIES the candidate algorithm
  is correct on all n=5 posets. If a chunk returns false, refine
  `compute_realizer`. Then reflect to the bridge `two_realizer_from_fin_ranks`
  and close counts 5–8 uniformly (delete EdgeCount5–9).
- **A4 (fallback): per-count explicit.** Risky — naive destruct of R2_matrix's
  ~20 entries is 2^20 proof branches; needs heavy pruning. Prefer A5.

Tooling note for S2: ALWAYS `pkill -9 -f dune` before a fresh reflection build
(stale dune servers forward/queue builds and confounded the A1 probe; the
wrapper now reaps dune on kill but pre-killing is still safest).

### Task A2 (was uniform-with-search; SUPERSEDED by A5 above)

**Files:** Create `N5Exhaustive/N5Orient.v`.

- [ ] **Step 1:** Define `is_total_b (M:M5) : bool` (every off-diagonal pair comparable) and `has_realizer_b (M:M5) : bool` searching candidate rank pairs (e.g. over `all_perms5` × `all_perms5`, ranking by position) for one whose two induced orders are R2_matrix-monotone, intersect to M, and have a distinguishing pair. Each predicate is a boolean over concrete `Fin.t 5`.
- [ ] **Step 2:** Build `bash .claude/scripts/timed-build.sh 120 posets/dimension/N5Exhaustive/N5Orient.vo 1 20000`; confirm definitions typecheck.
- [ ] **Step 3:** State+prove `n5_orient_exhaustive : forall M, is_poset_b M = true -> is_total_b M = false -> has_realizer_b M = true` by `native_cast_no_check (eq_refl true)` over the `3^10` enumeration (mirror `exhaustive_4edge`; split into chunks if compile > 5 min).
- [ ] **Step 4:** Build (wrapper, generous cap, `jobs=1`); commit `N5Orient.v`.

### Task A3: Reflect `has_realizer_b` to the bridge + wire (uniform path)

**Files:** `N5Orient.v`, `N5DispatcherShapes.v`, delete `EdgeCount{5,6,7,8,9}.v`.

- [ ] **Step 1:** Prove `has_realizer_b M = true -> exists rho1 rho2, <the four bridge hypotheses for M>` (reflect the boolean search to the existential rank pair + decidable properties via `vm_compute`/`reflect`).
- [ ] **Step 2:** Prove `n5_matrix_two_realizable : forall a..e, <distinct> -> Hcov -> is_total_b (R2_matrix R2 a b c d e) = false -> exists r, IsRealizer R2 r /\ cardinal r 2` by combining `R2_matrix_is_poset`, `n5_orient_exhaustive`, Step 1, and `two_realizer_from_fin_ranks`.
- [ ] **Step 2b:** Connect `~ total order on B` to `is_total_b (R2_matrix ...) = false` (via `R2_matrix_false_iff` + an incomparable pair from `Hinc_ex`).
- [ ] **Step 3:** Re-prove `n5_residual_classes_two_realizer` (and/or simplify `n5_nonantichain_nonchain_two_realizer`) to call `n5_matrix_two_realizable` directly; drop the edge-count case split for counts 5–9.
- [ ] **Step 4:** Delete `EdgeCount{5,6,7,8,9}.v` and their imports; rebuild `bash .claude/scripts/timed-build.sh 1800 posets/dimension 2`. Expected: green, admit count 5 → 1.
- [ ] **Step 5:** Commit; update status doc.

### Task A4: Per-count explicit constructions (FALLBACK if A1 says infeasible)

**Files:** `EdgeCount{8,7,6,5}.v` (in that order).

- [ ] For each count K (8 first): in `EdgeCount K.v`, after obtaining `R2_matrix`, `destruct` the comparability of the relevant `f0..f4` pairs (guided by `is_poset_b`/`edge_count_b = K` to prune), and for each concrete shape provide explicit `rho1,rho2` (literal rankings), discharging the bridge via `vm_compute`/`decide`. Build each via the wrapper (`jobs=1`, cap 600 s); commit per file. Admit count drops one per file.

---

## Track B — Trotter coverage

### Task B1: Decompose `trotter_coverage_via_extremality` (Session 4)

**Files:** read `RemovablePairs.v` around 1788–1842 + `CriticalPairDigraph.v`, `CriticalPairs.v`.

- [ ] **Step 1:** Read the lemma + `greedy_acyclic_subset`, `IsExtremalCP`, `aug_step`, and the cycle/critical-pair machinery. Write a Track B plan doc with 2–4 focused sub-lemmas, each a precise `Admitted` statement passing the admit-introduction checklist (true / non-circular / precise / minimal / documented).
- [ ] **Step 2:** Run the `proof-skeptic` agent on the proposed sub-decomposition before committing the admits.
- [ ] **Step 3:** Commit the refactor (broad admit → focused sub-admits + Qed wrapper); update status. Admit count may rise temporarily (progressive refinement).

### Tasks B2–Bn: Close the Trotter sub-lemmas (Sessions 5–N)

- [ ] One focused sub-lemma per session(s): cycle-⇒-refining-CP; extremality-kills-refinement-chains; greedy bookkeeping. Build via wrapper; commit per lemma; `proof-skeptic` at each close. Apply when-to-stop heuristics if 3 sessions pass with no net admit reduction.

---

## Per-session protocol (every session)

- [ ] Open: read status doc; `bash .claude/scripts/timed-build.sh 1800 posets/dimension 2` (or `@check`) green; state "Session X, admit count Z, goal W".
- [ ] Execute the session's tasks; commit per Qed/file.
- [ ] Close: status doc updated with commit hashes + next step; build green; new admits passed the checklist.

## Self-review notes

- Spec coverage: Track A counts 5–8 (A1–A4), Track B admit #2 (B1–Bn), both base-case requirement and inductive-step requirement covered.
- The uniform path (A2/A3) is gated on the A1 probe; A4 is the explicit fallback so no requirement is left without a task.
- Build discipline (wrapper, `jobs=1` for reflection, memory cap) stated per task.

---
name: long-running-formalization
description: Use when starting or continuing multi-session, research-level proof work (Hiraguchi-style, Trotter Ch.6, etc.) — codifies decomposition-first protocol, admit-soundness audits, status-doc discipline, progressive refinement, and when-to-stop heuristics. Triggers: opening a research-grade formalization track, introducing a new Admitted, refactoring an Admitted, switching strategies after 3+ failed attempts, planning multi-session work, session-end checkpoints.
---

# Long-Running Formalization

Research-level Coq proofs (>1 week of work) have distinct failure modes from regular coding. This skill codifies the meta-discipline that survived contact with Track B (Trotter Ch.6) and Track N (n=5 exhaustiveness).

## When this skill applies

Trigger this skill when the work is:
- **Multi-session** (will span >3 working sessions, possibly weeks).
- **Research-grade** (no off-the-shelf Coq formalization exists — already checked via [[searching-existing-formalizations]]).
- **Non-trivial decomposition** (paper proof is multi-page or chapter-length).

If the work is a one-shot bug fix or small lemma, skip this — too much overhead.

## The 5 disciplines

### Discipline 1: Decompose BEFORE writing code

**Rule:** Never start writing a research-level Qed without first writing a decomposition plan.

Before opening any `.v` file, in a plan document, factor the target theorem into:

1. **Mechanical-Qed parts** — boilerplate that any agent can write (signatures, plumbing, type-class dispatch).
2. **Iterable-Qed parts** — per-case lemmas with a clear template; pattern repeats across instances.
3. **Irreducible "deep claim" admits** — the genuine mathematical content that you can't decompose further.

Write each as a named Lemma/Admitted with a precise statement. The plan document IS your contract for the session.

**Why:** This forces you to identify the smallest unprovable nugget upfront. If category 3 is empty, the proof is mechanical. If category 3 is huge, you may need a different approach.

**Worked example (Track B):**
- Mechanical: `IsBoundaryReversalSet` predicate, helper lemmas, dune wiring.
- Iterable: `lift_and_force_with_boundary_is_poset` (one variant per shape).
- Deep: `trotter_per_L_acyclic_covering_family` (genuine Trotter Ch.6 content).

The Trotter track succeeded because we factored before committing code. Subsequent phases progressively shrank category 3.

### Discipline 2: Admit-introduction checklist

**Rule:** Every new `Admitted.` must pass these checks BEFORE commit:

- [ ] **Statement is mathematically true.** Attempt a counter-example for 5+ minutes. If you find one, the admit is false — fix the statement.
- [ ] **Statement is not circularly dependent.** Trace the `apply`/`exact` chain transitively. If the admit is reachable from itself via Qed-via-admit chains, it's unsound.
- [ ] **Statement is precise.** Vague admits ("there exists some function with some property") are escape hatches. Make the type signature exact.
- [ ] **Statement is minimal.** Could the admit be split into a smaller admit + Qed wrapper? If yes, split.
- [ ] **The admit's role is documented.** Comment block above the `Admitted` explains: what claim, what it gives downstream, why it's deep.

**Why:** We introduced a false admit in Phase B4 (`trotter_constant_boundary_acyclic` — counter-example found in Phase B5). The chain `trotter_boundary_coverage → trotter_boundary_existence → trotter_constant_boundary_acyclic` was Qed-via-false-premise, making the whole top-level Hiraguchi chain unsound until B6 fixed it.

Catch this BEFORE commit, not 2 sessions later.

### Discipline 3: Status-doc discipline

**Rule:** Maintain a per-track status doc, updated at session boundaries.

Path: `docs/superpowers/specs/YYYY-MM-DD-<track>-status.md`.

Contents:
- **Current admit count** with file:line and brief statement.
- **Per-session log**: session ID, deliverables, commit hash.
- **Pending sessions**: next concrete step, estimated effort.
- **Strategy choices and rationale**: why this approach over alternatives.
- **Risk register**: known gaps and contingency plans.
- **Useful files**: paths to plan, scripts, references.

**Why:** Multi-session work loses context. The status doc is the handoff artifact. We wrote `2026-05-25-current-state.md` and `2026-05-28-status.md` mid-track because we needed them; treat this as the default, not the emergency action.

### Discipline 4: Progressive refinement, not perfect proofs

**Rule:** Hard admits should iteratively refine, not survive in their original form.

When a deep admit blocks progress:
1. **Don't try to Qed it directly** — that's the multi-week ambush.
2. **Refactor it.** Each refactor should:
   - Replace the broad admit with a more focused one + Qed wrapper.
   - Narrow the hypothesis space (e.g., require `IsExtremalCP` instead of `IsCriticalPair`).
   - Make the remaining admit MORE attackable than before.

Track B's phases B1-B6 are the pattern: each phase narrowed the admit until B7 reduced it to a single coverage claim (`trotter_coverage_via_extremality`). The deep math content didn't change, but the surface area shrank dramatically.

**Anti-pattern:** trying to prove the original monolithic admit in one heroic push. This burns sessions without measurable progress.

### Discipline 5: When-to-stop heuristics

**Rule:** Recognize diminishing returns and switch tactics.

Stop pushing the current approach when:

- **3+ consecutive sessions** in one track end with no net admit-count change.
- **Each agent dispatch yields fewer net new lemmas** than the previous (e.g., 5 → 3 → 1 → 0).
- **The "fix the next case" cycle is now mostly duplicate detection**, not new content.
- **The build/iteration time exceeds productive work time** per session (e.g., 4-hour builds blocking 2-hour work).

When you hit these signals:
- **Don't keep grinding.** Stop. Audit.
- **Re-plan**: is there a fundamentally different approach? (e.g., abandon cascade enumeration for tactic automation, or for a paper-proof-based decomposition).
- **Accept and document**: if the gap is genuinely irreducible, document it precisely and ship the rest.

We saw this with n=5 cascade exhaustiveness: rounds of agent dispatching kept adding micro-cases but the residual admit's call-site count grew (267 → 280) instead of shrinking. Time to stop.

## Track-management for parallel work

If you have >1 independent admits, run them as separate tracks:

- **Each track has its own plan** (`docs/superpowers/plans/YYYY-MM-DD-<track>.md`).
- **Each track has its own status doc** (above).
- **Commit per track**: don't interleave commits from different tracks if avoidable.
- **Use worktrees if conflict risk is high**: see [[superpowers:using-git-worktrees]].

For our session, Track B (Trotter) and Track N (n=5) were genuinely independent — we ran them serially but could have parallelized in separate worktrees.

## Cross-track dependency check

Before commit, verify the Qed chain is sound:

```bash
grep -rn "Admitted\.$" posets/dimension/
```

For each admit, trace its callers:

```bash
grep -rn "<lemma_name>" posets/dimension/ --include='*.v'
```

If admit A is used by Qed B, and B is used (transitively) by admit A's proof — circular, unsound.

We tripped this with Phase D ("use Hiraguchi directly to close n5_residual"): `hiraguchi_bound → ... → n5_residual_classes_two_realizer`, so the closure was circular.

## Session opening protocol

When opening a new session on an existing track:

1. **Read the status doc.** Get the current state.
2. **Read the plan.** Get the intended next session.
3. **Verify build is green** via `mise run check-all` (fast).
4. **State explicitly** in your first message: "Starting session X of plan Y. Current admit count: Z. Goal this session: W."
5. **Execute the session.**
6. **At session-end**: update the status doc + commit.

This is overhead but it's the difference between "8 productive days" and "8 days of re-deriving context."

## Session-closing protocol

When wrapping up a session:

- [ ] All work committed.
- [ ] Build green (`mise build` or `mise run check-all`).
- [ ] Status doc updated (this session's commit hashes recorded).
- [ ] Next session's intended starting point documented.
- [ ] Any new admits introduced have passed the [[Admit-introduction checklist]].

## Anti-patterns

| Anti-pattern | Why it fails | Fix |
|---|---|---|
| "Just one more case" | Cascade explosion; diminishing returns. | Apply When-to-stop heuristics. |
| Heroic single-session monolithic admit closure | Burns sessions without progress markers. | Progressive refinement. |
| Skipping status doc updates | Context loss; next session re-derives state. | Status-doc discipline. |
| Trusting build success without checking .vo timestamps | False positives mask broken commits. | See [[coq-build-doctor]]. |
| Introducing admits without soundness audit | Sound chain becomes unsound silently. | Admit-introduction checklist. |
| One huge plan doc | Hard to navigate, no per-session boundaries. | Session-by-session breakdown (like `2026-05-28-close-final-admits.md`). |

## Quick triggers

| You're about to... | Run this discipline... |
|---|---|
| Start a new research-level track | Decompose-before-code (D1) + Status-doc setup (D3) |
| Introduce an Admitted | Admit-introduction checklist (D2) |
| Refactor an Admitted | Admit-introduction checklist (D2) + Progressive refinement (D4) |
| Spend 3+ sessions on same admit | When-to-stop heuristics (D5) |
| End a session | Session-closing protocol |
| Open a session | Session opening protocol |

## Cross-references

- Pre-formalization search: [[searching-existing-formalizations]]
- Build hygiene: [[coq-fast-compile]], [[coq-build-doctor]]
- Cascade structures: [[coq-cascade-split-pattern]]
- Plan writing: [[superpowers:writing-plans]]
- Branch isolation: [[superpowers:using-git-worktrees]]

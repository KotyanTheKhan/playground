---
name: coq-fast-compile
description: Use when writing or refactoring Coq proofs to keep compilation tractable — each .v file <500 lines, each Qed <5 min, parallel-friendly. Triggers: slow `mise build`, `dune build` stuck, single Qed taking >30 min, file >1000 lines, custom Ltac combinators that construct existential witnesses via tactics
---

# Coq Fast-Compile Discipline

Keep Coq proofs compiling fast by structural choices made BEFORE writing the proof, not after.

## The 6 rules

1. **Each `.v` file ≤ 500 lines.** If it grows past 300, plan a split.
2. **Each `Qed` body ≤ 100 lines.** If it grows past 50, factor into helper Lemmas.
3. **Each individual file compile ≤ 5 min.** Use `mise exec -- dune build <file>.vo` with timeout to measure.
4. **Per-case cascades go in SEPARATE FILES, not separate Lemmas in one file.** Dune compiles files in parallel; Lemmas in one file compile sequentially.
5. **Avoid Ltac combinators that produce large proof terms.** Anti-pattern: tactics that construct existential witnesses or do structured case-splits via a single macro. They produce huge proof terms even on small goals (100x slowdown observed). Use explicit `destruct (classic ...)` + `assumption` chains instead.
6. **Never combine unbounded `eauto` with a cartesian `try`-chain.** `eauto using <transitive_lemma>` does depth-first search with no fuel; multiplied across N×M case combinations inside a nested `destruct ... ; destruct ...`, it can exhaust RAM in EACH parallel `coqc` worker (`dune -j` defaults to NCPU). One bad file can crash the laptop. See "OOM anti-pattern" below.

## Verification protocol

After writing each Qed:
```bash
mise exec -- dune build <path/to/file>.vo
```

**ALWAYS set a timeout** (300 seconds / 5 min). On timeout:
- DO NOT retry the same compile.
- Split the file: extract the largest Lemma into a sibling file.
- Re-verify.

## Common pitfalls

| Pitfall | Symptom | Fix |
|---------|---------|-----|
| Single giant Qed | Compile >30 min | Extract each major case into its own Lemma + file |
| All cases in one file | No parallelism even after Lemma extraction | Move each Lemma to its own .v file |
| Ltac that builds witnesses | 10+ min Qed on small file | Inline the witness construction with explicit `exists` |
| `k^N` destruct nesting (large N) | Memory exhaustion / multi-hour Qed | Use per-structural-case helpers; keep each destruct tree under ~3000 leaves |
| Cartesian `try ... eauto using L` chain | Laptop OOM during `mise build` | See "OOM anti-pattern" — bound search or restructure |
| Single-file `mise run build <file>.v` | Silently no-ops | Use `mise exec -- dune build <file>.vo` instead |

## OOM anti-pattern: untamed `eauto` in cartesian case chains

If you find yourself writing:

```coq
induction Hcyc as [u v Huv | u w v Huw IHuw Hwv IHwv].
- (* base *) ...
- destruct IHuw as [A | [B | [C | [D | [E | F]]]]];
  destruct IHwv as [A | [B | [C | [D | [E | F]]]]];
  try (left; eapply t_trans; eauto);
  try (right; left; split; [eapply t_trans; eauto | assumption]);
  try (right; right; ...; eauto);
  ...
  try assumption.
```

You have built a memory bomb:

- **6 × 6 = 36 goals** from the cartesian destruct.
- **~10 `try` alternatives**, each invoking `eauto using <some_transitive_lemma>`.
- **`eauto` runs depth-first with no fuel cap** — it tries every transitivity composition it can build out of every hypothesis in scope, in every goal.
- **`dune` runs `-j NCPU` by default**, so this is happening in N parallel `coqc` workers, each with its own multi-GB heap.

Result: laptop OOMs, `coqc` workers get OOM-killed silently, `dune` reports cryptic errors or hangs.

### Fixes (in order of preference)

1. **Replace `eauto` with explicit term application.** If you know the proof, write `apply t_trans with (y := w); [exact ... | exact ...]` instead of `eapply t_trans; eauto`.
2. **Bound `eauto` depth.** `eauto 2 using L` or `eauto 3 using L` caps the search. Default depth is 5 and explodes fast.
3. **Cap goal count by changing the existential shape.** A 6-disjunct IH × 6-disjunct IH = 36 cases is the smell. Prove a STRONGER intermediate lemma whose statement is a SHORTER disjunction (2-3 cases), then destruct it.
4. **Use `clos_refl_trans` instead of multi-disjunct shapes.** The cleaner reformulation: state the IH as `clos_trans step3 u v ∨ (clos_refl_trans step3 u q ∧ clos_refl_trans step3 p v)` — 2 disjuncts, 4 cases instead of 36, each with explicit `rt_trans`. (This is exactly how `aug_cycle_implies_step3_path` ended up after the OOM incident on 2026-05-28.)
5. **Move the case-cascade to its own file** so it compiles alone, isolating the memory pressure.

### Bound concurrency when you must compile a suspect file

If you're forced to run a build that may include a memory-heavy file, cap dune parallelism:

```bash
mise exec -- dune build -j 2 <path>
```

This trades wall-clock for survival.

## Anti-pattern detection in code review

When reviewing or writing Coq, flag these for refactor:
- File line count > 500 → propose split.
- A single `Lemma` with `Proof. ... Qed.` body > 100 lines → propose helper extraction.
- Use of any tactic named `*_witness`, `*_close_*`, `*_split_*` if recently introduced → check it doesn't blow up.
- Nested `destruct (classic ...)` deeper than 5 levels → flatten via auxiliary lemma.
- `try ( ... eauto ... ); try ( ... eauto ... ); ...` inside a cartesian `destruct ... ; destruct ...` → memory bomb (see "OOM anti-pattern"). Refuse to commit until restructured.

## Quick reference

- **vos build** (`mise run check-all` or `mise exec -- dune build @check`): fast, type-checks only, skips Qed. Use for structure validation.
- **vo build** (`mise exec -- dune build <file>.vo`): full, verifies Qed. Use for correctness validation. Set timeout.
- **Full project**: `mise build`. Use sparingly; only after structural changes settle.

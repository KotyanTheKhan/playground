---
name: coq-fast-compile
description: Use when writing or refactoring Coq proofs to keep compilation tractable — each .v file <500 lines, each Qed <5 min, parallel-friendly. Triggers: slow `mise build`, `dune build` stuck, single Qed taking >30 min, file >1000 lines, you see `n5_split_witness` or similar Ltac combinators
---

# Coq Fast-Compile Discipline

Keep Coq proofs compiling fast by structural choices made BEFORE writing the proof, not after.

## The 5 rules

1. **Each `.v` file ≤ 500 lines.** If it grows past 300, plan a split.
2. **Each `Qed` body ≤ 100 lines.** If it grows past 50, factor into helper Lemmas.
3. **Each individual file compile ≤ 5 min.** Use `opam exec -- dune build <file>.vo` with timeout to measure.
4. **Per-case cascades go in SEPARATE FILES, not separate Lemmas in one file.** Dune compiles files in parallel; Lemmas in one file compile sequentially.
5. **Avoid Ltac combinators that produce large proof terms.** Specific anti-patterns: `n5_split_witness`, `n5_close_forall_via`, anything that constructs an `exists` witness via tactics. These caused 100x slowdowns. Use explicit `destruct (classic ...)` + `assumption` chains instead.

## Verification protocol

After writing each Qed:
```bash
opam exec -- dune build posets/dimension/<file>.vo
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
| `5^N` destruct nesting | Memory exhaustion at large N | Use per-structural-case closure helpers, each `5^3` to `5^5` max |
| Single-file `mise run build <file>.v` | Silently no-ops | Use `opam exec -- dune build <file>.vo` instead |

## Anti-pattern detection in code review

When reviewing or writing Coq, flag these for refactor:
- File line count > 500 → propose split.
- A single `Lemma` with `Proof. ... Qed.` body > 100 lines → propose helper extraction.
- Use of any tactic named `*_witness`, `*_close_*`, `*_split_*` if recently introduced → check it doesn't blow up.
- Nested `destruct (classic ...)` deeper than 5 levels → flatten via auxiliary lemma.

## Quick reference

- **vos build** (`dune build @check`): fast, type-checks only, skips Qed. Use for structure validation.
- **vo build** (`dune build <file>.vo`): full, verifies Qed. Use for correctness validation. Set timeout.
- **Full project**: `mise build`. Use sparingly; only after structural changes settle.

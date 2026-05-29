---
name: coq-cascade-split-pattern
description: Use when a single Coq Lemma has a giant case-cascade (deeply nested `destruct (classic ...)` blocks) producing a slow Qed — split each branch into its own Lemma in its own file. Triggers: dispatcher patterns, "for each iso class do X", per-case proof obligations
---

# Coq Cascade Split Pattern

When one `Qed` contains many parallel cases (e.g., a dispatcher across many shapes / classes / configurations), split each branch into its own Lemma in its own .v file. The top-level Lemma becomes a thin dispatcher.

## When to apply

Apply this pattern when ALL of:
- One `Lemma` has > 5 parallel branches (`destruct (classic ...)` or similar).
- Each branch is non-trivial (> 50 lines of proof).
- The total Qed takes > 30 min to compile.

## The 4-step pattern

### Step 1: Identify branch boundaries

In the source Lemma, find each `destruct (classic (P_i)) as [Hi | HnotI].` Each case `Hi` is a branch.

### Step 2: Extract each branch to a sibling file

Create `<ParentName>_<branchID>.v` with:
```coq
(* Imports — mirror what the parent file uses *)
From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
(* ... project-specific imports ... *)

Lemma <parent_name>_<branchID> :
  forall <type/instance parameters>
    (* ALL hypotheses the branch's proof body uses *)
    (<hypothesis bundle>)
    (HX : <branch's positive hypothesis>),
  <same conclusion as parent>.
Proof.
  intros ... HX.
  (* paste the branch's proof body verbatim *)
Qed.
```

Hypothesis bundle gotchas:
- Include ALL upstream negation hypotheses the body references (cases the outer dispatcher already ruled out).
- Include carrier-cover / membership hypotheses if the body destructs over a fixed set of elements.
- Include any flag-exclusion hypotheses (`H : ~ (x = p /\ y = q)` style) that the body uses.

### Step 3: Replace the parent's branch with `apply`

In the parent file, replace:
```coq
destruct (classic (P_i)) as [Hi | HnotI].
- (* 800-line body *)
  ...
- (* next branch *)
```

with:
```coq
destruct (classic (P_i)) as [Hi | HnotI].
- apply (@<parent_name>_<branchID> <explicit parameters> <hypothesis args> Hi).
- (* next branch *)
```

Use the explicit `@` form so Coq doesn't try to infer arguments via typeclass resolution — that can pick up the wrong instance and produce confusing errors.

### Step 4: Verify and commit per extraction

After each extraction (always via the timed wrapper — never bare dune):
```bash
bash .claude/scripts/timed-build.sh 300 <path/to/file>.vo 2
```

If it compiles, commit immediately. Don't batch multiple extractions before commit — easier to bisect failures.

## Critical: separate FILES, not just separate Lemmas

If you extract Lemmas but leave them all in the parent file, the speedup is small because Coq compiles a file sequentially through all its Qeds.

For real parallelism, each extracted Lemma needs its own .v file. Then `dune` compiles them concurrently across CPU cores.

**Rule of thumb:** the per-file compile time of the slowest Lemma sets the wall-clock floor. Splitting one giant file with N Lemmas into N files of one Lemma each turns a sequential sum into a parallel max.

## Sub-pattern: nested cascades

For deeply nested cascades (case → sub-case → sub-sub-case):
- Extract at the OUTERMOST level first.
- If extracted file is still slow (>5 min), recursively apply: split it at its outermost level.
- Stop when each file compiles in <5 min.

## awk/sed relabel for mechanical adaptation

When extracting a branch that's the mirror of an already-extracted branch (e.g., one identifier swap distinguishes them), use `awk`/`sed` with a 3-step swap pattern to avoid clobbering identifiers mid-replace:

```awk
# Example: swap identifier tokens `x` and `y` throughout a body
{
  gsub(/\<token_x\>/, "TMP_SWAP_PLACEHOLDER");
  gsub(/\<token_y\>/, "token_x");
  gsub(/TMP_SWAP_PLACEHOLDER/, "token_y");
  print
}
```

Pitfalls:
- Don't normalize compound names alphabetically (different identifiers may have different types).
- Watch for direction-sensitive tactic patterns flipping under the swap: `intro Hxy_eq; apply Hxy_neq; symmetry; exact Hxy_eq` may need the `symmetry;` removed (or added) after the swap depending on alphabetical ordering of identifiers.
- After any awk pass, re-run the compile to catch type/direction errors. Fix manually.

## Verification anti-pattern

Do NOT use `mise run build <file>.v` to verify — it silently no-ops on the .v target.

Use the timed wrapper targeting the `.vo`:
`bash .claude/scripts/timed-build.sh 300 <file>.vo 2`. It enforces the timeout
and a memory cap; never call bare `dune`/`mise build` (no limits → OOM risk).

## Worked-example shape

A dispatcher Lemma covering N parallel shape classes, each with M sub-cases:

1. Top-level extraction: lift each of the N shape branches into its own file. The parent file shrinks to a thin dispatcher.
2. If any extracted file is still slow (>5 min compile): apply the pattern recursively, splitting on the M sub-cases.
3. Stop when every file compiles in <5 min.

The number of recursion levels depends on the cascade's depth, but typically 2 levels suffice for dispatcher Lemmas with up to ~300 leaves.

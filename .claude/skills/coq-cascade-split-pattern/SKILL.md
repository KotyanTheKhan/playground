---
name: coq-cascade-split-pattern
description: Use when a single Coq Lemma has a giant case-cascade (deeply nested `destruct (classic ...)` blocks) producing a slow Qed — split each branch into its own Lemma in its own file. Triggers: dispatcher patterns, "for each iso class do X", per-case proof obligations
---

# Coq Cascade Split Pattern

When one `Qed` contains many parallel cases (e.g., 18 isomorphism class branches), split each branch into its own Lemma in its own .v file. The top-level Lemma becomes a thin dispatcher.

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
From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
(* import whatever the parent imports *)
From Dimension Require Import ... .

Lemma <parent_name>_<branchID> :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (* ALL hypotheses the branch's proof body uses *)
    (Hcard : cardinal B (Full_set B) N)
    (...) (* full hypothesis bundle *)
    (HX : <branch's positive hypothesis>),
  <same conclusion as parent>.
Proof.
  intros ... HX.
  (* paste the branch's proof body verbatim *)
Qed.
```

Hypothesis bundle gotchas:
- Include ALL upstream `Hn<class>` negation hypotheses the body uses.
- Include `Hcov5` (or analog) if body destructs over the carrier.
- Include `Hnot_pq` (or analog) flag exclusions if relevant.

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
- apply (@<parent_name>_<branchID> B R2 HR2 Hcard ... Hi).
- (* next branch *)
```

### Step 4: Verify and commit per extraction

After each extraction:
```bash
opam exec -- dune build posets/dimension/<file>.vo  # timeout 300s
```

If it compiles, commit immediately. Don't batch multiple extractions before commit — easier to bisect failures.

## Critical: separate FILES, not just separate Lemmas

If you extract Lemmas but leave them all in the parent file, the speedup is small because Coq compiles a file sequentially through all its Qeds.

For real parallelism, each extracted Lemma needs its own .v file. Then `dune` compiles them concurrently across CPU cores.

**Observed:** parent file with 19 Lemmas in one file → 4+ hour compile. Same 19 Lemmas in 19 files → ~15 min parallel.

## Sub-pattern: nested cascades

For deeply nested cascades (case → sub-case → sub-sub-case):
- Extract at the OUTERMOST level first.
- If extracted file is still slow (>5 min), recursively apply: split it at its outermost level.
- Stop when each file compiles in <5 min.

## awk relabel script for mechanical adaptation

When extracting a similar branch from a "mirror" structure (e.g., `(r, s)` case → `(s, r)` case via r↔s swap):

```awk
# /tmp/relabel_rs.awk — swaps r and s in token contexts
{
  gsub(/\<Hrs_neq\>/, "TMP_SWAP_HRS");
  gsub(/\<Hsr_neq\>/, "Hrs_neq");
  gsub(/TMP_SWAP_HRS/, "Hsr_neq");
  # repeat for other r/s tokens (HRrs, HRsr, etc.)
  print
}
```

Pitfalls:
- Don't normalize `_eq` names alphabetically (different types).
- Watch for `symmetry;` pattern flipping: `intro Hxy_eq; apply Hxy_neq; symmetry; exact Hxy_eq` may need to become `intro Hxy_eq; apply Hxy_neq; exact Hxy_eq` (no `symmetry`) after swap if the swap reverses alphabetical ordering of identifiers.

## Verification anti-pattern

Do NOT use `mise run build <file>.v` to verify — it silently no-ops on the .v target.

Use `opam exec -- dune build <file>.vo` instead, with explicit timeout.

## Worked example

Source: `N5Dispatcher.v` at 19,245 lines, one Qed, 4+ hour compile.

Result after applying this pattern:
- 19 sibling files (`N5Dispatcher_i.v` through `N5Dispatcher_xix.v`) each 900-2000 lines.
- Top-level dispatcher now 2,111 lines.
- Full `mise build` (parallel): completes successfully.

Then secondary split on the largest sub-files (3-way split at 3rd-edge case boundaries) brought individual files to <500 lines each.

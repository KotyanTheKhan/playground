---
name: coq-build-doctor
description: Use when Coq builds are stuck, broken, silently failing, or you can't tell if a change actually compiled — recovery playbook for stuck dune processes, locked `_build`, false-positive single-file builds, and bisecting build breaks. Triggers: `dune build` running for hours, `mise build` reports success but .vo missing, stuck rocqworker, `_build/.lock` held, "previously bound" warnings flooding output
---

# Coq Build Doctor

Recovery playbook for stuck or misleading Coq builds.

## Symptom → diagnostic flowchart

```dot
digraph diag {
    "Build seems stuck" [shape=diamond];
    "ps aux for rocqworker/dune" [shape=box];
    "Kill stuck workers + clear lock" [shape=box];
    "mise build reports success" [shape=diamond];
    "Check .vo timestamps" [shape=box];
    "Old timestamps?" [shape=diamond];
    "Cache lied — force rebuild" [shape=box];
    "Fresh timestamps OK" [shape=box];
    "Files all compiled?" [shape=diamond];
    "Compile errors hidden by warnings" [shape=box];
    "All good" [shape=box];

    "Build seems stuck" -> "ps aux for rocqworker/dune";
    "ps aux for rocqworker/dune" -> "Kill stuck workers + clear lock";
    "mise build reports success" -> "Check .vo timestamps";
    "Check .vo timestamps" -> "Old timestamps?";
    "Old timestamps?" -> "Cache lied — force rebuild" [label="yes"];
    "Old timestamps?" -> "Files all compiled?" [label="no"];
    "Files all compiled?" -> "Compile errors hidden by warnings" [label="no"];
    "Files all compiled?" -> "All good" [label="yes"];
}
```

## Common failure modes

### Mode 1: Stuck rocqworker (build runs forever)

**Diagnose:**
```bash
ps -ef | grep rocqworker | grep -v grep | awk '{print $2, "ETIME:", $5, $6, "CPU:", $7, $NF}'
```

If a worker has been running >30 min on a single file at 99% CPU:

**Fix:**
```bash
ps -ef | grep -E "rocqworker|dune" | grep -v grep | awk '{print $2}' | xargs -I{} kill -9 {}
rm -f _build/.lock
```

Then either fix the slow file (use `coq-cascade-split-pattern`) or commit and proceed.

### Mode 2: Silent build skip

`mise run build <file>.v` returns success without doing anything because dune sees the .v target as "not a build target."

**Diagnose:**
- After running `mise run build`, check `_build/default/posets/dimension/<file>.vo` timestamp.
- If unchanged from before the run, the build didn't happen.

**Fix:** Use `opam exec -- dune build <file>.vo` instead. This is the correct invocation.

### Mode 3: Stale cache claims success

`mise build` exits 0 because all .vo files are up-to-date in cache, but the cache reflects an OLD version of a .v file.

**Diagnose:**
- After modifying a .v file, check its mtime is newer than its .vo.
- `ls -la <file>.v _build/default/<file>.vo` and compare.

**Fix:** 
```bash
touch posets/dimension/<file>.v  # force re-compile
mise build
```

Or for a hard reset:
```bash
mise run clean
mise build  # full rebuild
```

### Mode 4: Lock file held by dead process

Symptom: `dune build` exits silently or hangs at startup.

**Diagnose:**
```bash
ls -la _build/.lock
# if file exists but no process owns it
```

**Fix:**
```bash
rm -f _build/.lock
```

### Mode 5: Hidden compile error behind warnings

The "previously bound to ... remapped to ..." warnings flood the output and hide a real error 10 lines down.

**Diagnose:**
```bash
mise build 2>&1 | grep -E "^Error|^File.*[Ee]rror"
```

**Fix:** Address the error in the named file. Common ones:
- "The variable X was not found in the current environment" → identifier typo or scope leak.
- "Hypothesis X expected" → missing apply argument.
- "Could not unify ... with ..." → goal mismatch.

## Bisecting a broken build

When the latest commit doesn't build but you don't know which earlier commit broke it:

```bash
# Save current state
git stash

# Find a known-green commit
git log --oneline | head -20

# Test each:
for commit in <suspect commits>; do
  git checkout $commit
  opam exec -- dune build @check  # FAST vos build (no Qed verification)
  echo "Commit $commit: exit $?"
done

# Restore
git checkout dimension_finish
git stash pop
```

`dune build @check` uses .vos (type-check only, no Qed). Completes in 1-2 min for the full project. Use this to bisect.

## Verification protocol

After ANY commit that should preserve a green build:

1. `mise build` (or `mise run check-all` for fast version).
2. Wait for completion (set timeout — 1 hour max for full project).
3. Check exit code AND verify .vo files were actually produced/refreshed.
4. If any concern, examine `_build/log` for warnings/errors.

## When to give up and revert

If 3 consecutive recovery attempts fail:
1. `git stash`.
2. `git reset --hard <last-known-green-commit>`.
3. `mise run clean`.
4. `mise build` to confirm restoration.
5. Replan the change.

Better to lose recent work than to push broken code forward.

## Useful commands cheatsheet

| Command | Purpose |
|---------|---------|
| `mise build` | Full project Qed-verified build |
| `mise run check-all` | Fast vos build (type-check only) |
| `mise run clean` | Clear `_build/` cache |
| `opam exec -- dune build <file>.vo` | Single-file Qed-verified build |
| `opam exec -- dune build @check` | Fast vos for all files |
| `rm -f _build/.lock` | Clear stuck lock |
| `ps -ef | grep rocqworker` | Find Coq workers |

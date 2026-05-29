---
name: coq-mise-build
description: Use when building or rebuilding any part of this playground Coq project, when `mise build` / `mise run …` fails, when adding or upgrading opam packages, when bumping the Coq/OCaml/dune versions, or when onboarding a fresh checkout. Also use when you see errors mentioning `coqc`, `dune`, `opam`, `Stdlib`, `ZornsLemma`, theory not found, "Cannot find a physical path", or a missing switch.
---

# coq-mise-build

## Overview

This project is built **only through `mise`**. Mise pins OCaml + opam, owns the
opam switch lifecycle, and runs every `dune` / `opam` / `coqc` invocation
inside the local `./_opam` switch. There is exactly one source of truth for
tool versions — `mise.toml` — and exactly one path for adding deps.

**Iron rule:** never invoke `dune`, `opam`, or `coqc` directly. If you find
yourself wanting to, you are bypassing the pinned environment and the build
will be unreproducible for the next session.

```
mise.toml ──► [env]/[tools] pins ──► mise run install-deps ──► ./_opam (local switch) ──► dune build
```

**Second iron rule — every COMPILATION goes through the timed wrapper.**
A bare `mise build` / `mise run build …` has no wall-clock cap and no memory
cap, and dune's default `-j = ncpu` runs one rocqworker per core. Across
memory-heavy proofs that fan-out has OOM-crashed the machine more than once.
So any command that actually compiles `.v` files must run as:

```
bash .claude/scripts/timed-build.sh <seconds> <target> [jobs] [mem_mb]
```

- `<seconds>` hard timeout (build killed if exceeded; exit 124),
- `<target>` a `path/File.vo`, a submodule dir, or `@all`,
- `[jobs]` dune `-j` (default 2; `1` for memory-heavy cascades),
- `[mem_mb]` kill if worker RSS exceeds this (default 20000 ≈ 20 GB; exit 137).

Non-compiling tasks (`setup`, `install-deps`, `versions`, `reinstall`,
`nuke-switch`, `env`, `coqtop`, `clean`) have no memory/timeout risk and may be
run directly as `mise run <task>`.

## Quick reference

Builds (anything that compiles `.v`) go through the wrapper; let `TB` stand for
`bash .claude/scripts/timed-build.sh`:

| Goal | Command |
|------|---------|
| Fresh clone, first build | `mise run setup && TB 1800 @all 4` |
| Build everything | `TB 1800 @all 4` |
| Build one library | `TB 600 posets 4` (or `list` / `tree` / `happenedBefore` / `eventualConsistency` / `standard_example` / `abhishek` / `chipala_book` / `vendor/ZornsLemma`) |
| Build an arbitrary path | `TB 300 posets/dimension 2` |
| Build a single file | `TB 120 posets/dimension/.../File.vo 2` |
| Build a memory-heavy cascade file | `TB 600 posets/dimension/.../Heavy.vo 1` |
| Quick check (proofs only) | `TB 1800 @check 4` |
| Clean build artifacts | `mise run clean` (no compile) |
| Confirm pinned versions | `mise run versions` (no compile) |
| Re-install pinned deps | `mise run reinstall` (no compile) |
| Nuke + rebuild the switch | `mise run nuke-switch` (slow, ~10–20 min) |
| Print opam env | `mise run env` |
| Coq REPL in pinned switch | `mise run coqtop` |

Pick `<seconds>` from the expected cost (single light file ~120s, heavy
cascade ~600s, whole project ~1800s) and `[jobs]` from memory weight (2 by
default, 1 for cascade-heavy files, up to ~4 for many small light files —
never the full ncpu across heavy files). If the user asks "build the project"
or "rebuild X", reach for this table — do not improvise a bare `mise build`.

Watch mode (`mise run watch`) is unsupported under the wrapper (it never
exits); avoid it for agent-driven builds.

## Tool / version model

Every pin lives in `mise.toml`:

* `[tools]` — `opam`, `ocaml` (managed by mise itself)
* `[env]` — every opam package version as `COQ_VERSION`, `COQ_HAMMER_VERSION`, etc.
* `[tasks.install-deps]` — the one place that installs opam packages,
  references those `[env]` vars by name.

**To bump a version:** edit the corresponding env var in `mise.toml`, then
`mise run reinstall`. Never `opam install x.y.z` directly — the pin
becomes invisible to fresh clones.

**To add a new opam package:**
1. Add `FOO_VERSION = "x.y.z"` to `[env]` in `mise.toml`.
2. Add `"foo.${FOO_VERSION}"` to the `opam install -y \ …` list in `tasks.install-deps`.
3. Add `(foo (>= "x.y.z"))` to `(depends …)` in `dune-project` if the
   package needs to appear in the generated `playground.opam`.
4. Run `mise run reinstall`.

**To bump Coq major version:** update `COQ_VERSION`, `COQ_STDLIB_VERSION`,
`ROCQ_RUNTIME_VERSION`, `ROCQ_STDLIB_VERSION`, `COQ_HAMMER_VERSION`
together — they must all stay compatible. Then `mise run nuke-switch`
(rebuilding the OCaml/Coq world is faster than reconciling a partial upgrade).

## Vendored libraries

`coq-zorns-lemma` is **vendored** under `vendor/ZornsLemma/`. Upstream
(`coq-community/topology`) pins `coq < 8.21`; no `rocq-zorns-lemma`
package exists. We run Coq 9.x, so the released opam package cannot be
installed. The vendored copy is the source of truth.

* The `.v` files were ported `From Coq` → `From Stdlib` for Coq 9.x.
* `vendor/ZornsLemma/dune` declares `(coq.theory (name ZornsLemma) (theories Stdlib))`.
* `_CoqProject` maps `-R vendor/ZornsLemma ZornsLemma`.
* Project code keeps importing `From ZornsLemma Require Import …` — the
  namespace is identical to the opam package's.

**If you bump Coq:** rebuild the vendor with `mise run build-zornslemma`
first; any new deprecation warnings appear there before they hit project code.

**If upstream ever ships a `rocq-zorns-lemma`:** delete `vendor/ZornsLemma/`,
re-add `coq-zorns-lemma` (or its new name) to `install-deps`, restore the
`(theories … ZornsLemma)` reference unchanged, and remove the
`-R vendor/ZornsLemma ZornsLemma` line from `_CoqProject`.

## Failure cookbook

### `Theory "Stdlib" has not been found`
Switch is on Coq 8.x. Run `mise run versions` — if `coqc` is `< 9.0`,
either bump pins (see "bump Coq major version" above) or rewrite the
offending dune file to drop the explicit `(theories Stdlib …)` (legacy
8.20 behavior). Don't drop `Stdlib` while on 9.x — it's an explicit
dependency now.

### `Cannot find a physical path bound to logical path X with prefix Stdlib`
The current dune theory is missing `(theories Stdlib)` (or `Stdlib`
isn't installed). Check the file's `dune`:
```
(coq.theory
 (name Foo)
 (theories Stdlib …))   ; ← this line is mandatory in Coq 9.x
```
If `Stdlib` is listed and the error persists, `mise run reinstall` —
`rocq-stdlib` may have been removed.

### `Theory "ZornsLemma" has not been found`
Either `_CoqProject` lost its `-R vendor/ZornsLemma ZornsLemma` line, or
the dune file consuming it is missing `(theories … ZornsLemma)`, or
`vendor/ZornsLemma` itself failed to build (run `mise run build-zornslemma`
to see the underlying error).

### `Multiple rules generated for X.glob`
There are pre-built `.vo`/`.glob`/`.vos`/`.vok`/`.aux` files alongside
the sources (commonly in `vendor/`). Dune treats them as both source and
output. Delete them: `find vendor -name '*.vo*' -o -name '*.glob' -o -name '.*.aux' | xargs rm -f`,
then rebuild.

### `Switch "./" not found` / `[ERROR] No package matching coq.X.Y.Z found`
Fresh checkout or broken switch. `mise run setup`. If you already have a
switch but it's wedged, `mise run nuke-switch`.

### `Warning: "From Coq" has been replaced by "From Stdlib"`
Cosmetic in 9.x but indicates a pending source migration. The compat
shim still works; not a build failure.

## Anti-patterns

* `mise build` / `mise run build foo` **without the wrapper** — no timeout, no
  memory cap, default `-j = ncpu`. Has OOM-crashed the machine. Always go
  through `bash .claude/scripts/timed-build.sh <secs> <target> [jobs] [mem_mb]`.
* `dune build foo` — bypasses the pinned switch *and* the wrapper. Use the wrapper.
* `opam install bar` — invisible to fresh clones. Add to `mise.toml`.
* `coqc -R …` for ad-hoc checks — won't see project's `_CoqProject`
  mappings, dune wrappers, or theory deps. Use `mise run coqtop` or
  `mise build <path>`.
* Editing `playground.opam` by hand — `(generate_opam_files true)` in
  `dune-project` regenerates it. Edit `dune-project`'s `(depends …)` instead.
* `eval $(opam env)` without `--switch=. --set-switch` — picks up the
  global switch, not the local one. Mise tasks already do this correctly.
* Bumping just one of `COQ_VERSION` / `ROCQ_RUNTIME_VERSION` / `COQ_STDLIB_VERSION` —
  the opam solver will fight you. Bump them together.

## Reproducibility check

Before committing any `mise.toml` / `dune-project` / `_CoqProject` change:

1. `mise run nuke-switch` (proves the switch can be built from scratch),
2. `bash .claude/scripts/timed-build.sh 1800 @all 4` (proves all `.v` files
   compile end-to-end, under the timeout + memory cap),
3. `mise run versions` (sanity-check that the pins resolved to what you intended).

If step 1 fails, the env is not actually reproducible no matter what step 2 says.

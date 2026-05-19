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

## Quick reference

| Goal | Command |
|------|---------|
| Fresh clone, first build | `mise run setup && mise build` |
| Build everything | `mise build` |
| Build one library | `mise run build-posets` / `build-list` / `build-tree` / `build-happenedbefore` / `build-eventualconsistency` / `build-standard-example` / `build-abhishek` / `build-chipala-book` / `build-zornslemma` |
| Build an arbitrary path | `mise run build posets/dimension` |
| Quick check (proofs only) | `mise run check-all` |
| Watch mode | `mise run watch` |
| Clean build artifacts | `mise run clean` |
| Confirm pinned versions | `mise run versions` |
| Re-install pinned deps | `mise run reinstall` |
| Nuke + rebuild the switch | `mise run nuke-switch` (slow, ~10–20 min) |
| Print opam env | `mise run env` |
| Coq REPL in pinned switch | `mise run coqtop` |

If the user asks "build the project" or "rebuild X", reach for the table
above — do not improvise.

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

* `dune build foo` — bypasses the pinned switch. Use `mise run build foo`.
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
2. `mise build` (proves all `.v` files compile end-to-end),
3. `mise run versions` (sanity-check that the pins resolved to what you intended).

If step 1 fails, the env is not actually reproducible no matter what step 2 says.

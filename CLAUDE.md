# CLAUDE.md

## Git

Do not add `Co-Authored-By` or any other AI watermarks to commit messages.

## Build commands

**Every build goes through the wrapper.** Never call `dune`/`mise build`/`coqc`
directly — they have no timeout and no memory cap, and the default `dune -j =
ncpu` fan-out across memory-heavy proofs has crashed the machine (OOM) more than
once. Use:

```
bash .claude/scripts/timed-build.sh <seconds> <target> [jobs] [mem_mb]
```

- `<seconds>` — hard wall-clock cap; the build is killed if exceeded. Always
  pass a real value (single files >300s must be justified — see the
  `coq-fast-compile` skill).
- `<target>` — a `path/to/File.vo` (single file), a submodule dir (e.g.
  `posets`, `list`), or `@all` (entire project).
- `[jobs]` — dune `-j` parallelism. **Default 2.** Use `1` for memory-heavy
  cascade files; raise only for many small light files.
- `[mem_mb]` — kill the build if total worker RSS exceeds this (default 20000 ≈
  20 GB; leaves headroom on a 32 GB machine).

Exit codes: `0` success, `124` timeout, `137` memory-limit kill, other = build
failure. Examples:

```
bash .claude/scripts/timed-build.sh 120 posets/dimension/.../File.vo      # single file, -j2
bash .claude/scripts/timed-build.sh 600 posets/dimension/.../Heavy.vo 1   # heavy cascade, -j1
bash .claude/scripts/timed-build.sh 1800 @all 4                           # whole project, -j4
```

For non-build opam/dune needs, still go through `mise exec -- opam …`.
`mise run clean` is fine (no compilation, no memory risk).

Run a whole-project build through the wrapper before committing to catch
cross-module import errors.

## Project layout

| Directory | Contents |
|-----------|----------|
| `posets/` | `IsPoset` / lattice typeclasses, `meet_le` order, `IsFinitePoset`, `nat` instances, Dilworth theorem + corollaries, dimension theory |
| `list/` | List poset and distributive lattice instances (lexicographic order) |
| `tree/` | Tree poset and distributive lattice instances |
| `happenedBefore/` | Happened-before causal order; impossibility of semilattice structure |
| `eventualConsistency/` | Eventual consistency models and convergence proof |
| `standard_example/` | S(n,k) poset proofs |
| `abhishek/` | Alternate Dilworth proof, Hall's theorem, Erdős–Szekeres |

Each directory is a separate logical library (mapped with `-R` in `_CoqProject`).

For an index of all classes, instances, and theorems see **[docs/INDEX.md](docs/INDEX.md)** — keep it up to date when adding or moving definitions.

## Hints

- **Decompose proofs into small lemmas.** A focused lemma with a descriptive name is easier to reuse and debug than an inline block. If a sub-goal recurs across cases, extract it.
- **Search existing libraries before proving.** `Search`, `SearchAbout`, and `Check` can surface lemmas in Stdlib (`Nat.min_assoc`, `Extensionality_Ensembles`, etc.) and in MathComp. Use the `rocq_query` MCP tool (from `rocq-mcp`, configured in `.mcp.json`) to run `Search` and `Check` against the live Coq environment including MathComp — faster than grepping source files.
- **Use `lia` for linear arithmetic** and `hauto lq:on` (Hammer) for goals that follow from a small set of boolean hypotheses without much structure.
- **`rewrite X at 1`** requires setoid. Use `transitivity` to split goals instead.
- **Typeclass resolution from bundled classes**: if `IsFinitePoset` wraps `IsPoset` but inference doesn't find it, add `#[local] Existing Instance fp_is_poset.` inside the section.
- **`repeat first [...]` order matters**: put the most specific branch first to avoid greedy choices into dead ends.

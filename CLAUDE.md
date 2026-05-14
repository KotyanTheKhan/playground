# CLAUDE.md

## Git

Do not add `Co-Authored-By` or any other AI watermarks to commit messages.

## Build commands

Always use `mise` — never invoke `dune`, `opam`, or `coqc` directly. If you must call them, use `mise exec -- dune …` / `mise exec -- opam …`.

- `mise build` — entire project
- `mise run build <dir>/` — single submodule (e.g. `posets/`, `list/`)
- `mise run build <file>.v` — single file
- `mise run clean`

Run `mise build` (no target) before committing to catch cross-module import errors.

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

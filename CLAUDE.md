# CLAUDE.md

## Build commands

Always use `mise` tasks — never invoke `dune` or `opam` directly.

`mise run build [TARGET]` accepts any dune target — a directory, a `.v` file, or nothing for everything:

```bash
mise build                                          # build entire project
mise run build posets/                              # build posets/ subtree
mise run build list/                                # build list/ subtree
mise run build happenedBefore/                      # build happenedBefore/ subtree
mise run build posets/dilworth/DilworthCorollaries.v  # build one file
mise run clean                                      # clean build artifacts
```

Use a scoped target (e.g. `mise run build posets/`) for fast feedback while working in one module. Run `mise build` (no target) before committing to catch import errors in other modules.

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
- **Search Stdlib before proving.** `Search`, `SearchAbout`, and `Check` can surface existing lemmas — `Nat.min_assoc`, `Nat.max_comm`, `Extensionality_Ensembles`, etc. Check `Stdlib.Sets`, `Stdlib.Arith`, and `Stdlib.Logic` before writing a lemma from scratch.
- **Use `lia` for linear arithmetic** and `hauto lq:on` (Hammer) for goals that follow from a small set of boolean hypotheses without much structure.
- **`rewrite X at 1`** requires setoid. Use `transitivity` to split goals instead.
- **Typeclass resolution from bundled classes**: if `IsFinitePoset` wraps `IsPoset` but inference doesn't find it, add `#[local] Existing Instance fp_is_poset.` inside the section.
- **`repeat first [...]` order matters**: put the most specific branch first to avoid greedy choices into dead ends.

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

## Import conventions

- Files in `posets/` import as `From Posets Require Import PosetClasses.`
- Files in `list/`, `tree/`, etc. import as `Require Import Posets.PosetClasses.`
- If a file uses any lattice class (`IsMeetSemilattice`, `IsJoinSemilattice`, `IsLattice`, `IsDistributiveLattice`) it must import **both**:
  ```coq
  Require Import Posets.PosetClasses.
  Require Import Posets.LatticeClasses.
  ```

## Common Coq pitfalls in this codebase

- **`rewrite X at 1`** requires setoid. Use `transitivity` to split goals instead.
- **Typeclass resolution from bundled classes**: if `IsFinitePoset` wraps `IsPoset` but inference doesn't find it, add `#[local] Existing Instance fp_is_poset.` inside the section.
- **`repeat first [apply Union_introl | apply Union_intror | apply In_singleton]`**: put the most specific branch first to avoid greedy left choices into dead ends.
- **`hauto lq:on`** (from Hammer) closes most boolean case-split goals in the list/tree instances.

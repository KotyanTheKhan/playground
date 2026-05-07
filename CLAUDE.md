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

```
posets/              — IsPoset, lattice classes, Dilworth theorem
  PosetClasses.v     — IsPoset typeclass only
  LatticeClasses.v   — IsMeetSemilattice, IsJoinSemilattice, IsLattice, IsDistributiveLattice
  LatticeOrder.v     — meet_le order + meet_semilattice_is_poset instance
  FinitePoset.v      — IsFinitePoset bundled class
  NatInstances.v     — nat instances
  dilworth/          — Dilworth theorem, corollaries, concrete example
  dimension/         — Dimension theory
list/                — list poset / lattice instances (lexicographic order)
tree/                — tree poset / lattice instances
happenedBefore/      — happened-before causal order, semilattice impossibility
eventualConsistency/ — eventual consistency models
standard_example/    — S(n,k) poset proofs
abhishek/            — Dilworth (alternate proof), Hall's theorem, Erdős–Szekeres
```

Each directory under `_CoqProject` is a separate logical library mapped with `-R`.

## Import conventions

- Files in `posets/` import as `From Posets Require Import PosetClasses.`
- Files in `list/`, `tree/`, etc. import as `Require Import Posets.PosetClasses.`
- If a file uses any lattice class (`IsMeetSemilattice`, `IsJoinSemilattice`, `IsLattice`, `IsDistributiveLattice`) it must import **both**:
  ```coq
  Require Import Posets.PosetClasses.
  Require Import Posets.LatticeClasses.
  ```

## Key typeclasses

```coq
Class IsPoset (A : Type) (R : A -> A -> Prop)        (* PosetClasses.v *)
Class IsMeetSemilattice (A : Type) (meet : A -> A -> A)  (* LatticeClasses.v *)
Class IsJoinSemilattice (A : Type) (join : A -> A -> A)
Class IsLattice (A : Type) (meet join : A -> A -> A)
Class IsDistributiveLattice (A : Type) (meet join : A -> A -> A)
Class IsFinitePoset (A : Type) (R : A -> A -> Prop) (n : nat)  (* FinitePoset.v *)
```

`meet_le` (in `LatticeOrder.v`) derives an `IsPoset` from any `IsMeetSemilattice`:
```coq
Definition meet_le : A -> A -> Prop := fun x y => meet x y = x.
```

## Common Coq pitfalls in this codebase

- **`rewrite X at 1`** requires setoid. Use `transitivity` to split goals instead.
- **Typeclass resolution from bundled classes**: if `IsFinitePoset` wraps `IsPoset` but inference doesn't find it, add `#[local] Existing Instance fp_is_poset.` inside the section.
- **`repeat first [apply Union_introl | apply Union_intror | apply In_singleton]`**: put the most specific branch first to avoid greedy left choices into dead ends.
- **`hauto lq:on`** (from Hammer) closes most boolean case-split goals in the list/tree instances.

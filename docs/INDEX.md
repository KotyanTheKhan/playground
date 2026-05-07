# Theory Index

**Keep this file up to date** — add entries when new classes, instances, or theorems are proved; remove or update entries when things move or are renamed.

---

## Typeclasses

### Poset hierarchy (`posets/`)

| Class | File | Parameters |
|-------|------|------------|
| `IsPoset` | `PosetClasses.v` | `A R` |
| `IsMeetSemilattice` | `LatticeClasses.v` | `A meet` |
| `IsJoinSemilattice` | `LatticeClasses.v` | `A join` |
| `IsLattice` | `LatticeClasses.v` | `A meet join` |
| `IsDistributiveLattice` | `LatticeClasses.v` | `A meet join` |
| `IsFinitePoset` | `FinitePoset.v` | `A R n` — bundles `IsPoset` + cardinality |

### Dilworth definitions (`posets/dilworth/Definitions.v`)

| Class | Meaning |
|-------|---------|
| `IsChain S` | `S` is a chain |
| `IsAntichain S` | `S` is an antichain |
| `IsChainCover S cover` | `cover` partitions `S` into chains |
| `Width S w` | `w` is the width (max antichain size) of `S` |
| `ChainCoverNumber S k` | `k` is the minimum chain cover number of `S` |

---

## Key Definitions

| Name | File | Meaning |
|------|------|---------|
| `meet_le` | `posets/LatticeOrder.v` | `meet_le x y ≔ meet x y = x` — canonical order from meet |
| `nat_meet` / `nat_join` | `posets/NatInstances.v` | `Nat.min` / `Nat.max` |
| `Above` / `Below` | `posets/dilworth/Definitions.v` | up-set / down-set relative to a set |

---

## Instances

### `nat`

| Instance | File |
|----------|------|
| `nat_poset : IsPoset nat le` | `posets/NatInstances.v` |
| `nat_meet_semilattice` | `posets/NatInstances.v` |
| `nat_join_semilattice` | `posets/NatInstances.v` |
| `nat_lattice_semi : IsLattice nat nat_meet nat_join` | `posets/NatInstances.v` |
| `nat_distrib_semi : IsDistributiveLattice nat ...` | `posets/NatInstances.v` |

### `List` (lexicographic order)

| Instance | File |
|----------|------|
| `list_meet_semilattice` | `list/MeetSemilatticeInstance.v` |
| `list_join_semilattice` | `list/JoinSemilatticeInstance.v` |
| `list_lattice` | `list/LatticeInstance.v` |
| `list_distributive_lattice` | `list/DistributiveLatticeInstance.v` |

### `Tree`

| Instance | File |
|----------|------|
| `tree_poset` | `tree/Instances.v` |
| `tree_meet_semilattice` | `tree/Instances.v` |
| `tree_join_semilattice` | `tree/Instances.v` |
| `tree_lattice` | `tree/Instances.v` |
| `tree_distrib_lattice` | `tree/Instances.v` |

### Derived

| Instance | File | Note |
|----------|------|------|
| `meet_semilattice_is_poset` | `posets/LatticeOrder.v` | `IsMeetSemilattice → IsPoset` via `meet_le` |

---

## Theorems and Corollaries

### Dilworth (`posets/dilworth/`)

| Name | File | Statement |
|------|------|-----------|
| `Dilworth` | `DilworthTheorem.v` | width = min chain cover number for any finite poset |
| `Dilworth_finite` | `DilworthCorollaries.v` | same, for `IsFinitePoset` (no explicit `n`) |
| `Dilworth_meet_semilattice` | `DilworthCorollaries.v` | Dilworth for any `IsMeetSemilattice` (via `meet_le`) |
| `Dilworth_lattice` | `DilworthCorollaries.v` | Dilworth for any `IsLattice` |
| `Dilworth_distributive_lattice` | `DilworthCorollaries.v` | Dilworth for any `IsDistributiveLattice` |

### Dimension (`posets/dimension/`)

| Name | File | Statement |
|------|------|-----------|
| `szpilrajn_theorem` | `Szpilrajn.v` | every partial order extends to a linear order |
| `incomparable_extension` | `Theorems.v` | incomparable elements can be ordered in some linear extension |
| `dushnik_miller_exists` | `Theorems.v` | every poset has a realizer |
| `subposet_dimension_le` | `Theorems.v` | dimension is monotone under sub-posets |
| `hiraguchi_bound` | `Theorems.v` | Hiraguchi's dimension bound |

### Happened-before (`happenedBefore/SemilatticeContradiction.v`)

| Name | Statement |
|------|-----------|
| `happened_before_not_poset_semilattice` | `happened_before nil` has no GLBs for cross-process events |
| `happened_before_cannot_be_meet_semilattice_instance` | no `IsMeetSemilattice` instance respects causal GLBs |
| `happened_before_cannot_be_join_semilattice_instance` | same for LUBs |
| `happened_before_cannot_be_lattice_instance` | no `IsLattice` instance is causally correct |
| `lex_meet_not_causal_glb` / `lex_join_not_causal_lub` | lexicographic meet/join are not causal GLB/LUB |

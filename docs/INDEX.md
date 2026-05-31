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
| `hiraguchi_bound_direct` | `HiraguchiDirect.v` | **Hiraguchi's bound `dim ≤ ⌊n/2⌋` (n≥4), SOUND proof.** Via `dimension_le_width` + `antichain_complement_dim_bound` (Trotter 1975 Thm 2) + `hiraguchi_combine`, using `width_exists`. `Print Assumptions` = standard classical axioms + the single base-case admit `small_complement_le_2` (Trotter Lemma 3). **No dependence on the Removable Pair Conjecture.** |
| `one_point_removal` | `OnePointRemoval.v` | `dim X ≤ 1 + dim(X−p)` (Trotter 1975 ineq. 1), Qed |
| `antichain_complement_dim_bound` | `AntichainComplement.v` | `dim P ≤ max{2,|P−A|}` for antichain A (Trotter 1975 Thm 2); Qed modulo `small_complement_le_2` |
| `width_exists` | `WidthExists.v` | every finite nonempty poset has a maximum antichain (Width), Qed |
| `linear_sum_dimension` | `LinearSum.v` | `dim(A ⊕ B) = max(dim A, dim B)` for the linear sum (positive dims), Qed |
| `product_dimension_le` | `ProductDimension.v` | `dim(A × B) ≤ dim A + dim B` (positive dims), Qed |
| `small_complement_le_2` | `AntichainComplement.v` | **(admit, TRUE)** antichain + ≤2 points ⟹ dim ≤ 2 (Trotter Lemma 3 finite analysis). The sole remaining gap — and the only admit — in the dimension module. |

> **Note (2026-05-31 prune).** The superseded `hiraguchi_bound` proof and its
> dependency on the OPEN Removable Pair Conjecture — together with the entire
> N5/N4 realizer + dispatcher + exhaustive machinery (~75.5K lines) — were
> removed. The full investigation is preserved on the git tag
> `archive/dimension-n5-full`. `hiraguchi_bound_direct` is the headline result;
> its only admit is `small_complement_le_2`.

### Happened-before (`happenedBefore/SemilatticeContradiction.v`)

| Name | Statement |
|------|-----------|
| `happened_before_not_poset_semilattice` | `happened_before nil` has no GLBs for cross-process events |
| `happened_before_cannot_be_meet_semilattice_instance` | no `IsMeetSemilattice` instance respects causal GLBs |
| `happened_before_cannot_be_join_semilattice_instance` | same for LUBs |
| `happened_before_cannot_be_lattice_instance` | no `IsLattice` instance is causally correct |
| `lex_meet_not_causal_glb` / `lex_join_not_causal_lub` | lexicographic meet/join are not causal GLB/LUB |

### Execution poset (`execution/`)

#### `execution/Op.v` — operations and programs

| Name | Meaning |
|------|---------|
| `Op` | inductive: `Local` / `Send` / `Recv` |
| `Program` | `list (list Op)` — per-process op sequences |
| `nprocs` / `proc_ops` / `proc_len` / `op_at` | program accessor definitions |
| `matched` | `Send`/`Recv` matching predicate |
| `wf_program` | well-formedness: all sends are matched |

#### `execution/Event.v` — event carrier

| Name | Meaning |
|------|---------|
| `Valid` / `ValidSet` | in-bounds `(process, index)` predicate and set |
| `Event` | finite carrier type (subtype of valid pairs) |
| `total` | total number of events across all processes |
| `raw_events` | explicit list of all events |
| `raw_events_NoDup` / `raw_events_spec` / `raw_events_length` | list well-formedness lemmas |
| `event_eq_dec` | decidable equality on `Event` |

#### `execution/Finite.v` — finiteness of the event carrier

| Name | Meaning |
|------|---------|
| `cardinal_of_NoDup_list` | cardinality via a duplicate-free list |
| `valid_cardinal` | `|ValidSet|` equals `total` |
| `event_cardinal` | `Event` carrier is finite (via `cardinal_subtype_full`) |

#### `execution/Edges.v` — program order and happens-before

| Name | Meaning |
|------|---------|
| `edge` | program-order + matched-message edge relation |
| `hb` | reflexive-transitive closure of `edge` |
| `hb_refl` / `hb_trans` | reflexivity and transitivity of `hb` |

#### `execution/Rank.v` — ranked programs and acyclicity

| Name | Meaning |
|------|---------|
| `RankedProgram` | rank strictly increasing along every `edge` |
| `hb_eq_or_rank_lt` | `hb e1 e2 → e1 = e2 ∨ rank e1 < rank e2` |
| `rank_hb_le` | `hb e1 e2 → rank e1 ≤ rank e2` |
| `hb_neq_rank_lt` | `hb e1 e2 → e1 ≠ e2 → rank e1 < rank e2` |
| `hb_antisym` | structural acyclicity of `hb` |

#### `execution/Poset.v` — poset instances

| Name | Meaning |
|------|---------|
| `hb_IsPoset` | `IsPoset Event hb` instance |
| `hb_IsFinitePoset` | `IsFinitePoset Event hb n` instance |
| `ExecPoset` | bundled record wrapping the poset |
| `exec_of` | constructs an `ExecPoset` from a `RankedProgram` |

#### `execution/Schedule.v` — frontier schedule model

| Name | Meaning |
|------|---------|
| `Frontier` / `Schedule` | Ψ(N,S) frontier model types |
| `op_for` | operation at a schedule step |
| `desugar_prog` / `desugar_rank` / `desugar` | schedule desugaring to `Program` + rank |
| `desugar_rank_mono` | desugared rank is strictly monotone along edges |
| `exec_of_schedule` | produces an `ExecPoset` from a `Schedule` |
| `schedule_program_agree` | schedule and desugared program agree on operations |

#### `execution/FromEdges.v` — poset construction from an edge spec

| Name | Meaning |
|------|---------|
| `EdgeSpec` | record specifying a finite edge relation |
| `op_at_es` | operation lookup from an `EdgeSpec` |
| `prog_of_edgespec` | builds a `Program` from an `EdgeSpec` |
| `edgespec_ranked` | `prog_of_edgespec` satisfies `RankedProgram` |
| `from_edges` | produces an `ExecPoset` directly from an `EdgeSpec` |
| `hb_prog_eq` | equal-process events agree on program |

#### `execution/Agreement.v` — universal schedule ⟷ edge-set agreement

| Name | Meaning |
|------|---------|
| `translate` | builds the equivalent `EdgeSpec` from a `Schedule` |
| `schedule_edges_agree` | `∀ s, desugar_prog s = prog_of_edgespec (translate s)` (axiom-free) |
| `schedule_edges_hb_agree` | the two representations induce the same `hb` order (transported) |

#### `execution/Examples.v` — test examples (not exported by aggregator)

| Name | Meaning |
|------|---------|
| `sched_n3` / `edges_n3` / `n3_same_program` | 3-event schedule and its edge spec, program agreement |
| `n3_ordered` / `n3_concurrent` | ordering facts for the n3 example |
| `sched_m45` / `edges_m45` / `m45_same_program` | 4+5-process mixed schedule example |

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

#### `execution/DimBridge.v` — dimension bridge to the Dimension theory

| Name | Meaning |
|------|---------|
| `exec_has_dimension` | an execution poset has dimension d |
| `exec_dimension_exists` | every execution has a dimension |
| `exec_dim_ge_2` | an incomparable pair forces dim ≥ 2 |
| `exec_dim_eq_2_of_realizer` | a size-2 realizer + incomparable pair ⇒ dim = 2 |

#### `execution/DimCriticalPairs.v` — critical-pair interface

| Name | Meaning |
|------|---------|
| `exec_critical_pair` | critical pair of an execution poset |
| `exec_incomparable_has_critical_pair` | every incomparable pair contains a critical pair |
| `exec_critical_pairs_reversible_iff_no_alt_cycle` | reversibility ⟺ no alternating cycle |
| `exec_dim_le_2_of_no_alt_cycle` | no alternating cycle of critical pairs ⇒ dim ≤ 2. **⚠ WEAK:** the hypothesis is strictly stronger than dim ≤ 2 (single-extension-reversible) and fails on antichains; converse is false. For a usable dim ≤ 2 lever see `barrier_dim_le2`. |

#### `execution/DimExamples.v` / `DimExampleN3.v` — concrete dimension-2 results (test-only)

| Name | Meaning |
|------|---------|
| `E_min_dim_2` | the minimal 4-event execution has dimension exactly 2 |
| `E_n3_dim_2` | the N=3 execution has dimension exactly 2 |

#### `execution/Examples.v` — test examples (not exported by aggregator)

| Name | Meaning |
|------|---------|
| `sched_n3` / `edges_n3` / `n3_same_program` | 3-event schedule and its edge spec, program agreement |
| `n3_ordered` / `n3_concurrent` | ordering facts for the n3 example |
| `sched_m45` / `edges_m45` / `m45_same_program` | 4+5-process mixed schedule example |

#### `execution/Frontier.v` — frontiers and barriers

| Name | Meaning |
|------|---------|
| `ConsistentCut` / `Frontier` | down-closed cut; antichain frontier of a cut |
| `IsBarrier` | L/U partition with all of L below all of U |
| `frontier_is_antichain` / `barrier_lower_consistent` / `barrier_upper_disjoint_below` | structural lemmas |

#### `execution/DimIso.v` — dimension under isomorphism

| Name | Meaning |
|------|---------|
| `dimension_iso` | poset dimension is invariant under order-isomorphism |

#### `execution/Ordinal.v` — barrier (ordinal-sum) decomposition

| Name | Meaning |
|------|---------|
| `sub_order` / `no_alt_cycle` | sub-poset on an ensemble; no alternating cycle of critical pairs |
| `barrier_critical_pairs` | critical pairs lie within a single block |
| `barrier_dim_ge` | `dim ≥ max` of block dimensions |
| `barrier_no_alt_cycle_propagation` | block no-alt-cycle ⇒ whole no-alt-cycle |
| `barrier_dim2` | both blocks no-alt-cycle ⇒ whole dim ≤ 2. **⚠ WEAK** (no-alt-cycle ≫ dim ≤ 2); use `barrier_dim_le2` for the genuine all-cases lever. |
| `barrier_dimension` | `dim = max` of block dimensions (via the linear sum) |

#### `execution/FullySync.v` — fully-synchronized decomposition

| Name | Meaning |
|------|---------|
| `IsFullySync` | execution is an ordinal sum of blocks (each prefix split a barrier) |
| `fully_sync_no_alt_cycle` / `fully_sync_dim2` | every block free of alternating cycles ⇒ the whole execution is dim ≤ 2. **⚠ WEAK:** no-alt-cycle ≫ dim ≤ 2 and fails on antichain blocks (effectively vacuous for mΨ); a genuine n-way lever would iterate `barrier_dim_le2`. |

#### `execution/FrontierExamples.v` — concrete barrier (test-only)

| Name | Meaning |
|------|---------|
| `E_min_barrier` / `E_min_barrier_cps` | the minimal execution's bottom barrier; critical pairs within blocks |

#### `execution/Reduction.v` — dimension-preserving reductions

| Name | Meaning |
|------|---------|
| `PreservesDim` / `ReducesDim` | two posets share a dimension / source dim ≤ target dim |
| `preserves_dim_refl` / `_sym` / `_trans`, `reduces_dim_refl` / `_trans`, `preserves_dim_reduces` | composability algebra |
| `iso_preserves_dim` | order-isomorphism preserves dimension |
| `subposet_reduces_dim` | an induced subposet has dimension ≤ the whole |
| `embedding_reduces_dim` | an order-embedding reduces dimension |
| `preserves_dim2` / `reduces_dim2` | the relations transport / bound the `dim ≤ 2` property |

#### `execution/ReductionExamples.v` — concrete reduction (test-only)

| Name | Meaning |
|------|---------|
| `E_min_block_reduces` / `E_min_block_dim_le_2` | E_min's dimension analysis reduces to its nontrivial block |
| `reduction_chain_demo` | composing an iso step with a subposet reduction |

#### `execution/ExtremumReduction.v` — extremum removal preserves dim<=2

| Name | Meaning |
|------|---------|
| `IsGlobalMin` / `IsGlobalMax` | element below / above all others |
| `remove_min_preserves_dim2` / `remove_max_preserves_dim2` | removing a global extremum preserves dim <= 2 (realizer surgery) |

#### `execution/ExtremumReductionExamples.v` — concrete extremum reduction (test-only)

| Name | Meaning |
|------|---------|
| `E_min_a_global_min` | E_min's bottom event is a global minimum |
| `E_min_remove_min_dim2` / `E_min_block_dim_le_2_via_extremum` | E_min's dim<=2 analysis reduces to its 3-element block |

#### `execution/BarrierDim2.v` — all-cases binary barrier dim<=2 lever

| Name | Meaning |
|------|---------|
| `block_dim0_global_min` / `block_dim0_global_max` | a dimension-0 block is a single global extremum |
| `barrier_dim_le2` | a barrier with both blocks dim<=2 makes the whole dim<=2 (no dim>0 hypothesis) |

#### `execution/BarrierDim2Examples.v` — concrete barrier dim<=2 (test-only)

| Name | Meaning |
|------|---------|
| `E_min_dim_le_2_via_barrier` | E_min is dim<=2 via the all-cases barrier lever on its bottom split |

#### `execution/FinPosetDim*.v` — generic finite-poset dimension levers

Carrier-generic versions of the ExecPoset levers (on any `(A,R)` with `IsPoset` + `Finite (Full_set A)`), needed for the n-way recursion where the lower part of a barrier split is a bare sub-poset, not an ExecPoset.

| Name | Meaning |
|------|---------|
| `fin_sub_order` / `fin_global_min` / `fin_global_max` / `fin_is_barrier` | generic sub-poset, extrema, barrier |
| `fin_dim_exists` | every finite poset has a dimension |
| `fin_remove_min_dim2` / `fin_remove_max_dim2` | removing a global extremum preserves dim ≤ 2 |
| `fin_block_dim0_global_min` / `fin_block_dim0_global_max` | a dimension-0 block is a single global extremum |
| `fin_barrier_dimension` | `dim = max` of block dimensions (both > 0) |
| `fin_barrier_dim_le2` | a barrier with both blocks dim ≤ 2 makes the whole dim ≤ 2 |
| `fin_chain_reproduces_E_min` | (test) the generic chain reproduces E_min's dim ≤ 2 |

#### `execution/FinFullySync.v` / `FullySyncDim2.v` — n-way fully-synchronized dim≤2

The genuine n-way dim≤2 lever: a fully-synchronized execution whose blocks are each dim ≤ 2 is itself dim ≤ 2. Proven generically on bare finite posets (so the induction recurses into the lower sub-poset of a barrier split), then instantiated for `IsFullySync`.

| Name | Meaning |
|------|---------|
| `fin_ordinal_partition` | a finite poset partitioned into linearly-ordered blocks |
| `restrict_block` / `restrict_partition` / `restricted_block_dim2` | restricting a partition / block dimension to a prefix sub-poset |
| `fin_sub_order_finite` / `fin_block_iso_full` | a subtype of a finite poset is finite; a full block is order-iso to the whole |
| `fin_fully_sync_dim_le2` | (generic) ordinal partition with each block dim ≤ 2 ⇒ whole dim ≤ 2 |
| `fully_sync_pairwise_below` | IsFullySync's prefix barriers ⇒ earlier blocks lie below later ones |
| `fully_sync_dim_le2` | (ExecPoset) the n-way dim ≤ 2 lever for `IsFullySync` |
| `E_min_is_fully_sync_2` / `E_min_dim_le_2_via_fully_sync` | (test) E_min as a 2-block fully-sync execution, dim ≤ 2 via the n-way path |

#### `execution/FinExtremumDim.v` — exact barrier dimension (exact n-way dim=max, slice 1)

Exact-dimension siblings of the dim≤2 levers. Adding a global extremum to a nonempty poset gives `dim = max(d, 1)` (so a singleton rest ⇒ a 2-chain ⇒ dim 1); a barrier with blocks of dimensions dL, dU has `dim = max(1, max(dL, dU))`.

| Name | Meaning |
|------|---------|
| `fin_singleton_dim0` | a ≤1-element poset has dimension 0 |
| `fin_add_min_dim` / `fin_add_max_dim` | adding a global min/max gives `dim = max(d, 1)` (rest inhabited) |
| `fin_barrier_dimension_full` | a barrier with block dims dL, dU has `dim = max(1, max(dL, dU))` |
| `chain2_exact_dim` | (test) a 2-element chain has dimension 1 via `fin_add_min_dim` |

#### `execution/FinFullySyncDim.v` / `FullySyncDimExact.v` — exact n-way fully-synchronized dimension (slice 2)

Completes the exact n-way `dim = max`: a fully-synchronized execution with ≥2 elements has `dim = max(1, maxᵢ dim(Bᵢ))` (the per-block dimensions given as a `dims` list; `max(1, …)` because singleton blocks have dimension 0).

| Name | Meaning |
|------|---------|
| `singleton_union_one_block` | a singleton-union prefix is one singleton block (dims-fold = 0) |
| `restricted_block_dim_exact` | a prefix block's exact dimension transports to its restriction |
| `fin_fully_sync_dimension` | (generic) ordinal partition ⇒ `dim = max(1, fold_right max 0 dims)` |
| `fully_sync_dimension` | (ExecPoset) the exact n-way dimension for `IsFullySync` |
| `chain_all_singleton_dim` | (test) an all-singleton 2-block chain has dimension 1 |

#### `execution/ChainDim.v` / `TransformA.v` — Transformation A (sync-square contraction)

Transformation A (contract a synchronization square into 2 synchronized points) as a dimension-preserving block replacement: replacing a fully-synchronized block by another of equal dimension preserves the whole execution's dimension (via `fully_sync_dimension`). The square and its contraction are both dimension-1 chains, so A *preserves* (does not lower) dimension — matching the paper. The square↔contraction geometry is a concrete realization of the paper's informally-specified contraction.

| Name | Meaning |
|------|---------|
| `chain_dim_1` | a total order on ≥2 elements has dimension 1 |
| `transform_preserves_dimension` | two fully-sync executions with equal max-block-dimension have equal dimension |
| `B_square_R` / `B_contracted_R` | the 4-event square (4-chain) and 2-point contracted (2-chain) blocks, each dimension 1 |
| `transform_A_preserves` | swapping the square block for its contraction preserves the execution's dimension |
| `transform_A_square_dim_1` / `transform_A_contracted_dim_1` | (test) both blocks have dimension 1 |

#### `execution/SyncShape.v` — sync-shape operational definitions + IsFullySync bridge

Program-level "sync-shape" (every matched send/recv pair at the same local index — the rendezvous form): every `desugar s` program is sync-shaped. A fully-synchronizing schedule's execution is a fully-synchronized decomposition by frontiers (`IsFullySync`), connecting program syntax to the dimension machinery. `FullySynchronizing` is the barrier-ordering lifted to the schedule (a caller-discharged hypothesis), not derived from per-frontier connectivity (a later refinement).

| Name | Meaning |
|------|---------|
| `sync_shaped` / `synchronous_message` | every matched send/recv pair is at the same local index |
| `desugar_sync_shaped` | every frontier-model (`desugar s`) program is sync-shaped |
| `frontier_block` / `frontier_blocks` | the per-local-index event blocks of a schedule's execution |
| `FullySynchronizing` | every index-i event precedes every index-j>i event (the barrier ordering hypothesis) |
| `fully_synchronizing_is_fully_sync` | a fully-synchronizing schedule's execution is `IsFullySync` by frontiers |
| `fully_synchronizing_dim2` | + per-frontier-block dim≤2 ⇒ execution dim≤2 |
| `s_demo_*` | (test) a concrete 2×2 fully-synchronizing schedule end-to-end |

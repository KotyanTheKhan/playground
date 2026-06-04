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

#### `execution/core/Op.v` — operations and programs

| Name | Meaning |
|------|---------|
| `Op` | inductive: `Local` / `Send` / `Recv` |
| `Program` | `list (list Op)` — per-process op sequences |
| `nprocs` / `proc_ops` / `proc_len` / `op_at` | program accessor definitions |
| `matched` | `Send`/`Recv` matching predicate |
| `wf_program` | well-formedness: all sends are matched |

#### `execution/core/Event.v` — event carrier

| Name | Meaning |
|------|---------|
| `Valid` / `ValidSet` | in-bounds `(process, index)` predicate and set |
| `Event` | finite carrier type (subtype of valid pairs) |
| `total` | total number of events across all processes |
| `raw_events` | explicit list of all events |
| `raw_events_NoDup` / `raw_events_spec` / `raw_events_length` | list well-formedness lemmas |
| `event_eq_dec` | decidable equality on `Event` |

#### `execution/core/Finite.v` — finiteness of the event carrier

| Name | Meaning |
|------|---------|
| `cardinal_of_NoDup_list` | cardinality via a duplicate-free list |
| `valid_cardinal` | `|ValidSet|` equals `total` |
| `event_cardinal` | `Event` carrier is finite (via `cardinal_subtype_full`) |

#### `execution/core/Edges.v` — program order and happens-before

| Name | Meaning |
|------|---------|
| `edge` | program-order + matched-message edge relation |
| `hb` | reflexive-transitive closure of `edge` |
| `hb_refl` / `hb_trans` | reflexivity and transitivity of `hb` |

#### `execution/core/Rank.v` — ranked programs and acyclicity

| Name | Meaning |
|------|---------|
| `RankedProgram` | rank strictly increasing along every `edge` |
| `hb_eq_or_rank_lt` | `hb e1 e2 → e1 = e2 ∨ rank e1 < rank e2` |
| `rank_hb_le` | `hb e1 e2 → rank e1 ≤ rank e2` |
| `hb_neq_rank_lt` | `hb e1 e2 → e1 ≠ e2 → rank e1 < rank e2` |
| `hb_antisym` | structural acyclicity of `hb` |

#### `execution/core/Poset.v` — poset instances

| Name | Meaning |
|------|---------|
| `hb_IsPoset` | `IsPoset Event hb` instance |
| `hb_IsFinitePoset` | `IsFinitePoset Event hb n` instance |
| `ExecPoset` | bundled record wrapping the poset |
| `exec_of` | constructs an `ExecPoset` from a `RankedProgram` |

#### `execution/core/Schedule.v` — frontier schedule model

| Name | Meaning |
|------|---------|
| `Frontier` / `Schedule` | Ψ(N,S) frontier model types |
| `op_for` | operation at a schedule step |
| `desugar_prog` / `desugar_rank` / `desugar` | schedule desugaring to `Program` + rank |
| `desugar_rank_mono` | desugared rank is strictly monotone along edges |
| `exec_of_schedule` | produces an `ExecPoset` from a `Schedule` |
| `schedule_program_agree` | schedule and desugared program agree on operations |

#### `execution/core/ScheduleWf.v` — well-formed schedules + `desugar_wf`

Well-formedness of the frontier model: each frontier must be a **partial matching** — every process participates at most once, in one role. This strengthens the original in-range-only sketch, which is *unsound* (`desugar_wf` is false under it: a frontier `[(0,1);(0,2)]` has all endpoints in range yet produces an unmatched receive). Under the matching condition, `op_for` is fully characterized by membership, discharging all four `wf_program` obligations.

| Name | Meaning |
|------|---------|
| `wf_frontier` | a frontier is in-range + `NoDup (flat_map endpoints …)` (partial matching) |
| `wf_schedule` | every frontier of the schedule is `wf_frontier` |
| `find_fst_unique` / `find_snd_unique` / `no_fst_of_recv` | `find` is canonical under the `NoDup` matching |
| `op_for_send_iff` / `op_for_recv_iff` | `op_for fr p k = Send q k ⟺ In (p,q) fr` (and the recv dual) |
| `op_at_desugar_inv` | a `Some` from `op_at (desugar_prog s)` is in-range and reads back as `op_for` |
| `desugar_wf` | `wf_schedule s → wf_program (desugar s)` (axiom-free); closes the core-model deferral |
| `wf_sched_n3` / `wf_s_demo` / `wf_sched_m45` | (test) concrete well-formed schedule witnesses |

#### `execution/core/FromEdges.v` — poset construction from an edge spec

| Name | Meaning |
|------|---------|
| `EdgeSpec` | record specifying a finite edge relation |
| `op_at_es` | operation lookup from an `EdgeSpec` |
| `prog_of_edgespec` | builds a `Program` from an `EdgeSpec` |
| `edgespec_ranked` | `prog_of_edgespec` satisfies `RankedProgram` |
| `from_edges` | produces an `ExecPoset` directly from an `EdgeSpec` |
| `hb_prog_eq` | equal-process events agree on program |

#### `execution/core/Agreement.v` — universal schedule ⟷ edge-set agreement

| Name | Meaning |
|------|---------|
| `translate` | builds the equivalent `EdgeSpec` from a `Schedule` |
| `schedule_edges_agree` | `∀ s, desugar_prog s = prog_of_edgespec (translate s)` (axiom-free) |
| `schedule_edges_hb_agree` | the two representations induce the same `hb` order (transported) |

#### `execution/dimension/DimBridge.v` — dimension bridge to the Dimension theory

| Name | Meaning |
|------|---------|
| `exec_has_dimension` | an execution poset has dimension d |
| `exec_dimension_exists` | every execution has a dimension |
| `exec_dim_ge_2` | an incomparable pair forces dim ≥ 2 |
| `exec_dim_eq_2_of_realizer` | a size-2 realizer + incomparable pair ⇒ dim = 2 |

#### `execution/dimension/DimTwoGeneric.v` — carrier-generic dimension-2 toolkit (exported)

| Name | Meaning |
|------|---------|
| `dim_ge_2_of_incomparable` | an incomparable pair in any poset forces dim ≥ 2 |
| `dim_eq_2_of_realizer` | a size-2 realizer + incomparable pair ⇒ dim = 2 |
| `dim2_record` | builds `PosetDimension R 2` from two linear extensions meeting in `R` plus an incomparable pair (bare `Type`-sorted record) |

#### `execution/dimension/DimCriticalPairs.v` — critical-pair interface

| Name | Meaning |
|------|---------|
| `exec_critical_pair` | critical pair of an execution poset |
| `exec_incomparable_has_critical_pair` | every incomparable pair contains a critical pair |
| `exec_critical_pairs_reversible_iff_no_alt_cycle` | reversibility ⟺ no alternating cycle |
| `exec_dim_le_2_of_no_alt_cycle` | no alternating cycle of critical pairs ⇒ dim ≤ 2. **⚠ WEAK:** the hypothesis is strictly stronger than dim ≤ 2 (single-extension-reversible) and fails on antichains; converse is false. For a usable dim ≤ 2 lever see `barrier_dim_le2`. |

#### `execution/dimension/examples/DimExamples.v` / `DimExampleN3.v` — concrete dimension-2 results (test-only)

| Name | Meaning |
|------|---------|
| `E_min_dim_2` | the minimal 4-event execution has dimension exactly 2 |
| `E_n3_dim_2` | the N=3 execution has dimension exactly 2 |

#### `execution/dimension/examples/Examples.v` — test examples (not exported by aggregator)

| Name | Meaning |
|------|---------|
| `sched_n3` / `edges_n3` / `n3_same_program` | 3-event schedule and its edge spec, program agreement |
| `n3_ordered` / `n3_concurrent` | ordering facts for the n3 example |
| `sched_m45` / `edges_m45` / `m45_same_program` | 4+5-process mixed schedule example |

#### `execution/core/Frontier.v` — frontiers and barriers

| Name | Meaning |
|------|---------|
| `ConsistentCut` / `Frontier` | down-closed cut; antichain frontier of a cut |
| `IsBarrier` | L/U partition with all of L below all of U |
| `frontier_is_antichain` / `barrier_lower_consistent` / `barrier_upper_disjoint_below` | structural lemmas |

#### `execution/dimension/DimIso.v` — dimension under isomorphism

| Name | Meaning |
|------|---------|
| `dimension_iso` | poset dimension is invariant under order-isomorphism |

#### `execution/dimension/Ordinal.v` — barrier (ordinal-sum) decomposition

| Name | Meaning |
|------|---------|
| `sub_order` / `no_alt_cycle` | sub-poset on an ensemble; no alternating cycle of critical pairs |
| `barrier_critical_pairs` | critical pairs lie within a single block |
| `barrier_dim_ge` | `dim ≥ max` of block dimensions |
| `barrier_no_alt_cycle_propagation` | block no-alt-cycle ⇒ whole no-alt-cycle |
| `barrier_dim2` | both blocks no-alt-cycle ⇒ whole dim ≤ 2. **⚠ WEAK** (no-alt-cycle ≫ dim ≤ 2); use `barrier_dim_le2` for the genuine all-cases lever. |
| `barrier_dimension` | `dim = max` of block dimensions (via the linear sum) |

#### `execution/sync/FullySync.v` — fully-synchronized decomposition

| Name | Meaning |
|------|---------|
| `IsFullySync` | execution is an ordinal sum of blocks (each prefix split a barrier) |
| `fully_sync_no_alt_cycle` / `fully_sync_dim2` | every block free of alternating cycles ⇒ the whole execution is dim ≤ 2. **⚠ WEAK:** no-alt-cycle ≫ dim ≤ 2 and fails on antichain blocks (effectively vacuous for mΨ); a genuine n-way lever would iterate `barrier_dim_le2`. |

#### `execution/core/examples/FrontierExamples.v` — concrete barrier (test-only)

| Name | Meaning |
|------|---------|
| `E_min_barrier` / `E_min_barrier_cps` | the minimal execution's bottom barrier; critical pairs within blocks |

#### `execution/dimension/examples/EminBlockDimExamples.v` — E_min {b,c,d} block dim = 2 (test-only)

| Name | Meaning |
|------|---------|
| `bcd_R` / `bcd_poset` / `bcd_dim2` | a bare 3-element poset (b<nothing, c<d) of dimension exactly 2, via `dim2_record` |
| `f3` / `g3` / `f3_iso` | order-isomorphism between the bare poset and the `Umin = {b,c,d}` block of `E_min` |
| `dim_block_bcd_2` | the block `fin_sub_order (ep_order E_min) Umin` has `PosetDimension … 2`, transported via `dimension_iso` |
| `dim_block_a_0` | the lower block `fin_sub_order (ep_order E_min) Lmin = {a}` is a singleton ⇒ `PosetDimension … 0` (via `fin_singleton_dim0`) |
| `E_min_Hfin` / `E_min_fin_barrier` | E_min carrier finite; `IsBarrier E_min Lmin Umin` = `fin_is_barrier (ep_order E_min) Lmin Umin` |
| `E_min_exact_dim_via_barrier` | barrier assembly: `dim E_min = max 1 (max (dim Lmin) (dim Umin)) = max 1 (max 0 2) = 2`, via `fin_barrier_dimension_full`, cross-checking `E_min_dim_2`. **#66 closed** (the {b,c,d} block has dimension exactly 2; E_min exact-dim cross-check). |

#### `execution/dimension/Reduction.v` — dimension-preserving reductions

| Name | Meaning |
|------|---------|
| `PreservesDim` / `ReducesDim` | two posets share a dimension / source dim ≤ target dim |
| `preserves_dim_refl` / `_sym` / `_trans`, `reduces_dim_refl` / `_trans`, `preserves_dim_reduces` | composability algebra |
| `iso_preserves_dim` | order-isomorphism preserves dimension |
| `subposet_reduces_dim` | an induced subposet has dimension ≤ the whole |
| `embedding_reduces_dim` | an order-embedding reduces dimension |
| `preserves_dim2` / `reduces_dim2` | the relations transport / bound the `dim ≤ 2` property |

#### `execution/dimension/examples/ReductionExamples.v` — concrete reduction (test-only)

| Name | Meaning |
|------|---------|
| `E_min_block_reduces` / `E_min_block_dim_le_2` | E_min's dimension analysis reduces to its nontrivial block |
| `reduction_chain_demo` | composing an iso step with a subposet reduction |

#### `execution/dimension/ExtremumReduction.v` — extremum removal preserves dim<=2

| Name | Meaning |
|------|---------|
| `IsGlobalMin` / `IsGlobalMax` | element below / above all others |
| `remove_min_preserves_dim2` / `remove_max_preserves_dim2` | removing a global extremum preserves dim <= 2 (realizer surgery) |

#### `execution/dimension/examples/ExtremumReductionExamples.v` — concrete extremum reduction (test-only)

| Name | Meaning |
|------|---------|
| `E_min_a_global_min` | E_min's bottom event is a global minimum |
| `E_min_remove_min_dim2` / `E_min_block_dim_le_2_via_extremum` | E_min's dim<=2 analysis reduces to its 3-element block |

#### `execution/barriers/BarrierDim2.v` — all-cases binary barrier dim<=2 lever

| Name | Meaning |
|------|---------|
| `block_dim0_global_min` / `block_dim0_global_max` | a dimension-0 block is a single global extremum |
| `barrier_dim_le2` | a barrier with both blocks dim<=2 makes the whole dim<=2 (no dim>0 hypothesis) |

#### `execution/barriers/examples/BarrierDim2Examples.v` — concrete barrier dim<=2 (test-only)

| Name | Meaning |
|------|---------|
| `E_min_dim_le_2_via_barrier` | E_min is dim<=2 via the all-cases barrier lever on its bottom split |

#### `execution/dimension/FinPosetDim*.v` — generic finite-poset dimension levers

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

#### `execution/sync/FinFullySync.v` / `FullySyncDim2.v` — n-way fully-synchronized dim≤2

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

#### `execution/dimension/FinExtremumDim.v` — exact barrier dimension (exact n-way dim=max, slice 1)

Exact-dimension siblings of the dim≤2 levers. Adding a global extremum to a nonempty poset gives `dim = max(d, 1)` (so a singleton rest ⇒ a 2-chain ⇒ dim 1); a barrier with blocks of dimensions dL, dU has `dim = max(1, max(dL, dU))`.

| Name | Meaning |
|------|---------|
| `fin_singleton_dim0` | a ≤1-element poset has dimension 0 |
| `fin_add_min_dim` / `fin_add_max_dim` | adding a global min/max gives `dim = max(d, 1)` (rest inhabited) |
| `fin_barrier_dimension_full` | a barrier with block dims dL, dU has `dim = max(1, max(dL, dU))` |
| `chain2_exact_dim` | (test) a 2-element chain has dimension 1 via `fin_add_min_dim` |

#### `execution/sync/FinFullySyncDim.v` / `FullySyncDimExact.v` — exact n-way fully-synchronized dimension (slice 2)

Completes the exact n-way `dim = max`: a fully-synchronized execution with ≥2 elements has `dim = max(1, maxᵢ dim(Bᵢ))` (the per-block dimensions given as a `dims` list; `max(1, …)` because singleton blocks have dimension 0).

| Name | Meaning |
|------|---------|
| `singleton_union_one_block` | a singleton-union prefix is one singleton block (dims-fold = 0) |
| `restricted_block_dim_exact` | a prefix block's exact dimension transports to its restriction |
| `fin_fully_sync_dimension` | (generic) ordinal partition ⇒ `dim = max(1, fold_right max 0 dims)` |
| `fully_sync_dimension` | (ExecPoset) the exact n-way dimension for `IsFullySync` |
| `chain_all_singleton_dim` | (test) an all-singleton 2-block chain has dimension 1 |

#### `execution/dimension/ChainDim.v` / `execution/families/TransformA.v` — Transformation A (sync-square contraction)

Transformation A (contract a synchronization square into 2 synchronized points) as a dimension-preserving block replacement: replacing a fully-synchronized block by another of equal dimension preserves the whole execution's dimension (via `fully_sync_dimension`). The square and its contraction are both dimension-1 chains, so A *preserves* (does not lower) dimension — matching the paper. The square↔contraction geometry is a concrete realization of the paper's informally-specified contraction.

| Name | Meaning |
|------|---------|
| `chain_dim_1` | a total order on ≥2 elements has dimension 1 |
| `transform_preserves_dimension` | two fully-sync executions with equal max-block-dimension have equal dimension |
| `B_square_R` / `B_contracted_R` | the 4-event square (4-chain) and 2-point contracted (2-chain) blocks, each dimension 1 |
| `transform_A_preserves` | swapping the square block for its contraction preserves the execution's dimension |
| `transform_A_square_dim_1` / `transform_A_contracted_dim_1` | (test) both blocks have dimension 1 |

#### `execution/sync/SyncShape.v` — sync-shape operational definitions + IsFullySync bridge

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

#### `execution/barriers/ConnSync.v` — connectivity ⟹ FullySynchronizing (exported)

Derives the `FullySynchronizing` barrier ordering (taken as a hypothesis in `SyncShape.v`) from a local, per-transition connectivity condition. The key reduction is gap-induction: if every adjacent local-index pair is ordered (`StepBarrier`), then every index-i event precedes every index-j>i event. `StepConnected` supplies the adjacent orderings from a per-transition sync-pair *witness* — either the same process (program edge), a same-index message edge, a next-index message edge, or a relay through some `r` (message-then-program-then-message). `s_demo` is discharged this way in `ConnSyncExamples.v`.

| Name | Meaning |
|------|---------|
| `mk_event` | build a valid execution event `(p,k)` from in-range process/index proofs |
| `prog_step` / `msg_step` | the two primitive happened-before edges: same-process program edge `(p,k)→(p,S k)`; same-index message edge `(p,k)→(q,k)` from a frontier pair |
| `StepBarrier` / `step_barrier_implies_fullsync` | adjacent local-index events ordered; gap-induction lifts this to `FullySynchronizing` |
| `step_witness` / `StepConnected` | per-transition sync-pair witness (same proc / this-frontier / next-frontier / relay through `r`); holding at every adjacent transition |
| `step_connected_fully_synchronizing` | `wf_schedule` + nonempty procs + `StepConnected` ⇒ `FullySynchronizing` |
| `step_connected_dim2` | + per-frontier-block dim≤2 ⇒ execution dim≤2 |

Honest note: `StepConnected` is only satisfiable when the per-transition matching structure supplies the witnesses (caps synced procs per single transition ≈≤4); the lemmas themselves are general.

#### `execution/barriers/WindowSync.v` — thick (window) barrier (exported)

Lifts the per-transition barrier of `ConnSync.v` to a *window* of consecutive frontiers: when all process pairs are reachable through the multi-hop edges of a width-`(b−a)` window, every event before index `a` precedes every event at/after index `b`, for **any** process count. `window_reach` chains `window_step` (stay, or a single frontier cross) across the window so a route may relay through intermediate processes over several frontiers — exceeding the ≤4-process reach of one transition. `WindowSyncExamples.v` discharges a 3-process gather/scatter window (`s_gs`, frontiers `[(0,1)];[(1,0)];[(2,0)];[(0,1)];[(0,2)]`) where procs 1,2 gather to coordinator 0 then 0 scatters to 1,2; the window `[1,5)` synchronizes all three processes (`s_gs_window_barrier`), which no single transition could.

| Name | Meaning |
|------|---------|
| `window_step` | per-frontier forward step at level `k`: stay (`p=q`) or cross a frontier-`k` message pair |
| `window_reach` | windowed reachability: an `m`-hop chain of `window_step`s from frontier `a` to frontier `a+m` |
| `WindowConnected` | all process pairs window-reachable across `[a,b)` (the thick-barrier connectivity hypothesis) |
| `prog_chain` | a process's own events are ordered along increasing local index (program edges) |
| `window_reach_hb` | a `window_reach` route lifts to a happened-before ordering between its endpoints |
| `window_connected_barrier` | `WindowConnected s a b` ⇒ events before index `a` precede events at/after `b`, for **any** `n` |

Honest note: this records the consecutive-cut impossibility — a single transition reaches ≤4 processes (matchings + intra-frontier messages), so `FullySynchronizing` (the consecutive/adjacent barrier) is unattainable for `n>4`; a window of `b−a` frontiers lifts the cap by relaying through intermediate processes over several frontiers.

#### `execution/families/DisjointChainsDim.v` — disjoint-union-of-chains ⟹ dim ≤ 2 (exported)

Closes **critical-review finding 2**: `fully_sync_dim_le2`'s per-block `dim ≤ 2` hypothesis is now *discharged* for frontier blocks. A poset that is a disjoint union of chains (a component label `comp` with `R x y ⟹ comp x = comp y` and same-component ⟹ comparable) has dim ≤ 2 — proved by an explicit 2-realizer (lexicographic on `(comp, R)`, component order forward in `L1`, reversed in `L2`); **no width or finiteness needed**, so it applies where `two_chain_cover_dim_le2` (width ≤ 2) cannot. A frontier block's comparability is exactly the message matching (within one frontier, `hb` between distinct events is a single sender→receiver message — proved via the rank `2·index + c`), so every frontier block of a well-formed schedule is a disjoint union of chains, hence dim ≤ 2 *unconditionally*. `DisjointChainsDimExamples.v` discharges a width-3 antichain block (3 processes, empty frontier) where the width≤2 route fails.

| Name | Meaning |
|------|---------|
| `disjoint_chains_dim_le2` | a disjoint union of chains (component label + same-comp-chain) has dim ≤ 2 (explicit 2-realizer; no width/finiteness) |
| `hb_same_index_msg` | within one frontier, `hb` between two distinct events is a direct sender→receiver message (rank argument) |
| `fb_comp` | frontier-block component label: a receiver maps to its sender, else to itself |
| `frontier_block_dim_le2` | every frontier block of a well-formed schedule has dim ≤ 2 (discharges the per-block hypothesis) |
| `fully_sync_frontier_dim_le2` | `wf_schedule` + `IsFullySync` (frontier blocks) ⟹ execution dim ≤ 2 — the per-block bound is now automatic |

Honest note: this closes the **per-block** half of the gap (finding 2). It does **not** address **finding 1** — `fully_sync_frontier_dim_le2` still assumes `IsFullySync`, whose barrier ordering is unsatisfiable for `n>4` (matching frontiers). Admit-free (only standard classical/choice axioms).

#### `execution/barriers/BarrierExecDim.v` — true N-way barriers ⟹ dim ≤ 2 for any N (exported)

**Addresses critical-review finding 1.** The pairwise-message `hb` cannot order all of layer `k` before all of layer `k+1` for N>4 (a single transition reaches ≤4 processes), so `FullySynchronizing`/`IsFullySync` are unsatisfiable for N>4 — limiting the earlier dim≤2 story to N≤4. This module models a **true barrier**: the fully-synchronized order `blo` where *every index is a full barrier* (all of layer `i` precedes all of layer `j` for `i<j`), with the real intra-layer message matching as the within-layer order. `blo ⊇ hb` (it strengthens `hb` with the barrier edges — synchronization *reduces* dimension). We prove `dim (blo s) ≤ 2` for **arbitrary N**, formalizing the paper's general dim-2 claim for genuinely synchronized executions.

| Name | Meaning |
|------|---------|
| `layered_chains_dim_le2` | a layered poset (full barriers between layers + disjoint chains within each) has dim ≤ 2 — one explicit 2-realizer (lex `(layer, comp, R)`, component fwd/rev); no finiteness/width. Generalizes `disjoint_chains_dim_le2`. |
| `blo` | the fully-synchronized (true-barrier) order: `idx x < idx y`, or same index with the intra-layer `hb` order |
| `hb_idx_le` | `hb` respects the index (from the rank `2·idx + c`) |
| `blo_IsPoset` | `blo` is a partial order |
| `barrier_execution_dim_le2` | `wf_schedule s` ⟹ `dim (blo s) ≤ 2`, for **any** process count |
| `blo_dim_eq_2` | `wf_schedule s` + an incomparable pair in `blo s` ⟹ `dim (blo s) = 2` (exact; via `dim_ge_2_of_incomparable`). `bar5_dim_eq_2`: the N=5 barrier execution has dimension **exactly** 2. |

Honest scope: this models the *barrier* synchronization primitive (the paper's "synchronization"), not arbitrary pairwise-message executions (which are not dim ≤ 2). The pairwise `hb` model and its N>4 `FullySynchronizing` limitation remain on record alongside `blo`. `BarrierExecDimExamples.v` exhibits an **N=5** barrier execution with dim ≤ 2 — the regime finding 1 excluded. Admit-free (standard classical/proof-irrelevance axioms only).

#### `execution_clock/OnlineClock.v` — computable 2-coordinate clock (`blo` = product order) (exported)

Turns the abstract `L1`/`L2` realizer into a concrete computable timestamp. A generic theorem `stamp_iff` (any poset with integer `lay`/`comp`/`step` + bound `B` satisfying barrier/resp-lay/resp-comp/rank/bound ⟹ `R x y ↔ stamp x ≤_prod stamp y`, the product of two lexicographic orders, comparison on emitted integers only), instantiated for `blo` as `blo_iff_stamp` (**any N**). This is the soundness/characterization half of the "online dim-2 clock"; online *locality* is argued in `execution/DIM2_CLOCK.md`, not in Coq. Admit-free (`classic`, `proof_irrelevance`, `constructive_definite_description`, `Extensionality_Ensembles`).

| Name | Meaning |
|------|---------|
| `le_lex3` / `le_prod` | lexicographic ≤ on a nat triple (6-scalar form); product of the two lex orders (`T2` uses `B − comp`) |
| `stamp_iff` | generic: 5 structural hypotheses ⟹ `R x y ↔ le_prod …` (no finiteness; integer-only test) |
| `clk_lay` / `clk_comp` / `clk_step` | barrier index `snd`; `fb_comp`; `Recv?1:0` |
| `fb_comp_lt_nprocs` | `clk_comp < sch_nprocs` (the bound `B = nprocs−1`) |
| `blo_same_layer` / `hb_layer_step` / `blo_rank` | within-layer reductions discharging the rank hypothesis |
| `blo_iff_stamp` | `wf_schedule` ⟹ `blo s x y ↔ le_prod (nprocs−1) …`, for any process count |
| `stamp` | readable `(nat³ × nat³)` timestamp for `vm_compute` |

`OnlineClockExamples.v` (test): `s_bar5` (N=5 barrier, incomparable stamps), `s_msg3` (literal `vm_compute`d stamps for a sender/receiver/isolated triple), and an abstract length-3 chain exercising the generic `stamp_iff` with `step ∈ {0,1,2}`.

#### `execution_clock/OnlineClockLocal.v` — online maintenance: the locality theorem (exported)

`local_stamp (N p i : nat) (o : Op)` computes the clock from purely local data — the schedule `s` is **not** an argument, so the function cannot consult a global view; that signature *is* the locality. `local_stamp_correct` proves it equals the offline `stamp` at every valid event (near-definitional via `block_op_for`), and `blo_iff_local_stamp` restates the causality characterization `blo ⟺ stamp_le` purely through it. Two `reflexivity` interface lemmas pin the minimal interface: the only cross-process datum the clock reads is a `Recv`'s sender id (no clock-value piggybacking; per-process state is `(pid, a local counter)`). Honest scope: the *formula* is schedule-blind, but the bridge `local_obs s p i` still takes `s`; that a process determines its own op and layer counter from local state alone holds by the `blo` model's construction (noted, not separately formalized — that is the remaining operational-semantics work). Admit-free (the four standard axioms, inherited from `blo_iff_stamp`).

| Name | Meaning |
|------|---------|
| `local_stamp` | schedule-blind clock: `(N,p,i,op) → (nat³ × nat³)` |
| `local_obs` | the op a process observes at its event (`op_for …`) |
| `local_stamp_correct` | `local_stamp … = stamp s x` for every valid event |
| `stamp_le` / `stamp_le_stamp` | product order on stamp pairs; bridge to `le_prod` |
| `blo_iff_local_stamp` | `blo s x y ↔ stamp_le (local_stamp x) (local_stamp y)` |
| `local_stamp_send_eq_local` / `local_stamp_recv_tag_irrel` | Send carries no clock data; Recv uses only its sender |

`OnlineClockLocalExamples.v` (test): `s_msg3`'s local observations and stamps match the offline literals; a `local_stamp_correct` instance; causality via the local clock.

#### `execution_clock/RoundSem.v` — barrier-round operational model + schedule-free clock (exported)

An operational, primitive-state model: an `RSys` is `nprocs`, `nrounds`, and a per-process program `rs_prog p : list Op`; `rop S p r = nth r (rs_prog S p)` is process `p`'s round-`r` action. `rwf` is rendezvous compatibility (sends/recvs matched per round). `rhb` is the barrier order on valid events (`rhb_IsPoset`, unconditional, via the realized send∧recv edge). The clock `rclock S p r = local_stamp (nprocs) p r (rop S p r)` reads **only** `p`'s own program and counter — no `Schedule`/`op_at` projection — and `rhb_iff_rclock` proves causality through it (via `stamp_iff`). This closes the proof-skeptic W-2 gap operationally for the barrier-synchronized regime. Admit-free (`Print Assumptions rhb_iff_rclock` = only `proof_irrelevance`).

| Name | Meaning |
|------|---------|
| `RSys` / `rop` / `rvalid` / `rwf` | round system; per-process op; valid event; rendezvous well-formedness |
| `redge` / `rhb_same` / `rhb` / `rhb_sub` / `rhb_IsPoset` | realized edge; within-round order; barrier order; on the valid-event carrier; partial order |
| `rlay` / `rcomp` / `rstep` | round; sender (or own pid); `Recv?1:0` |
| `rcomp_eq_of_rhb` / `rhb_comparable_of_comp` / `rhb_rank` / `rcomp_lt_nprocs` | the `stamp_iff` structural hypotheses |
| `rhb_iff_stamp` | `rwf` ⟹ `rhb x y ↔ le_prod (nprocs-1) …` |
| `rclock` / `rclock_is_stamp` / `rhb_iff_rclock` | schedule-free clock; its coordinates; causality via it |

`RoundSemExamples.v` (test): a 3-proc/1-round system `Sdemo`, `rclock` literals, an `rhb` edge and an incomparable pair.

#### `execution/families/FrontierCompose.v` — connecting executions by a frontier: the dimension dichotomy (exported)

Abstract poset-dimension theory: composing two **antichains** by a frontier `F` gives the bipartite poset `compose_le F` (an `IsPoset` for any `F`). The dichotomy — *when does connecting two dim-2 executions by a frontier preserve dimension*: a **non-crossing** frontier preserves `dim ≤ 2`, a **crossing** (S₃) frontier raises it to `dim ≥ 3`. Both proven, admit-free.

| Name | Meaning |
|------|---------|
| `Carrier` / `compose_le` / `compose_IsPoset` | disjoint-sum carrier; the frontier-composed order (two antichains + one-way `F`); a poset for any `F` |
| `Ferrers` / `threshold_Ferrers` | non-crossing (no 2×2 crossing); a threshold frontier `φ a ≤ ψ b` is Ferrers |
| `M1` / `M2` / `threshold_dim_le2` | the explicit 2-realizer; **a threshold frontier (`F a b ⟺ φ a ≤ ψ b`, on `Fin.t` carriers) preserves `dim ≤ 2`** |
| `crownF` / `crown3` | the S₃ crown frontier `i ≠ j` on `Fin 3` + `Fin 3` |
| `crown_critical` / `crown_alt_cycle` | the three `(aᵢ,bᵢ)` critical pairs; any two form an alternating cycle |
| `crown3_dim_ge_3` / `crown3_dim_exists` / `crown3_dim_ge_3_closed` | **the crown frontier gives `dim ≥ 3`** — connecting two dim-2 antichains can raise dimension (`_closed`: crown3 *has* a dimension, via Dushnik–Miller, and it is ≥ 3) |

`FrontierComposeExamples.v` (test): a Ferrers staircase (`dim ≤ 2`) vs the crown (`¬Ferrers`, `dim ≥ 3`). Honest scope: Slice A (antichains); the positive is `threshold_dim_le2` (full `ferrers_dim_le2` needs Ferrers⟹threshold, deferred); exact `dim = 3` (3-realizer) and general dim-2 inputs (Slice B) are future work.

#### `execution/families/TransformB.v` — Transformation B (2-process block dim ≤ 2) (exported)

The NomaDB paper's second reduction: *"two processes between synchronizations form at most 2 critical pairs,"* simplified to "one local modification," preserving the dimension property. The faithful core: a block spanned by 2 processes is covered by 2 chains (each process's events are a chain under program order), so its **width ≤ 2**, hence **dim ≤ 2** (`dimension_le_width`). Being a per-block property, it is preserved under any 2-process block replacement (mirroring how Transformation A used block replacement). `TransformBExamples.v` exhibits the equal-bound (`B2` and its simplification `B2s` both ≤ 2) that drives the transformation.

| Name | Meaning |
|------|---------|
| `two_chain_cover_dim_le2` | a finite poset covered by two chains has dim ≤ 2 (via `width_exists` + `dimension_le_width` + chain/antichain pigeonhole) |
| `B2` / `B2_R` / `B2_dim_le2` | concrete 2-process block (two disjoint 2-chains, the between-syncs shape); dim ≤ 2 |
| `B2s` / `B2s_R` / `B2s_dim_le2` | the "one local modification" simplification — a single chain; dim ≤ 2 |
| `transform_B_preserves_dim2` | all blocks ≤ 2 ⇒ fully-sync execution dim ≤ 2 (`= fully_sync_dim_le2`); the block swap keeps the bound invariant |
| `transform_B_equal_bound` | (test) `B2` and `B2s` both dim ≤ 2 — the equal bound that makes the transformation dimension-preserving |

Honest caveat (as for Transformation A): the paper's inter-sync geometry is informally specified; `B2`/`B2s` are our faithful concrete realization, and "critical pairs" are formalized as the equivalent width ≤ 2 ⇒ dim ≤ 2 bound.

#### `execution_yaml/Yaml.v` — YAML file format (libnomadim) datatypes, printer, and bridges

The libnomadim on-disk format (a YAML block map: an `execution:` doc with `n_procs` + `syncs`, or a `poset:` doc with `n_vertices` + cover `edges`). This slice provides the in-memory datatypes, a byte-faithful serializer (`dump`), and bridges from each document kind to the existing model: executions become `Schedule`s, posets become finite reachability posets. The string *parser* (read direction) is in `YamlParse.v` below; OCaml-extracted real file I/O is deferred to a later slice.

| Name | Meaning |
|------|---------|
| `YamlExecution` / `YamlPoset` / `Document` | datatypes mirroring the two YAML document kinds |
| `wf_yaml_execution` | sync endpoints in-range and distinct |
| `wf_yaml_poset` | edges in-range + a strict rank witness (⇒ acyclic) |
| `string_of_nat` / `dump` | decimal printer; `dump` is byte-faithful to `data/*.yaml` |
| `schedule_of_yaml` | YAML execution ⇒ `Schedule` (each sync ⇒ a singleton frontier) |
| `Vert` / `yaml_edge` / `yaml_order` | poset carrier `{n | n < n_verts}`, listed edges, refl-trans closure |
| `yaml_order_IsPoset` | under `wf_yaml_poset`, `yaml_order` is an `IsPoset` (antisym via the rank witness) |
| `yaml_vert_finite` | the vertex carrier is `Finite` |
| `dump_*_eq` / `poset_s3_is_poset` | (test) byte-fidelity vs the real data files; S(3,1) as an actual poset |

#### `execution_yaml/YamlLex.v` + `YamlParse.v` — YAML reader (lenient, read direction)

A lenient parser `parse_document : string -> option Document` that reads real libnomadim YAML — not only our own canonical `dump` bytes, but also hand-edited / other-tool output with `#` comments, blank lines, varied indentation, flow (`[a, b]`) or compact (`[a,b]`) pairs, and extra spaces. `YamlLex.v` is the leniency layer (raw text → cleaned `Line` list); `YamlParse.v` parses fields/pairs and assembles the document. Correctness anchor: instance-level round-trip (`parse_document (dump d) = Some d`) on the three real data documents — *everything we emit, we read back exactly*. The *universal* round-trip theorem (`forall d, wf_document d -> …`) is deferred (needs `string_of_nat`↔`nat_of_digits` inversion + `split_lines`/`++` commutation).

| Name | Meaning |
|------|---------|
| `clean_lines` / `Line` | raw string ⇒ cleaned logical lines (drop blanks/comments/`\r`/trailing spaces; record indent) |
| `nat_of_digits` / `la_eqb` | lenient decimal parse; boolean `list ascii` equality |
| `parse_key_value` / `match_key` / `parse_nat_field` | split a `key: value` line; recognize a section header; read a `key: N` field |
| `parse_pair` / `parse_seq_item` | lenient `[a, b]`/`a, b`/`[a,b]` pair; a `- [a, b]` sequence item |
| `parse_document` | dispatch on `execution:` / `poset:`; assemble a `Document` |
| `roundtrip_*` / `accept_messy_*` | (test) read-back of `dump` output; acceptance of commented/re-spaced variants |

---

## nomadim (C++ tool, `nomadim/`)

A standalone C++17 port of the [NomaDimension](https://github.com/DePizzottri/NomaDimension)
tool: enumerate distributed executions of *N* processes and decide whether their
happened-before poset has order dimension ≤ 2. It is the **computational
counterpart** of the Coq `execution/` dimension theory (it does not build through
dune; see `nomadim/README.md`). Build/test/benchmark via mise:
`mise run nomadim-test` · `nomadim-test-slow` · `nomadim-bench`.

### Core library (`nomadim/include/nomadim/`, `nomadim/src/`)

| Module | Key functions / types | Meaning |
|--------|-----------------------|---------|
| `execution` | `Execution{n_procs, syncs}`, `validate()` | distributed execution = processes + ordered sync pairs |
| `process_graph` | `ProcessGraph`, `init`, `sync`, `build(Execution)` | event-structure DAG; reachability = happened-before poset |
| `floyd` | `make_graph_matrix`, `floyd`, `floyd_advance_vertex` | transitive-closure distance matrix (Floyd–Warshall) |
| `order_relation` | `StrictRel{add_and_close, less}`, `base_order`, `linearize`, `topo_order` | dense transitive-closure strict order; shared by realizer + hypergraph |
| `dimension` | `is_dim2`, `analyze_dimension`/`dimension` (→ `DimensionResult{dimension, critical_pairs, hyperedges, colorings}`, `Coloring`), `find_critical_pairs`, `check_if_critical`, `check_critical_pairs_graph`, `have_cycle`, `is_bipartite` | dim ≤ 2 ⇔ critical-pair incompatibility graph bipartite; general dim = χ of the critical-pair hypergraph (color classes are reversible sets) |
| `hypergraph` | `Caps`, `reverse_set`, `is_reversible`, `enumerate_hyperedges`, `chromatic_number`, `enumerate_min_colorings` | reversible sets, minimal alternating-cycle hyperedges, and chromatic-number coloring of the critical-pair hypergraph |
| `realizer` | `find_realizer(adjacency_list)`, `find_one_realizer`, `find_all_realizers` (→ `Coloring` list) | 2-realizer (dim ≤ 2) via incomparability orientation; general one/all minimum realizers induced by the minimum colorings of the hypergraph |
| `oracle` (test-only) | `oracle_dimension` | brute-force dimension (enumerate linear extensions → minimum realizing subset); cross-validates `analyze_dimension`; not linked into CLI/WASM |
| `wasm_bindings` | Embind module `nomadim.{js,wasm}` (`isDim2`, `findRealizer`, `criticalPairs`, `dimension`, `findOneRealizer`, `allRealizers`, `expandExecution`, `parseDocument`, `dumpPoset`, `dumpExecution`, `dumpDocument`) | JSON/YAML bridge over libnomadim for the browser editor; built with `-DNOMADIM_WASM=ON` via `mise run nomadim-editor-build`; consumed by the browser editor (`nomadim/editor/`, `mise run nomadim-editor`) (viewer + poset editing: add/remove vertices & edges, critical-pair highlight, dimension + realizers panel, notes, save) + execution swimlane view & expand-to-poset (incl. drag editing) |
| `poset` | `Poset{n_vertices, edges}`, `validate()`, `from(ProcessGraph)` | general poset by cover/adjacency relation |
| `isomorphism` | `is_isomorphic`, `generate_all_isomorphic`, `canonical_sync_name` | process-permutation isomorphism + canonical prune key |
| `enumerate` | `enumerate(n,k,threads) -> EnumerateResult`, `is_full_synchronized` | multithreaded `std::thread` work-pool enumeration of non-isomorphic dim-2 executions |
| `io` | `parse_document`, `load_file`, `dump_execution`, `dump_poset`, `dump_document`, `poset_hash`, `save_file`, `Document`, `Meta` | YAML read/write for `execution`/`poset`/`meta` documents (`meta` = notes + cached dimension/realizers keyed by `source_hash`) |

### CLI (`nomadim/app/`, binary `nomadim`)

| Subcommand | Meaning |
|------------|---------|
| `check <file.yaml>` | report whether a poset/execution has dimension ≤ 2 (exit 0 = yes, 2 = no) |
| `dimension <file.yaml> [--realizers] [--all] [--max-vertices N] [-o out]` | report general order dimension; optionally print one realizer / all minimum colorings + realizers; `-o` writes a document with computed `meta` |
| `enumerate -n N [-k K] [-j threads] [-o out]` | enumerate non-isomorphic, fully-synchronized, dim-2 executions of N processes |
| `convert <in.yaml> <out.yaml>` | expand an execution document into its poset document |

### Tests & benchmarks (`nomadim/tests/`, `nomadim/bench/`)

GoogleTest unit tests for every public function plus golden enumeration counts
(N=4,K=5 → 10; K=6 → 102; K=7 → 634; N=5,K=7 → 40; …); `bench/bench_nomadim.cpp`
(Google Benchmark) with `bench/compare.py` gating regressions against
`bench/baseline.json`.

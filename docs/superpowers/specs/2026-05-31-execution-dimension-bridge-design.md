# Execution Dimension Bridge + Concrete dim-2 — Design (Sub-project B, part 1)

**Date:** 2026-05-31
**Branch:** `execution_poset`
**Depends on:** sub-project A (`execution/` core model, complete) and the `Dimension` theory (`posets/dimension`, already a build dep of `execution/`).
**Paper:** NomaDB TechReport.

## Where this sits

Sub-project B is "reductions to sync-shape + dimension-preservation proofs". It is
research-grade and decomposed into multiple specs. **This spec is B part 1: the
dimension bridge** — connect the `ExecPoset` of sub-project A to the dimension
theory, and prove a concrete execution has dimension exactly 2, by two routes
(explicit realizer + critical-pair characterization). It is foundational: every
later preservation proof needs to talk about the dimension of an execution, and
this validates the `A ↔ dimension` link on real examples before the hard
transformation proofs.

Later B specs (out of scope here): defining sync-shape/synchronization precisely,
the reduction steps (Transformations A and B), and their critical-pair /
dimension-preservation proofs.

## Library facts this builds on (verified present)

- `DimDefs.v`: `PosetDimension d` (class: a minimum-size realizer), `IsRealizer`,
  `IsLinearExtension`, `IsTotalOrder`, `Incomparable R x y := ~(R x y \/ R y x)`,
  `Strict`.
- `Theorems.v`: `dushnik_miller_exists : forall n, cardinal A (Full_set A) n -> exists d, inhabited (PosetDimension R d)`; `dimension_is_minimum` (a field of `PosetDimension`).
- `CriticalPairs.v`: `IsCriticalPair x y` (class), `incomparable_lifting_to_critical_pair`, `critical_pair_realizer_iff` (a realizer ⟺ every critical pair is reversed by some member), `IsAlternatingCycle`, `critical_pairs_reversible_iff_no_alternating_cycle : (exists L, IsLinearExtension R L /\ forall x y, In (A*A) S (x,y) -> L y x) <-> ~(exists cycle, (forall p, In _ S p) /\ IsAlternatingCycle R cycle)`.
- From `execution/`: `ExecPoset`, `ep_carrier`, `ep_order`, `ep_size_ok` (`cardinal (ep_carrier E) (Full_set _) (ep_size E)`), `hb_IsPoset`/`hb_IsFinitePoset`, `exec_of_schedule`, `sched_n3`, `n3_concurrent`.

The dimension machinery is parametric in `(A, R)` with `IsPoset A R`; `ep_order E`
is such a relation (`hb_IsPoset`), so the machinery applies directly.

## Component 1 — bridge core (`execution/DimBridge.v`)

Reusable, low-risk. Public names fixed:

```coq
Definition exec_has_dimension (E : ExecPoset) (d : nat) : Prop :=
  inhabited (PosetDimension (ep_carrier E) (ep_order E) d).

(* every execution has a (unique) dimension *)
Lemma exec_dimension_exists :
  forall E, exists d, exec_has_dimension E d.

(* an incomparable pair forces dimension >= 2 *)
Lemma exec_dim_ge_2 :
  forall E x y, Incomparable (ep_order E) x y ->
    forall d, PosetDimension (ep_carrier E) (ep_order E) d -> 2 <= d.

(* explicit two-realizer route: a size-2 realizer + an incomparable pair give dim = 2 *)
Lemma exec_dim_eq_2_of_realizer :
  forall E,
    (exists L1 L2,
       IsLinearExtension (ep_order E) L1 /\
       IsLinearExtension (ep_order E) L2 /\
       (forall x y, ep_order E x y <-> (L1 x y /\ L2 x y))) ->
    (exists x y, Incomparable (ep_order E) x y) ->
    exec_has_dimension E 2.
```

Proof notes:
- `exec_dimension_exists`: `dushnik_miller_exists` instantiated at `(ep_carrier E, ep_order E)` with `ep_size_ok E` as the `cardinal` witness; needs the `IsPoset`/`IsFinitePoset` instances in scope (`Existing Instance hb_IsPoset`/`hb_IsFinitePoset`).
- `exec_dim_ge_2`: by contradiction. A `PosetDimension d` with `d <= 1` has a realizer of cardinal `<= 1`. If 0, `realizer_intersection` makes `ep_order E x y` hold for all `x y` (vacuous `forall L in ∅`), so by antisymmetry the carrier has `<= 1` element — contradicts a distinct incomparable pair. If 1, `ep_order E = L` for that single linear extension `L`, which is total — contradicts incomparability. (~30 lines.)
- `exec_dim_eq_2_of_realizer`: the explicit pair `{L1, L2}` (as `fun L => L = L1 \/ L = L2`) is a realizer (`realizer_linear` from the two `IsLinearExtension`; `realizer_intersection` from the given iff). The incomparable pair forces `L1 <> L2` (one orients it each way), so the realizer has cardinal 2 ⇒ via `dimension_is_minimum`, the dimension `d <= 2`. `exec_dim_ge_2` gives `d >= 2`. Combined with `exec_dimension_exists`, `d = 2`. (~60–80 lines.)

## Component 2 — critical-pair characterization interface (`execution/DimCriticalPairs.v`)

Three layers, increasing risk. The first layer + Components 1 and 3 form a complete
self-contained deliverable; the master bridge is the flagged stretch.

### Layer 2a — thin specialization (low risk)
```coq
Definition exec_critical_pair (E : ExecPoset) (x y : ep_carrier E) : Prop :=
  IsCriticalPair (ep_order E) x y.
```
Plus re-exports of `incomparable_lifting_to_critical_pair` and
`critical_pairs_reversible_iff_no_alternating_cycle` specialized to `ep_order E`
(direct instantiation of the parametric library results).

### Layer 2b — master bridge (high-risk research piece)
```coq
Lemma exec_dim_le_2_iff_no_alt_cycle :
  forall E,
    (exists d, exec_has_dimension E d /\ d <= 2)
    <->
    ~ (exists cycle,
         (forall p, List.In p cycle -> IsCriticalPair (ep_order E) (fst p) (snd p)) /\
         IsAlternatingCycle (ep_order E) cycle).
```
Proof = compose `critical_pairs_reversible_iff_no_alternating_cycle` (with
`S := all critical pairs`) with a new Dushnik–Miller step
`dim <= 2 <-> exists L (linear ext of ep_order E) reversing every critical pair`:
- (⇐) build a size-2 realizer `{L1, L2}` from a single reversing `L` (let `L2 := L`;
  `L1 :=` a linear extension keeping every critical pair un-reversed), verified a
  realizer via `critical_pair_realizer_iff`;
- (⇒) a size-2 realizer `{L1, L2}` has, for each critical pair, one member
  reversing it; the standard argument yields a single `L` reversing all.
Estimate ~150–250 lines. **If this stalls across sessions it is split into a
deferred follow-up; it must never be `Admitted`.**

## Component 3 — concrete dim-2 examples (`execution/DimExamples.v`, test-only)

Both via `exec_dim_eq_2_of_realizer`. Linear extensions are presented as
injective integer keys: `L x y := key x <= key y` for an injective, `hb`-monotone
`key : ep_carrier E -> nat`. Then `IsTotalOrder`/`IsLinearExtension` reduce to
`lia` on keys (totality, antisymmetry via injectivity, "extends `hb`" via key
monotonicity along `hb`). The intersection `hb = L1 ∩ L2`: forward is key
monotonicity; backward (`key1 x <= key1 y /\ key2 x <= key2 y -> hb x y`) is finite
per-pair case analysis, eased by first proving an explicit closed-form
characterization of `hb` for the concrete example.

1. **Minimal example** `E_min := exec_of_schedule sched_min` where
   `sched_min := {| sch_nprocs := 2; sch_frontiers := [ [(0,1)] ; [] ] |}` (4 events:
   proc0 `[Send 1; Local]`, proc1 `[Recv 0; Local]`). Order: `(0,0) ≺ (0,1),(1,0),(1,1)`,
   `(1,0) ≺ (1,1)`, with `(0,1) ∥ (1,0)` and `(0,1) ∥ (1,1)`. Two keys chosen to
   disagree exactly on the incomparable pairs (e.g. `key1`: order `(0,0),(1,0),(0,1),(1,1)`;
   `key2`: order `(0,0),(0,1),(1,0),(1,1)`). Result: `exec_has_dimension E_min 2`.
   (Built via `desugar`, so rank/acyclicity are free.)

2. **N=3 example** `exec_of_schedule sched_n3` (the paper's "N=3 always dim 2",
   6 events). Reuse `n3_concurrent` for the dim ≥ 2 witness; two injective-key
   linear extensions + intersection. Result: `exec_has_dimension (exec_of_schedule sched_n3) 2`.

## File layout, wiring, testing

- New files `execution/DimBridge.v`, `execution/DimCriticalPairs.v`,
  `execution/DimExamples.v`.
- `execution/dune`: add `DimBridge DimCriticalPairs DimExamples` to `(modules …)`.
- `_CoqProject`: add the three `execution/*.v` paths.
- `execution/Execution.v`: add `DimBridge` and `DimCriticalPairs` to the
  `Require Export` line (NOT `DimExamples`, which is test-only).
- `docs/INDEX.md`: add a "Dimension bridge" subsection under the Execution library.
- Every file builds through `.claude/scripts/timed-build.sh`; whole-`execution`
  and `@all` green; **zero `Admitted`** (deferred items are split out, not admitted).
- `Print Assumptions` audit on the two `exec_has_dimension … 2` results — expected
  to depend only on the standard classical axioms already used by
  `PosetDimension`/`dushnik_miller_exists` (`classic`, `proof_irrelevance`,
  `constructive_definite_description`, `Extensionality_Ensembles`); recorded, not a
  blocker.
- Files kept <500 lines, each `Qed` <5 min, per `coq-fast-compile`.

## Acceptance criteria

1. `DimBridge.v` builds: `exec_has_dimension`, `exec_dimension_exists`,
   `exec_dim_ge_2`, `exec_dim_eq_2_of_realizer`, zero admits.
2. `DimCriticalPairs.v` builds: layer 2a definitions + specialized re-exports;
   the master bridge `exec_dim_le_2_iff_no_alt_cycle` proven, OR explicitly split
   into a tracked follow-up (with layer 2a still delivered) — never admitted.
3. `DimExamples.v` builds: `exec_has_dimension E_min 2` and
   `exec_has_dimension (exec_of_schedule sched_n3) 2`, zero admits.
4. Whole-project build green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later B specs)

Sync-shape/synchronization definitions, the reduction steps (Transformations A/B),
dimension-preservation proofs, and computing dimensions of general (non-example)
executions.

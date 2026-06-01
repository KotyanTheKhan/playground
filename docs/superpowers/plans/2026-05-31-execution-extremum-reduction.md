# Execution Extremum Reduction — Implementation Plan (Sub-project B, part 3, slice 2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. Proof bodies give a strategy. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Prove that removing a global extremum from an execution poset preserves `dim ≤ 2` (exact dimension, via realizer surgery), and demonstrate it on `E_min`.

**Architecture:** Two new modules in the `Execution` theory: `ExtremumReduction` (`IsGlobalMin`/`IsGlobalMax` + the `remove_min`/`remove_max` preservation theorems; the substantive proof is the backward realizer surgery that adds the extremum back to a block realizer) and `ExtremumReductionExamples` (concrete `E_min` instance, test-only).

**Tech Stack:** Coq/Rocq 9.1; `Dimension` (`DimDefs`, `Theorems` for `cardinal_Im_injective`); execution `Poset`, `DimBridge`, `Ordinal`, `Reduction`, `DimExamples`; Stdlib `Ensembles`/`Image`/`ProofIrrelevance`/`FunctionalExtensionality`/`PropExtensionality`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/ExtremumReduction.v` | `IsGlobalMin`/`IsGlobalMax`; `remove_min_preserves_dim2`/`remove_max_preserves_dim2` (forward via the reduction framework; backward via realizer surgery). |
| `execution/ExtremumReductionExamples.v` | `E_min_a_global_min`, `E_min_remove_min_dim2`, `E_min_block_dim_le_2_via_extremum` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `IsGlobalMin`, `IsGlobalMax`, `remove_min_preserves_dim2`, `remove_max_preserves_dim2`, `E_min_a_global_min`, `E_min_remove_min_dim2`, `E_min_block_dim_le_2_via_extremum`.

---

## Task E0: Scaffold

**Files:** create `execution/ExtremumReduction.v`, `execution/ExtremumReductionExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the two stubs.
- [ ] **Step 2:** Add `ExtremumReduction`, `ExtremumReductionExamples` to the `(modules …)` list in `execution/dune`.
- [ ] **Step 3:** Add the two `.v` paths to `_CoqProject` (after the reduction-framework entries).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/ExtremumReduction.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/ExtremumReduction.v execution/ExtremumReductionExamples.v execution/dune _CoqProject
git commit -m "scaffold execution extremum-reduction modules"
```

---

## Task E1: Extremum predicates + `remove_min_preserves_dim2` (`ExtremumReduction.v`)

**Files:** `execution/ExtremumReduction.v`

This is the substantive task. The backward direction (Steps 4–7) is the realizer surgery.

- [ ] **Step 1: Imports + predicates + forward direction skeleton**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Reduction.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition IsGlobalMin (E : ExecPoset) (m : ep_carrier E) : Prop :=
  forall x, ep_order E m x.
Definition IsGlobalMax (E : ExecPoset) (m : ep_carrier E) : Prop :=
  forall x, ep_order E x m.
```

- [ ] **Step 2: Build (predicates compile)** — `bash .claude/scripts/timed-build.sh 120 execution/ExtremumReduction.vo 2`. Exit 0.

- [ ] **Step 3: State the theorem and prove the FORWARD direction**

```coq
Lemma remove_min_preserves_dim2 :
  forall E m, IsGlobalMin E m ->
    ((exists d, inhabited (PosetDimension (sub_order E (fun x => x <> m)) d) /\ d <= 2)
     <->
     (exists d, exec_has_dimension E d /\ d <= 2)).
```
Forward (`-> ... -> exec dim2`, i.e. the `<-` of the iff: from `E` dim2 to block dim2 — wait, orient carefully): the iff is `(block dim2) <-> (E dim2)`.
- `(E dim2) -> (block dim2)` (the EASY half): `subposet_reduces_dim (ep_carrier E) (ep_order E) (fun x => x <> m)` gives `ReducesDim (sub_order E (fun x => x<>m)) (ep_order E)`; then `reduces_dim2` needs `(exists dR, inhabited (PosetDimension (block) dR))` (from `subposet_dimension_le` applied to `E`'s dimension, or `dushnik_miller_exists` on the finite block) and the `E` dim2 hypothesis, yielding block dim2. Prove this half fully now; leave the other half (`admit` is NOT allowed — instead structure the `split` so this half is `Qed`-able and the backward half is the next steps). Implement the whole `split` but develop the backward half in Steps 4–7 before the final `Qed`.

(Implementation note: write the lemma with `split.` and complete BOTH halves before `Qed`. The forward half is short; the backward half is the surgery below. Do not commit a partial proof.)

- [ ] **Step 4: The lifted linear extension**

For the backward half, define (locally, inside the proof or as a top-level helper above the lemma):
```coq
(* Lift a linear extension LB of the (remove m) block to a linear extension of E,
   placing m at the bottom. *)
Definition lift_min (E : ExecPoset) (m : ep_carrier E)
   (LB : {z | z <> m} -> {z | z <> m} -> Prop)
   (a b : ep_carrier E) : Prop :=
   a = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).
```
(`lift_min … a m` reduces to `a = m`; `lift_min … m b` is always true.)

- [ ] **Step 5: `lift_min` is a linear extension of `ep_order E`**

Prove a helper (above the lemma; `Context`/explicit args as convenient):
```coq
Lemma lift_min_is_linext :
  forall E m (LB : {z | z <> m} -> {z | z <> m} -> Prop),
    IsGlobalMin E m ->
    IsLinearExtension (sub_order E (fun x => x <> m)) LB ->
    IsLinearExtension (ep_order E) (lift_min E m LB).
```
Strategy (`refine {| linear_is_total := _ ; linear_extends := _ |}` then `{| total_is_poset := _ ; total_comparable := _ |}`):
- `total_comparable a b`: `destruct (classic (a = m))`, `destruct (classic (b = m))`. `a=m`: `left` (lift m b). `b=m, a<>m`: `right` (lift b a = lift m... wait b=m so lift _ b a is left disjunct). both `<>m`: `LB`'s `total_comparable` on `(exist a)(exist b)` gives the two cases → the `LB` disjunct of `lift a b` or `lift b a`.
- `IsPoset (lift_min …)`: refl (`a=m`→left; else `LB` refl, needs `exists (Ha)(Ha), LB (exist a Ha)(exist a Ha)` = `LB` refl on `exist a Ha` — use `proof_irrelevance` so the two `Ha` match). antisym: `lift a b` and `lift b a`. If `a=m` and `b=m` then `a=b`. If `a=m, b<>m`: `lift b a` with `b<>m,a=m`: `lift b a = (b=m? no) \/ (exists Hb:b<>m, Ha:a<>m=m<>m false...)` → `lift b a` requires `a<>m` for the second disjunct (Hb' : a <> m) which is false (a=m) → `lift b a` is false → contradiction with hypothesis `lift b a`. So `a=m,b<>m` can't have both `lift a b` and `lift b a`. Symmetric. both `<>m`: `LB` antisym gives `exist a = exist b` → `a = b` (`proj1_sig`). trans: case split; `m` at bottom composes; off-`m` via `LB` trans; mixed cases use that `m` is below all.
- `linear_extends a b : ep_order E a b -> lift_min E m LB a b`: `destruct (classic (a = m))`; `a=m`→`left`. else `a<>m`; show `b<>m`: if `b=m` then `ep_order E a m`; `IsGlobalMin` gives `ep_order E m a`; `poset_antisym` ⇒ `a=m`, contra. So `b<>m`; `right; exists Ha, Hb`; apply `LB`'s `linear_extends` to `(exist a Ha)(exist b Hb)` — note `sub_order E (fun x=>x<>m) (exist a Ha)(exist b Hb) = ep_order E a b` (definitional), which holds.

- [ ] **Step 6: `lift_min` injectivity + the lifted realizer**

```coq
Lemma lift_min_inj :
  forall E m (LB1 LB2 : {z | z <> m} -> {z | z <> m} -> Prop),
    lift_min E m LB1 = lift_min E m LB2 -> LB1 = LB2.
```
Strategy: `intros … Heq`. `extensionality x; extensionality y` (`FunctionalExtensionality`). `x = exist _ a Ha`, `y = exist _ b Hb` (destruct). Need `LB1 x y = LB2 x y`. From `Heq` at `(a,b)` (both `<>m`): `lift_min … LB1 a b = lift_min … LB2 a b`. The `a=m` disjunct is false (`a<>m` from `Ha`), so both reduce to `exists Ha' Hb', LBi (exist a Ha')(exist b Hb')`; by `proof_irrelevance` `Ha'=Ha`, `Hb'=Hb`, so this is `LBi x y`. Use `propositional_extensionality` to turn the `=` of Props into `<->` and back. Conclude `LB1 x y = LB2 x y`.

- [ ] **Step 7: Finish the backward direction (the surgery)**

Inside `remove_min_preserves_dim2`'s backward half: given `[d [ [RBdim] Hle ]]` (a block dimension `d ≤ 2` with `RBdim : PosetDimension (sub_order E (fun x=>x<>m)) d`):
- `RB := dimension_realizer RBdim`, `HRBreal := dimension_is_realizer RBdim`, `HRBcard := dimension_cardinality RBdim`.
- `RE := Im _ _ RB (lift_min E m)`.
- `IsRealizer (ep_order E) RE`:
  - `realizer_linear`: a member is `lift_min E m LB` for `LB ∈ RB`; `realizer_linear HRBreal` gives `IsLinearExtension (sub_order …) LB`; `lift_min_is_linext` gives the lift is a linear extension. (`In _ RE` membership: `inversion` the `Im`.)
  - `realizer_intersection a b`: `ep_order E a b <-> forall LE ∈ RE, LE a b`. Forward: `a=m` → all `lift m b` true (left disjunct), and goal `ep_order E a b` — but careful, forward is `ep_order E a b -> ...`; given `ep_order E a b`, each `LE = lift LB`, and `lift LB a b` holds: `a=m`→left; else `b<>m` (as in Step 5) and `LB`'s `linear_extends` on the block order `= ep_order E a b`. Backward: `(forall LE∈RE, LE a b) -> ep_order E a b`. `destruct (classic (a=m))`: `a=m` → `ep_order E m b` by `IsGlobalMin`. else `a<>m`; show `b<>m`: instantiate the hypothesis at some `LE` (RB nonempty? if `RB` empty then `d=0`; handle: if `d=0`, the block is ≤1 element; then `E` has ≤2 elements and the goal... — simpler: get `b<>m` from: if `b=m`, pick any `LE∈RE`; `LE a m = (a=m)` = false (a<>m), contradicting `LE a m` from the hypothesis — but need RE nonempty. If RE empty (d=0), `forall LE∈∅` is vacuous so hypothesis gives nothing; then handle `d=0` separately: `d=0` ⇒ block realizer empty ⇒ block relation universal ⇒ block ≤1 element ⇒ `E` is `m` + ≤1 other ⇒ `ep_order E a b` decidable directly. To avoid this, FIRST case-split `destruct d`; `d=0` is a small special case (`E` has ≤ 2 elements, a chain, every pair comparable with `m` at bottom — `ep_order E a b` holds whenever needed); `d>=1` ⇒ RE nonempty, use the instantiation argument). After `b<>m`: each `LE a b = lift LB a b` reduces (a,b≠m) to `LB (exist a)(exist b)`; so `forall LB∈RB, LB (exist a)(exist b)`; `realizer_intersection HRBreal` gives `sub_order … (exist a)(exist b)` = `ep_order E a b`.
  - cardinal: `cardinal _ RE d` via `cardinal_Im_injective _ _ RB (lift_min E m) d HRBcard (lift_min_inj …)` (the injectivity restricted to `In RB`).
- Conclude: `destruct (exec_dimension_exists E) as [dE [HdE]]`; `dimension_is_minimum HdE RE d (IsRealizer) (cardinal) : dE <= d`; with `Hle : d <= 2`, `dE <= 2`; `exists dE; split; [exact (inhabits HdE) | lia]`. (`exec_has_dimension E dE = inhabited (PosetDimension … dE)`.)

The `d = 0` special case: a `PosetDimension (block) 0` means the block's relation is the universal relation (empty realizer), forcing the block to have ≤ 1 element (`poset_antisym`); then `ep_carrier E` has ≤ 2 elements (`m` + ≤1), so `ep_order E` is a chain — give a direct size-≤1 realizer of `E` (any single linear extension, or note `dim E ≤ 1 ≤ 2`). Keep this branch short; if it balloons, factor `block_dim0_means_E_dim_le_2` as a helper.

- [ ] **Step 8: `remove_max_preserves_dim2`** — the dual (append `m` at top): `lift_max LB a b := b = m \/ (exists Ha Hb, LB …)`; symmetric helpers `lift_max_is_linext`, `lift_max_inj`; same realizer argument. (If the file approaches 500 lines, move `max` to a helper file `execution/ExtremumReductionMax.v`, wired the same way.)

- [ ] **Step 9: Build** — `bash .claude/scripts/timed-build.sh 600 execution/ExtremumReduction.vo 1`. Exit 0; `grep -nE "Admitted|admit|Axiom" execution/ExtremumReduction.v` empty.
- [ ] **Step 10: Commit** — `git add execution/ExtremumReduction.v && git commit -m "feat(execution): removing a global extremum preserves dim<=2 (realizer surgery)"`.

---

## Task E2: Concrete `E_min` instance (`ExtremumReductionExamples.v`)

**Files:** `execution/ExtremumReductionExamples.v`

- [ ] **Step 1: Imports + the three examples**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal Reduction
                              DimExamples ExtremumReduction.

Example E_min_a_global_min : IsGlobalMin E_min ev_a.

Example E_min_remove_min_dim2 :
  (exists d, inhabited (PosetDimension (sub_order E_min (fun x => x <> ev_a)) d) /\ d <= 2)
  <->
  (exists d, exec_has_dimension E_min d /\ d <= 2).

Example E_min_block_dim_le_2_via_extremum :
  exists d, inhabited (PosetDimension (sub_order E_min (fun x => x <> ev_a)) d) /\ d <= 2.
```
(Use `ev_a` from `DimExamples.v` — the concrete `(0,0)` event. If `ev_a` is not exported, reconstruct it as `exist _ (0,0) <proof>` and the `hb_a_*` facts inline.)

Strategies:
- `E_min_a_global_min`: `intro x`. By `valid_event_min_cases x`, `proj1_sig x` is one of `(0,0),(0,1),(1,0),(1,1)`. Goal `ep_order E_min ev_a x`. For `(0,0)`: `x = ev_a` (via `eq_ev_a`/`proof_irrelevance`), `ep_order` is refl. For the others: canonicalize `x` to `ev_b`/`ev_c`/`ev_d` and apply `hb_a_b`/`hb_a_c`/`hb_a_d`. (Reuse the `DimExamples.v` helpers exactly as `FrontierExamples.v` did.)
- `E_min_remove_min_dim2`: `exact (remove_min_preserves_dim2 E_min ev_a E_min_a_global_min)`.
- `E_min_block_dim_le_2_via_extremum`: `apply (proj1 E_min_remove_min_dim2)` is the wrong direction; use `apply (proj2 E_min_remove_min_dim2)` — wait orient: the iff is `(block dim2) <-> (E dim2)`. We want to CONCLUDE `block dim2` from `E dim2`. So `apply (proj2 E_min_remove_min_dim2)` if `proj2 : (E dim2) -> (block dim2)`; check the iff orientation (`A <-> B`, `proj1 : A -> B`, `proj2 : B -> A`; here `A = block dim2`, `B = E dim2`, so `proj2 : (E dim2) -> (block dim2)`). Supply `(E dim2)`: `exists 2; split; [exact E_min_dim_2 | lia]`.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/ExtremumReductionExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/ExtremumReductionExamples.v && git commit -m "test(execution): E_min global-min removal preserves dim<=2"`.

---

## Task E3: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `ExtremumReduction` to the `Require Export` line in `execution/Execution.v` (NOT the examples; nor a `Max` helper file if you split one — export `ExtremumReduction` which re-exports it, or add it explicitly).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 600 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions remove_min_preserves_dim2.` to `execution/ExtremumReduction.v` and `Print Assumptions E_min_block_dim_le_2_via_extremum.` to `execution/ExtremumReductionExamples.v`; build, read the axiom blocks (expect only standard classical/choice axioms — `classic`, `proof_irrelevance`, `functional_extensionality*`, `propositional_extensionality`, `constructive_definite_description`, `relational_choice`, `Extensionality_Ensembles`), then `git checkout -- execution/ExtremumReduction.v execution/ExtremumReductionExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add an "Extremum reduction" subsection: `IsGlobalMin`/`IsGlobalMax`, `remove_min_preserves_dim2`/`remove_max_preserves_dim2` (ExtremumReduction.v); `E_min_a_global_min`/`E_min_remove_min_dim2`/`E_min_block_dim_le_2_via_extremum` (ExtremumReductionExamples.v). Match existing table style.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export extremum reduction; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (predicates + `remove_min`/`remove_max`) → E1; Component 2 (concrete `E_min`) → E2; wiring/testing/audit → E0 + E3. All mapped.
- **The realizer surgery (E1 Steps 4–7) is the one substantive proof**, structurally like the `LP` construction (`Ordinal.v`) and `dimension_iso` (`DimIso.v`) — the implementer has those as references.
- **`d = 0` edge case** is explicitly called out (E1 Step 7) — block-dim-0 ⇒ `E` ≤2 elements ⇒ `dim E ≤ 1 ≤ 2`.
- **Name consistency:** `IsGlobalMin`/`IsGlobalMax`, `remove_min_preserves_dim2`/`remove_max_preserves_dim2`, `lift_min`/`lift_max`, `sub_order E (fun x => x <> m)` (the block) used consistently; the iff orientation `(block dim2) <-> (E dim2)` is fixed.
- **Reused (confirmed present):** `subposet_reduces_dim`/`reduces_dim2` (Reduction), `sub_order`/`posdim_unique` (Ordinal), `cardinal_Im_injective` (Theorems/LinearSum), `exec_dimension_exists`/`E_min_dim_2` (DimBridge/DimExamples), `ev_a`/`hb_a_*`/`valid_event_min_cases`/`eq_ev_*` (DimExamples).
- **Execution-time checks:** `About cardinal_Im_injective` (arg order), whether `ev_a`/`hb_a_*` are exported from `DimExamples.v` (else reconstruct inline), the iff orientation in `E_min_block_dim_le_2_via_extremum`.

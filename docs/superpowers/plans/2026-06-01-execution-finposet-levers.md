# Generic Finite-Poset Dimension Levers — Implementation Plan (n-way slice 1 of 2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.
>
> **Nature of this slice:** a carrier-abstracted PORT of three existing, building proofs onto bare finite posets `(A,R)` with `IsPoset A R` + `Finite (Full_set A)`. For each ported lemma, READ the named source proof first and transcribe it with the carrier abstracted (`ep_carrier E ↦ A`, `ep_order E ↦ R`, `sub_order E ↦ fin_sub_order`, `exec_has_dimension E d ↦ inhabited (PosetDimension R d)`, `exec_dimension_exists E ↦ fin_dim_exists`, `ExecPoset` finiteness ↦ the `Hfin` hypothesis). The underlying library lemmas (`dimension_iso`, `linear_sum_dimension`, `dushnik_miller_exists`, `cardinal_Im_injective`, `subtype_is_poset`) are already fully generic.

**Goal:** Restate and prove the dimension-preservation lever chain on bare finite posets, so the n-way iteration (slice 2) can recurse into sub-posets that are not `ExecPoset`s.

**Architecture:** New generic module(s) in the `Execution` theory: `FinPosetDim.v` (predicates + lemmas; possibly split with `FinPosetDimSurgery.v` for the realizer surgery) and `FinPosetDimExamples.v` (the `E_min` consistency check, test-only). Existing `ExecPoset` lemmas are left UNCHANGED.

**Tech Stack:** Coq/Rocq 9.1; `Posets` (`PosetClasses`, `FinitePoset`); `Dimension` (`DimDefs`, `Theorems`, `LinearSum`, `CriticalPairs`); execution `DimIso`; Stdlib `Ensembles`/`Finite_sets`/`Finite_sets_facts`/`Image`/`ProofIrrelevance`/`FunctionalExtensionality`/`PropExtensionality`/`ClassicalDescription`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/FinPosetDim.v` | `fin_sub_order`, `fin_global_min/max`, `fin_is_barrier`, `fin_dim_exists`, `fin_block_dim0_global_min/max`, `fin_barrier_dimension`, `fin_barrier_dim_le2`; imports the surgery file. |
| `execution/FinPosetDimSurgery.v` | `fin_lift_min/max`, `fin_remove_min_dim2`/`fin_remove_max_dim2` (the realizer surgery; the heavy ~250-line port). |
| `execution/FinPosetDimExamples.v` | `fin_chain_reproduces_E_min` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Decision: split the surgery into `FinPosetDimSurgery.v` from the start (it is the heavy part; keeping `FinPosetDim.v` focused avoids a 500-line file). `FinPosetDim.v` imports `FinPosetDimSurgery`.

Canonical names (verbatim): `fin_sub_order`, `fin_global_min`, `fin_global_max`, `fin_is_barrier`, `fin_dim_exists`, `fin_lift_min`, `fin_lift_max`, `fin_remove_min_dim2`, `fin_remove_max_dim2`, `fin_block_dim0_global_min`, `fin_block_dim0_global_max`, `fin_barrier_dimension`, `fin_barrier_dim_le2`, `fin_chain_reproduces_E_min`.

**Sectioning convention (all of FinPosetDim.v and FinPosetDimSurgery.v):** wrap the
generic content in
```coq
Section FinPoset.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).
  ...
End FinPoset.
```
so every lemma takes `(A) R {HR} (Hfin)` after the section closes. `fin_sub_order`/
`fin_global_*`/`fin_is_barrier` go inside the section too (they reference `R`).

---

## Task G0: Scaffold

**Files:** create `execution/FinPosetDimSurgery.v`, `execution/FinPosetDim.v`, `execution/FinPosetDimExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the three stubs.
- [ ] **Step 2:** Add `FinPosetDimSurgery`, `FinPosetDim`, `FinPosetDimExamples` to the `(modules …)` list in `execution/dune`.
- [ ] **Step 3:** Add the three `.v` paths to `_CoqProject` (after the barrier-dim2 entries; `FinPosetDimSurgery` before `FinPosetDim` before `FinPosetDimExamples`).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/FinPosetDimSurgery.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/FinPosetDimSurgery.v execution/FinPosetDim.v execution/FinPosetDimExamples.v execution/dune _CoqProject
git commit -m "scaffold generic finite-poset dimension lever modules"
```

---

## Task G1: Predicates + realizer surgery (`FinPosetDimSurgery.v`)

**Files:** `execution/FinPosetDimSurgery.v`

**READ FIRST:** `execution/ExtremumReduction.v` in full — this task ports its
`lift_min`/`lift_max`, `lift_min_is_linext`/`lift_max_is_linext`,
`lift_min_inj`/`lift_max_inj`, `small_E_dim_le_2`, and
`remove_min_preserves_dim2`/`remove_max_preserves_dim2` onto `(A, R, Hfin)`.

- [ ] **Step 1: Imports + section + generic predicates**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.

Section FinPoset.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  Definition fin_sub_order (S : Ensemble A)
    : {z | Ensembles.In _ S z} -> {z | Ensembles.In _ S z} -> Prop :=
    fun x y => R (proj1_sig x) (proj1_sig y).

  Instance fin_sub_order_poset (S : Ensemble A) : IsPoset _ (fin_sub_order S) :=
    subtype_is_poset R S.

  Definition fin_global_min (m : A) : Prop := forall x, R m x.
  Definition fin_global_max (m : A) : Prop := forall x, R x m.

  (* every finite poset has a dimension *)
  Lemma fin_dim_exists : exists d, inhabited (PosetDimension R d).
End FinPoset.
```
`fin_dim_exists` proof: `destruct (finite_cardinal _ _ Hfin) as [n Hn]`; `exact (dushnik_miller_exists n Hn)` (the `IsPoset` is `HR`; `dushnik_miller_exists : forall n, cardinal A (Full_set A) n -> exists d, inhabited (PosetDimension R d)`). Confirm shape with `About dushnik_miller_exists`.

NOTE: keep `fin_global_min/max` and `fin_dim_exists` inside the section (they need `R`/`Hfin`); `fin_sub_order` and `fin_sub_order_poset` too. After `End FinPoset.`, these take `R {HR} (Hfin)` leading args as appropriate.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 120 execution/FinPosetDimSurgery.vo 2`. Exit 0.

- [ ] **Step 3: `fin_lift_min` + the global-min surgery** (port of `ExtremumReduction.v`)

Re-open the section (or keep one section for the whole file). Port verbatim, abstracting the carrier:

```coq
Definition fin_lift_min (m : A) (LB : {z | z <> m} -> {z | z <> m} -> Prop)
   (a b : A) : Prop :=
   a = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).

Lemma fin_lift_min_is_linext :
  forall m (LB : {z | z <> m} -> {z | z <> m} -> Prop),
    fin_global_min m ->
    IsLinearExtension (fin_sub_order (fun x => x <> m)) LB ->
    IsLinearExtension R (fin_lift_min m LB).

Lemma fin_lift_min_inj :
  forall m (LB1 LB2 : {z | z <> m} -> {z | z <> m} -> Prop),
    fin_lift_min m LB1 = fin_lift_min m LB2 -> LB1 = LB2.

(* small case: if R is total (block had dim 0), dim R <= 1 <= 2 *)
Lemma fin_small_dim_le_2 :
  (forall a b : A, R a b \/ R b a) ->
    exists d, inhabited (PosetDimension R d) /\ d <= 2.

Lemma fin_remove_min_dim2 :
  forall m, fin_global_min m ->
    ((exists d, inhabited (PosetDimension (fin_sub_order (fun x => x <> m)) d) /\ d <= 2)
     <-> (exists d, inhabited (PosetDimension R d) /\ d <= 2)).
```
Port the proofs of `lift_min_is_linext`, `lift_min_inj`, `small_E_dim_le_2`,
`remove_min_preserves_dim2` from `ExtremumReduction.v` with the substitutions:
`IsGlobalMin E m ↦ fin_global_min m`, `ep_order E ↦ R`, `sub_order E ↦ fin_sub_order`,
`exec_has_dimension E d ↦ inhabited (PosetDimension R d)`,
`exec_dimension_exists E ↦ fin_dim_exists R Hfin` (or however it resolves in-section —
inside the section `fin_dim_exists` is available with `R`/`Hfin` implicit/in scope),
`poset_refl`/`poset_antisym` use the `HR` instance, and the realizer-surgery's
`cardinal_Im_injective` step is unchanged. `fin_small_dim_le_2` ports `small_E_dim_le_2`
(its singleton realizer `Singleton R` argument is carrier-generic; the `dimension_is_minimum`
+ `fin_dim_exists` finish is identical).

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinPosetDimSurgery.vo 1`. Exit 0; zero admits.

- [ ] **Step 5: `fin_lift_max` + the global-max surgery** (dual port)

```coq
Definition fin_lift_max (m : A) (LB : {z | z <> m} -> {z | z <> m} -> Prop)
   (a b : A) : Prop :=
   b = m \/ (exists (Ha : a <> m) (Hb : b <> m), LB (exist _ a Ha) (exist _ b Hb)).

Lemma fin_lift_max_is_linext : (* analogous to fin_lift_min_is_linext, fin_global_max *)
  forall m (LB : _), fin_global_max m ->
    IsLinearExtension (fin_sub_order (fun x => x <> m)) LB ->
    IsLinearExtension R (fin_lift_max m LB).
Lemma fin_lift_max_inj : (* analogous *)
  forall m (LB1 LB2 : _), fin_lift_max m LB1 = fin_lift_max m LB2 -> LB1 = LB2.
Lemma fin_remove_max_dim2 :
  forall m, fin_global_max m ->
    ((exists d, inhabited (PosetDimension (fin_sub_order (fun x => x <> m)) d) /\ d <= 2)
     <-> (exists d, inhabited (PosetDimension R d) /\ d <= 2)).
```
Port `lift_max_*`/`remove_max_preserves_dim2` from `ExtremumReduction.v` analogously.

- [ ] **Step 6: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinPosetDimSurgery.vo 1`. Exit 0; zero admits. If 124, the file is too big — move `fin_remove_max_dim2` + its `fin_lift_max_*` helpers into a third file `execution/FinPosetDimSurgeryMax.v` (wire it in) and keep min here.
- [ ] **Step 7: Commit** — `git add execution/FinPosetDimSurgery.v && git commit -m "feat(execution): generic finite-poset extremum-removal surgery"`.

---

## Task G2: Barrier levers (`FinPosetDim.v`)

**Files:** `execution/FinPosetDim.v`

**READ FIRST:** `execution/Ordinal.v` (`barrier_dimension`/`barrier_dimension_section`) and `execution/BarrierDim2.v` (`block_dim0_global_min/max`, `barrier_dim_le2`) — this task ports them.

- [ ] **Step 1: Imports + `fin_is_barrier` + `fin_barrier_dimension`**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality
                          ClassicalDescription.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems LinearSum.
From Execution Require Import DimIso FinPosetDimSurgery.

Section FinPosetBarrier.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  Definition fin_is_barrier (L U : Ensemble A) : Prop :=
    (forall x, Ensembles.In _ L x \/ Ensembles.In _ U x) /\
    (forall x, ~ (Ensembles.In _ L x /\ Ensembles.In _ U x)) /\
    (exists x, Ensembles.In _ L x) /\ (exists y, Ensembles.In _ U y) /\
    (forall x y, Ensembles.In _ L x -> Ensembles.In _ U y -> R x y).

  Lemma fin_barrier_dimension :
    forall L U, fin_is_barrier L U -> forall dL dU d,
      PosetDimension (fin_sub_order R L) dL ->
      PosetDimension (fin_sub_order R U) dU ->
      PosetDimension R d -> 0 < dL -> 0 < dU -> d = Nat.max dL dU.
End FinPosetBarrier.
```
(Note `fin_sub_order` is defined in `FinPosetDimSurgery.v` and after its section takes
`R` as a leading arg — hence `fin_sub_order R L`. If it was defined with `R` as a
section variable so it reads `fin_sub_order L` in-section, match that; check the actual
signature with `About fin_sub_order` after G1 and keep G2 consistent.)

Port `barrier_dimension_section` from `Ordinal.v`: build the order-iso to the
`LinearSumRel` of the two blocks (the `bd_f`/`bd_g`/`bd_iso` construction, carrier
abstracted to `A`/`R`/`fin_sub_order`), transport via `dimension_iso`, finish with
`linear_sum_dimension`. The `ClassicalDescription.excluded_middle_informative` for the
`In L`/`In U` split is carrier-generic.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinPosetDim.vo 1`. Exit 0.

- [ ] **Step 3: `fin_block_dim0_global_min/max`** (port of `BarrierDim2.v`)

```coq
Lemma fin_block_dim0_global_min :
  forall L U, fin_is_barrier R L U ->
    PosetDimension (fin_sub_order R L) 0 ->
    exists m, fin_global_min R m /\ (forall x, Ensembles.In _ U x <-> x <> m).
Lemma fin_block_dim0_global_max :
  forall L U, fin_is_barrier R L U ->
    PosetDimension (fin_sub_order R U) 0 ->
    exists m, fin_global_max R m /\ (forall x, Ensembles.In _ L x <-> x <> m).
```
Port `block_dim0_global_min/max` from `BarrierDim2.v`: empty-realizer (`cardinalO_empty`
on `dimension_cardinality`) ⟹ `fin_sub_order R L` universal ⟹ all `L` elements equal
the inhabited witness `m` ⟹ `fin_global_min m` (via cover + barrier `Hbelow`) and
`U = {x | x <> m}` (cover + disjoint). Identical structure, carrier abstracted.

- [ ] **Step 4: `fin_barrier_dim_le2`** (port of `BarrierDim2.v`'s `barrier_dim_le2`)

```coq
Lemma fin_barrier_dim_le2 :
  forall L U, fin_is_barrier R L U ->
    (exists d, inhabited (PosetDimension (fin_sub_order R L) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension (fin_sub_order R U) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension R d) /\ d <= 2).
```
Port the 3-case proof: extract `dL`, `dU`; `destruct dL`.
- `dL = 0`: `fin_block_dim0_global_min` gives `m` + `U = {x|x<>m}`; rewrite `U` (functional+propositional extensionality from the `<->`); `apply (proj1 (fin_remove_min_dim2 R Hfin m Hmin))` with the `U`-hypothesis. (Confirm `fin_remove_min_dim2` orientation/args via `About`.)
- `dL = S _`, `dU = 0`: symmetric via `fin_block_dim0_global_max` + `fin_remove_max_dim2`.
- both `> 0`: `fin_dim_exists R Hfin` gives `d`; `fin_barrier_dimension … (Nat.lt_0_succ _)(Nat.lt_0_succ _)`; `lia`.

- [ ] **Step 5: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinPosetDim.vo 1`. Exit 0; zero admits.
- [ ] **Step 6: Commit** — `git add execution/FinPosetDim.v && git commit -m "feat(execution): generic finite-poset barrier dim<=2 lever"`.

---

## Task G3: Consistency check (`FinPosetDimExamples.v`)

**Files:** `execution/FinPosetDimExamples.v`

- [ ] **Step 1: The `E_min` reproduction**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FinPosetDimSurgery FinPosetDim
                              DimExamples FrontierExamples.

#[local] Existing Instance hb_IsPoset.

Example fin_chain_reproduces_E_min :
  exists d, inhabited (PosetDimension (ep_order E_min) d) /\ d <= 2.
```
Strategy:
- `Hfin : Finite (ep_carrier E_min) (Full_set _)`: `apply (cardinal_finite _ _ (ep_size E_min)); exact (ep_size_ok E_min)` (or `cardinal_finite … (ep_size_ok E_min)`; confirm `cardinal_finite` arg shape).
- `apply (fin_barrier_dim_le2 (ep_order E_min) Hfin Lmin Umin)`. First the `fin_is_barrier (ep_order E_min) Lmin Umin` argument: build it from `E_min_barrier : IsBarrier E_min Lmin Umin` — the two conjunctions are identical up to `ep_order E_min`/`R`, so `destruct E_min_barrier` and re-`split`/assemble the five components (cover, disjoint, inhabited, inhabited, Hbelow). (If `IsBarrier E_min Lmin Umin` is *definitionally* `fin_is_barrier (ep_order E_min) Lmin Umin`, `exact E_min_barrier` works; otherwise reassemble.)
- Two block goals `exists d, inhabited (PosetDimension (fin_sub_order (ep_order E_min) S) d) /\ d <= 2` for `S ∈ {Lmin, Umin}`: `fin_sub_order (ep_order E_min) S` is definitionally `sub_order E_min S`; reuse the `E_min_block_dim2`-style derivation (`subposet_dimension_le (ep_order E_min) S 2 Hd2` with `Hd2` from `E_min_dim_2`). If the elaborator balks at `fin_sub_order` vs `sub_order`, `unfold fin_sub_order, sub_order` / `change`.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/FinPosetDimExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/FinPosetDimExamples.v && git commit -m "test(execution): generic lever chain reproduces E_min dim<=2"`.

---

## Task G4: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `FinPosetDimSurgery FinPosetDim` to the `Require Export` line in `execution/Execution.v` (and `FinPosetDimSurgeryMax` if G1 split it); NOT the examples.
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 600 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions fin_barrier_dim_le2.` to `execution/FinPosetDim.v` and `Print Assumptions fin_chain_reproduces_E_min.` to `execution/FinPosetDimExamples.v`; build, read the axiom blocks (expect only standard classical/choice axioms), then `git checkout -- execution/FinPosetDim.v execution/FinPosetDimExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "Generic finite-poset dimension levers" subsection: `fin_sub_order`/`fin_global_min`/`fin_global_max`/`fin_is_barrier`/`fin_dim_exists`, `fin_remove_min_dim2`/`fin_remove_max_dim2`, `fin_block_dim0_global_min`/`fin_block_dim0_global_max`, `fin_barrier_dimension`, `fin_barrier_dim_le2` (with a one-line note: "carrier-generic versions of the ExecPoset levers, for the n-way recursion"); `fin_chain_reproduces_E_min`. Match existing table style.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export generic finite-poset levers; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (predicates) → G1 Step 1 + G2 Step 1; Component 2 (lemmas: surgery → G1, barrier → G2); Component 3 (consistency) → G3; wiring/testing/audit → G0 + G4. All mapped.
- **Existing `ExecPoset` lemmas untouched** (acceptance #4): this slice only ADDS files; it does not edit `ExtremumReduction.v`/`Ordinal.v`/`BarrierDim2.v`. Subagents must not modify those (they are READ-only references here).
- **Heaviest task is G1** (the realizer surgery port, ~250 lines): split into `FinPosetDimSurgery.v` from the start, with a further `…SurgeryMax.v` escape if it still overruns.
- **Name consistency:** `fin_` prefix throughout; `fin_sub_order R S` vs in-section `fin_sub_order S` reconciled by checking `About fin_sub_order` after G1 (the plan flags this in G2 Step 1).
- **Reused (confirmed present):** `dushnik_miller_exists`, `subtype_is_poset`, `subposet_dimension_le`, `cardinal_Im_injective`, `cardinalO_empty`, `cardinal_finite`, `finite_cardinal` (Dimension/Stdlib); `dimension_iso` (DimIso); `linear_sum_dimension` (LinearSum); `E_min`/`E_min_dim_2`/`Lmin`/`Umin`/`E_min_barrier`/`ep_size_ok` (execution).
- **Execution-time checks:** `About fin_sub_order` (R positional vs section), `About dushnik_miller_exists`/`cardinal_finite`/`finite_cardinal` arg shapes, `fin_remove_min_dim2` iff orientation (proj1/proj2), whether `IsBarrier E_min … ` is definitionally `fin_is_barrier (ep_order E_min) …` (G3 reassembles if not).

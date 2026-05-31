# Execution Reduction Framework — Implementation Plan (Sub-project B, part 3, slice 1)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. Proof bodies give a strategy. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** A composable framework for dimension-preserving (`PreservesDim`) and dimension-reducing (`ReducesDim`) maps between posets, with iso/subposet/embedding instances, dim≤2 corollaries, and a concrete `E_min` block-reduction instance.

**Architecture:** Two new modules in the `Execution` theory: `Reduction` (general-poset relations + composability + instances + corollaries, thin wrappers over `dimension_iso`/`subposet_dimension_le`/`posdim_unique`), `ReductionExamples` (concrete `E_min` instance, test-only).

**Tech Stack:** Coq/Rocq 9.1; `Dimension` (`DimDefs`, `Theorems`); execution `Poset`, `DimBridge`, `DimIso`, `Ordinal`, `DimExamples`, `FrontierExamples`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/Reduction.v` | `PreservesDim`, `ReducesDim`; composability; `iso_preserves_dim`, `subposet_reduces_dim`, `embedding_reduces_dim`; `preserves_dim2`, `reduces_dim2`. |
| `execution/ReductionExamples.v` | `E_min_block_reduces`, `E_min_block_dim_le_2`, `reduction_chain_demo` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `PreservesDim`, `ReducesDim`, `preserves_dim_refl`, `preserves_dim_sym`, `preserves_dim_trans`, `reduces_dim_refl`, `reduces_dim_trans`, `preserves_dim_reduces`, `iso_preserves_dim`, `subposet_reduces_dim`, `embedding_reduces_dim`, `preserves_dim2`, `reduces_dim2`, `E_min_block_reduces`, `E_min_block_dim_le_2`, `reduction_chain_demo`.

---

## Task D0: Scaffold

**Files:** create `execution/Reduction.v`, `execution/ReductionExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the two stubs (`(* … *)` comment line each).
- [ ] **Step 2:** Add `Reduction`, `ReductionExamples` to the `(modules …)` list in `execution/dune`.
- [ ] **Step 3:** Add the two `.v` paths to `_CoqProject` (after the frontier/ordinal entries).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/Reduction.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/Reduction.v execution/ReductionExamples.v execution/dune _CoqProject
git commit -m "scaffold execution reduction-framework modules"
```

---

## Task D1: Relations, composability, dim≤2 corollaries (`Reduction.v`)

**Files:** `execution/Reduction.v`

- [ ] **Step 1: Imports + the two relations**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimIso Ordinal.

Definition PreservesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall d, PosetDimension R d <-> PosetDimension S d.

Definition ReducesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall dR dS, PosetDimension R dR -> PosetDimension S dS -> dR <= dS.
```

- [ ] **Step 2: Composability**

```coq
Lemma preserves_dim_refl : forall A (R : A -> A -> Prop), PreservesDim A R A R.
Lemma preserves_dim_sym :
  forall A R B S, PreservesDim A R B S -> PreservesDim B S A R.
Lemma preserves_dim_trans :
  forall A R B S C T,
    PreservesDim A R B S -> PreservesDim B S C T -> PreservesDim A R C T.

Lemma reduces_dim_refl :
  forall A (R : A -> A -> Prop) `{IsPoset A R}, ReducesDim A R A R.
Lemma reduces_dim_trans :
  forall A R B S C T `{IsPoset B S},
    (exists dS, PosetDimension S dS) ->
    ReducesDim A R B S -> ReducesDim B S C T -> ReducesDim A R C T.

Lemma preserves_dim_reduces :
  forall A R B S `{IsPoset A R} `{IsPoset B S},
    (exists dS, PosetDimension S dS) ->
    PreservesDim A R B S -> ReducesDim A R B S.
```
Strategies (all `unfold` then logic):
- `preserves_dim_refl`/`_sym`/`_trans`: the iff is reflexive/symmetric/transitive pointwise (`tauto`/`firstorder` per `d`).
- `reduces_dim_refl`: `intros A R ? dR dS HdR HdS`. `posdim_unique HdR HdS : dR = dS`; `lia`.
- `reduces_dim_trans`: `intros … [dS HdS] H1 H2 dR dT HdR HdT`. `H1 dR dS HdR HdS : dR <= dS`; `H2 dS dT HdS HdT : dS <= dT`; `lia`.
- `preserves_dim_reduces`: `intros … [dS HdS] Hpres dR dS' HdR HdS'`. From `Hpres`, `PosetDimension R dR <-> PosetDimension S dR`; so `PosetDimension S dR` holds; `posdim_unique` with `HdS'` gives `dR = dS'`; `lia`.

- [ ] **Step 3: dim≤2 corollaries**

```coq
Lemma preserves_dim2 :
  forall A R B S,
    PreservesDim A R B S ->
    ((exists d, PosetDimension R d /\ d <= 2) <-> (exists d, PosetDimension S d /\ d <= 2)).

Lemma reduces_dim2 :
  forall A R B S,
    ReducesDim A R B S ->
    (exists dR, PosetDimension R dR) ->
    (exists d, PosetDimension S d /\ d <= 2) ->
    (exists d, PosetDimension R d /\ d <= 2).
```
Strategies:
- `preserves_dim2`: split; forward `[d [Hd Hle]]`: `Hpres d` gives `PosetDimension S d`; `exists d`. Backward symmetric.
- `reduces_dim2`: `intros … Hred [dR HdR] [dS [HdS Hle]]`. `Hred dR dS HdR HdS : dR <= dS`; `exists dR; split; [exact HdR | lia]`.

- [ ] **Step 4:** Build `bash .claude/scripts/timed-build.sh 240 execution/Reduction.vo 2`. Exit 0; zero admits.
- [ ] **Step 5:** Commit `git add execution/Reduction.v && git commit -m "feat(execution): reduction relations, composability, dim<=2 corollaries"`.

---

## Task D2: Instances (`Reduction.v`)

**Files:** `execution/Reduction.v` (extend)

- [ ] **Step 1: `iso_preserves_dim`**

```coq
Lemma iso_preserves_dim :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S} (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
    (forall a a', R a a' <-> S (f a) (f a')) ->
    PreservesDim A R B S.
```
Strategy: `unfold PreservesDim`. `intros … Hgf Hfg Hiso d`. Split.
- forward `PosetDimension R d -> PosetDimension S d`: `apply (dimension_iso A B R S f g Hgf Hfg Hiso)`.
- backward `PosetDimension S d -> PosetDimension R d`: `apply (dimension_iso B A S R g f Hfg Hgf Hiso')` where `Hiso' : forall b b', S b b' <-> R (g b)(g b')`. Derive `Hiso'` from `Hiso` + the bijection: `S b b' <-> S (f (g b)) (f (g b'))` (rewrite `Hfg`) `<-> R (g b)(g b')` (by `Hiso` backwards). Prove `Hiso'` as a local `assert`. (Confirm `dimension_iso`'s argument order with `About dimension_iso`.)

- [ ] **Step 2: `subposet_reduces_dim`**

```coq
Lemma subposet_reduces_dim :
  forall (B : Type) (S : B -> B -> Prop) `{IsPoset B S} (Sub : Ensemble B),
    ReducesDim {z | Ensembles.In _ Sub z}
               (fun x y => S (proj1_sig x) (proj1_sig y)) B S.
```
Strategy: `unfold ReducesDim`. `intros B S ? Sub dSubgiven dS HdSub HdS`. `subposet_dimension_le S Sub dS HdS` (positional `S`) gives `[d_q [Hinh Hle]]` with `Hinh : inhabited (PosetDimension (fun x y => S (proj1_sig x)(proj1_sig y)) d_q)` and `Hle : d_q <= dS`. `destruct Hinh as [Hq]`. `posdim_unique HdSub Hq : dSubgiven = d_q` (the subtype poset's IsPoset is `subtype_is_poset S Sub`; ensure it's the instance in scope — add `pose proof (subtype_is_poset S Sub)` or `Existing Instance`). `lia`.

- [ ] **Step 3: `embedding_reduces_dim`** (deferrable convenience)

```coq
Lemma embedding_reduces_dim :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S} (f : A -> B),
    (forall a a', a <> a' -> f a <> f a') ->
    (forall a a', R a a' <-> S (f a) (f a')) ->
    ReducesDim A R B S.
```
Strategy: the image `Im A (Full_set A) f : Ensemble B` is a subposet of `S`; `(A,R)` is order-iso to it. Build:
- `f' : A -> {b | In _ (Im _ _ (Full_set A) f) b} := fun a => exist _ (f a) (Im_intro _ _ (Full_set A) f a (Full_intro _ a) (f a) eq_refl)` (adjust to the exact `Im`/`Im_intro` shape; `Im` is from `Ensembles`).
- `g' : {b | In _ (Im …) b} -> A`: from `proj2_sig` (an `In (Im …) (proj1_sig b)` = `exists a, … /\ proj1_sig b = f a`), extract `a` via `constructive_definite_description` (uniqueness from injectivity of `f`) — needs `From Stdlib Require Import Description`. 
- Prove `g' (f' a) = a` (injectivity), `f' (g' b) = b` (image), and the order-iso `R a a' <-> (sub_order on image)(f' a)(f' a')` (= `S (f a)(f a')` by `Hemb`).
- Then `iso_preserves_dim` gives `PreservesDim R (image-subposet)`; `subposet_reduces_dim` gives `ReducesDim (image-subposet) S`; combine with `preserves_dim_reduces` (image-subposet has a dimension — finite or via `dushnik_miller_exists`... for general `B` not necessarily finite; if `B` is infinite this needs care) and `reduces_dim_trans`.

**Deferral note:** `embedding_reduces_dim` is a convenience derived from the two primitives. The `constructive_definite_description` extraction and the dimension-existence side-condition make it the fiddliest item. **If it stalls after real effort, deliver `iso_preserves_dim` + `subposet_reduces_dim` (the essential instances) and report `embedding_reduces_dim` as a tracked follow-up — never admit.** The concrete example (Task D3) uses only `subposet_reduces_dim`, so it is unaffected.

- [ ] **Step 4:** Build `bash .claude/scripts/timed-build.sh 360 execution/Reduction.vo 2`. Exit 0; zero admits.
- [ ] **Step 5:** Commit `git add execution/Reduction.v && git commit -m "feat(execution): iso/subposet/embedding reduction instances"`.

---

## Task D3: Concrete `E_min` instance (`ReductionExamples.v`)

**Files:** `execution/ReductionExamples.v`

- [ ] **Step 1: Imports + the three examples**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimIso Ordinal
                              DimExamples FrontierExamples Reduction.

Example E_min_block_reduces :
  ReducesDim {z | Ensembles.In _ Umin z}
             (fun x y => ep_order E_min (proj1_sig x) (proj1_sig y))
             (ep_carrier E_min) (ep_order E_min).

Example E_min_block_dim_le_2 :
  exists d, PosetDimension
              (fun x y : {z | Ensembles.In _ Umin z} =>
                 ep_order E_min (proj1_sig x) (proj1_sig y)) d /\ d <= 2.

Example reduction_chain_demo :
  ReducesDim {z | Ensembles.In _ Umin z}
             (fun x y => ep_order E_min (proj1_sig x) (proj1_sig y))
             (ep_carrier E_min) (ep_order E_min).
```
(Note: `sub_order E_min Umin` is definitionally `fun (x y : {z | In Umin z}) => ep_order E_min (proj1_sig x)(proj1_sig y)`; you may write `sub_order E_min Umin` instead of the lambda if it elaborates — check by `Print sub_order`. Use whichever unifies.)

Strategies:
- `E_min_block_reduces`: `apply (subposet_reduces_dim (ep_carrier E_min) (ep_order E_min) Umin)` (the `IsPoset (ep_carrier E_min) (ep_order E_min)` is `hb_IsPoset (ep_ranked E_min)` — `Existing Instance hb_IsPoset.`).
- `E_min_block_dim_le_2`: `apply (reduces_dim2 _ _ _ _ E_min_block_reduces)`.
  - `exists dR` (the block has a dimension): `dushnik_miller_exists` on the block. The block carrier `{z | In Umin z}` is finite (subtype of the finite `ep_carrier E_min`); get its cardinal via `cardinal_finite`/`subtype` reasoning, or more simply: the block is a subtype of a finite type, so `Finite (Full_set …)` holds; apply `dushnik_miller_exists`. (If proving block finiteness is fiddly, note `ep_size_ok E_min` gives `ep_carrier E_min` finite; a subtype of a finite type is finite — search `Finite_subtype`/`cardinal_subtype_full` already used in `Finite.v`.)
  - the `S`-side `exists d ≤ 2`: from `E_min_dim_2 : exec_has_dimension E_min 2` (= `inhabited (PosetDimension (ep_order E_min) 2)`); `destruct` it; `exists 2; split; [assumption | lia]`.
- `reduction_chain_demo`: `apply (reduces_dim_trans _ (ep_order E_min) _ (ep_order E_min) _ (ep_order E_min))` with the bridging dimension from `exec_dimension_exists E_min`; first leg `PreservesDim (ep_order E_min) (ep_order E_min)` via `iso_preserves_dim … (f:=id)(g:=id)` (the three hypotheses are `eq_refl`/`fun _ => eq_refl` and `iff_refl`-style) then `preserves_dim_reduces`; second leg `E_min_block_reduces`. (Goal endpoints must match; `reduces_dim_trans` from the block to `E_min` via `E_min` — i.e. the identity-iso leg is `ReducesDim (ep_order E_min)(ep_order E_min)`, composed after the block→E_min reduction. Order the transitivity so types line up; equivalently just `exact E_min_block_reduces` after demonstrating the iso leg separately — the point is to exercise `iso_preserves_dim` + composition, so structure it to actually use them.)

- [ ] **Step 2:** Build `bash .claude/scripts/timed-build.sh 300 execution/ReductionExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3:** Commit `git add execution/ReductionExamples.v && git commit -m "test(execution): E_min block reduction and composability demo"`.

---

## Task D4: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `Reduction` to the `Require Export` line in `execution/Execution.v` (NOT `ReductionExamples`).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 600 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions preserves_dim2.`, `Print Assumptions reduces_dim2.` to `execution/Reduction.v` and `Print Assumptions E_min_block_dim_le_2.` to `execution/ReductionExamples.v`; build, read the axiom blocks (expect only standard classical/choice axioms), then `git checkout -- execution/Reduction.v execution/ReductionExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "Reduction framework" subsection: `PreservesDim`/`ReducesDim` + composability (`preserves_dim_*`, `reduces_dim_*`, `preserves_dim_reduces`), `iso_preserves_dim`/`subposet_reduces_dim`/`embedding_reduces_dim` (note if embedding deferred), `preserves_dim2`/`reduces_dim2` (Reduction.v); `E_min_block_reduces`/`E_min_block_dim_le_2`/`reduction_chain_demo` (ReductionExamples.v). Match existing table style.
- [ ] **Step 6:** Commit `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export reduction framework; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (relations + composability) → D1; Component 2 (instances + dim2 corollaries) → D2 (instances) + D1 (corollaries — grouped with relations as they're trivial); Component 3 (concrete) → D3; wiring/testing/audit → D0 + D4. All mapped.
- **Deferral:** `embedding_reduces_dim` (D2 Step 3) is the only fiddly item and is explicitly deferrable; `iso_preserves_dim` + `subposet_reduces_dim` + all corollaries + the concrete example do not depend on it.
- **Name consistency:** `PreservesDim`/`ReducesDim` argument order `(A R B S)`; instances and corollaries use it consistently; `sub_order E_min Umin` ≡ the lambda form used in `ReductionExamples`.
- **Reused (confirmed present):** `dimension_iso` (DimIso), `subposet_dimension_le`/`subtype_is_poset` (Theorems), `posdim_unique`/`sub_order` (Ordinal), `exec_dimension_exists`/`E_min_dim_2`/`Umin` (DimBridge/DimExamples/FrontierExamples).
- **Execution-time checks:** `About dimension_iso` (arg order), `About subposet_dimension_le` (positional `S`), the `Im`/`Im_intro` shape for `embedding_reduces_dim`, block-finiteness lemma name for `E_min_block_dim_le_2` (`cardinal_subtype_full` pattern from `Finite.v`).

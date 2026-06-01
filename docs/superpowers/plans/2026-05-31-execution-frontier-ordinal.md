# Execution Frontiers & Ordinal Decomposition — Implementation Plan (Sub-project B, part 2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`) syntax.
>
> **Coq convention (as in prior plans):** **Definitions and lemma statements are authoritative — implement them verbatim.** Proof bodies give a strategy; develop exact tactics at execution time. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Formalize frontiers/barriers of execution posets and the ordinal-sum decomposition: a barrier split gives `no-alt-cycle` propagation (⇒ the dim≤2 reduction lever) and, as a stretch, `dim = max` of the blocks.

**Architecture:** Four new modules in the `Execution` theory: `Frontier` (definitions + structural), `Ordinal` (barrier decomposition theorems + iteration), `DimIso` (reusable dimension-under-order-iso, for the stretch), `FrontierExamples` (concrete `E_min` barrier, test-only).

**Tech Stack:** Coq/Rocq 9.1; `Dimension` modules `DimDefs`/`CriticalPairs`/`Theorems`/`LinearSum`; execution `Poset`/`DimBridge`/`DimCriticalPairs`/`DimExamples`; Stdlib `Ensembles`/`Finite_sets`/`List`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/Frontier.v` | `ConsistentCut`, `Frontier`, `IsBarrier`; `frontier_is_antichain`, `barrier_lower_consistent`, `barrier_upper_disjoint_below`. |
| `execution/Ordinal.v` | `no_alt_cycle`, block sub-posets, `barrier_critical_pairs`, `barrier_dim_ge`, `barrier_no_alt_cycle_propagation`, `barrier_dim2`, `IsFullySync`, `fully_sync_no_alt_cycle`, `fully_sync_dim2`. (Stretch lemmas `barrier_dimension`/`fully_sync_dimension` added here.) |
| `execution/DimIso.v` | reusable `dimension_iso` (stretch support). |
| `execution/FrontierExamples.v` | `E_min_barrier`, `E_min_barrier_cps` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (use exactly): `ConsistentCut`, `Frontier`, `IsBarrier`, `frontier_is_antichain`, `barrier_lower_consistent`, `barrier_upper_disjoint_below`, `sub_order`, `no_alt_cycle`, `barrier_critical_pairs`, `barrier_dim_ge`, `barrier_no_alt_cycle_propagation`, `barrier_dim2`, `IsFullySync`, `fully_sync_no_alt_cycle`, `fully_sync_dim2`, `dimension_iso`, `barrier_dimension`, `fully_sync_dimension`.

---

## Task C0: Scaffold the four modules

**Files:** create `execution/Frontier.v`, `execution/DimIso.v`, `execution/Ordinal.v`, `execution/FrontierExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the four stubs (one `(* … *)` comment line each).
- [ ] **Step 2:** Add `Frontier`, `DimIso`, `Ordinal`, `FrontierExamples` to the `(modules …)` list in `execution/dune`.
- [ ] **Step 3:** Add the four `execution/*.v` paths to `_CoqProject` (after `execution/DimExampleN3.v`).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/Frontier.vo 2`. Expected exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/Frontier.v execution/DimIso.v execution/Ordinal.v execution/FrontierExamples.v execution/dune _CoqProject
git commit -m "scaffold execution frontier/ordinal modules"
```

---

## Task C1: Frontiers & barriers (`Frontier.v`)

**Files:** `execution/Frontier.v`

- [ ] **Step 1: Definitions + structural lemmas**

```coq
From Stdlib Require Import Ensembles Finite_sets Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset.

#[local] Existing Instance hb_IsPoset.

Section Frontier.
  Context (E : ExecPoset).

  Definition ConsistentCut (C : Ensemble (ep_carrier E)) : Prop :=
    forall x y, ep_order E x y -> Ensembles.In _ C y -> Ensembles.In _ C x.

  Definition Frontier (F : Ensemble (ep_carrier E)) : Prop :=
    exists C, ConsistentCut C /\
      (forall x, Ensembles.In _ F x <->
         (Ensembles.In _ C x /\
          (forall y, Ensembles.In _ C y -> ep_order E x y -> y = x))).

  Definition IsBarrier (L U : Ensemble (ep_carrier E)) : Prop :=
    (forall x, Ensembles.In _ L x \/ Ensembles.In _ U x) /\
    (forall x, ~ (Ensembles.In _ L x /\ Ensembles.In _ U x)) /\
    (exists x, Ensembles.In _ L x) /\ (exists y, Ensembles.In _ U y) /\
    (forall x y, Ensembles.In _ L x -> Ensembles.In _ U y -> ep_order E x y).
End Frontier.
```

Then (after the section, `E` explicit):
```coq
Lemma frontier_is_antichain :
  forall E F, Frontier E F ->
    forall x y, Ensembles.In _ F x -> Ensembles.In _ F y -> ep_order E x y -> x = y.

Lemma barrier_lower_consistent :
  forall E L U, IsBarrier E L U -> ConsistentCut E L.

Lemma barrier_upper_disjoint_below :
  forall E L U, IsBarrier E L U ->
    forall x y, Ensembles.In _ U x -> Ensembles.In _ L y -> ~ ep_order E x y.
```

Proof strategies:
- `frontier_is_antichain`: from `Frontier`, `F`'s elements are maximal in `C`; `x,y∈F`, `ep_order x y`, both in `C` ⇒ by `F`'s maximality clause (`forall y∈C, x≤y → y=x`) applied to `x` and `y`: `y = x`.
- `barrier_lower_consistent`: `unfold ConsistentCut`. Given `ep_order E x y`, `y∈L`. Suppose `x∉L`; by cover `x∈U`; barrier gives `ep_order E y x` (wait: barrier is L below U, so `y∈L, x∈U ⇒ ep_order E y x`). With `ep_order E x y` and `ep_order E y x`, `poset_antisym ⇒ x = y ∈ L`, contradicting `x∈U` (disjoint). So `x∈L`.
- `barrier_upper_disjoint_below`: `x∈U, y∈L`. Barrier gives `ep_order E y x` (L below U). If also `ep_order E x y`, `poset_antisym ⇒ x=y`, contradicting disjoint cover. So `~ ep_order E x y`.

- [ ] **Step 2:** Build `bash .claude/scripts/timed-build.sh 180 execution/Frontier.vo 2`. Exit 0.
- [ ] **Step 3:** Commit `git add execution/Frontier.v && git commit -m "feat(execution): frontiers, barriers, and structural lemmas"`.

---

## Task C2: Block sub-posets + critical-pairs + dim≥ (`Ordinal.v` part 1)

**Files:** `execution/Ordinal.v`

- [ ] **Step 1: Imports, `sub_order`, `no_alt_cycle`, block poset**

```coq
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimCriticalPairs Frontier.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* The order of an execution restricted to a sub-ensemble S (a sub-poset). *)
Definition sub_order (E : ExecPoset) (S : Ensemble (ep_carrier E))
  : {x : ep_carrier E | Ensembles.In _ S x} -> {x | Ensembles.In _ S x} -> Prop :=
  fun x y => ep_order E (proj1_sig x) (proj1_sig y).

(* sub_order is a poset (from the library's subtype_is_poset). *)
Instance sub_order_poset (E : ExecPoset) (S : Ensemble (ep_carrier E))
  : IsPoset _ (sub_order E S) := subtype_is_poset (ep_order E) S.

Definition no_alt_cycle (A : Type) (R : A -> A -> Prop) : Prop :=
  ~ (exists cycle,
       (forall p, List.In p cycle -> IsCriticalPair R (fst p) (snd p))
       /\ IsAlternatingCycle R cycle).
```

- [ ] **Step 2: `barrier_critical_pairs` and `barrier_dim_ge`**

```coq
Lemma barrier_critical_pairs :
  forall E L U, IsBarrier E L U ->
    forall x y, IsCriticalPair (ep_order E) x y ->
      (Ensembles.In _ L x /\ Ensembles.In _ L y) \/
      (Ensembles.In _ U x /\ Ensembles.In _ U y).

Lemma barrier_dim_ge :
  forall E L U, IsBarrier E L U ->
    forall dL dU d,
      PosetDimension (sub_order E L) dL ->
      PosetDimension (sub_order E U) dU ->
      PosetDimension (ep_order E) d ->
      Nat.max dL dU <= d.
```

Strategies:
- `barrier_critical_pairs`: a critical pair `(x,y)` is incomparable (`critical_incomparable`). By barrier cover, each of `x,y ∈ L∪U`. If `x∈L, y∈U`: barrier gives `ep_order E x y`, contradicting incomparability. If `x∈U, y∈L`: barrier gives `ep_order E y x`, contradicting incomparability. So both in `L` or both in `U`.
- `barrier_dim_ge`: `subposet_dimension_le (ep_order E) L d Hd` gives `exists d_q, inhabited (PosetDimension (sub_order E L) d_q) /\ d_q <= d`. By PosetDimension uniqueness (`dimension_is_minimum` applied both ways, or a `PosetDimension_unique` helper proven inline: two dimensions of the same poset are equal), `d_q = dL`, so `dL <= d`. Same for `U`. `lia`.
  - Helper (prove inline): `Lemma posdim_unique : forall (A:Type)(R:A->A->Prop) d d', PosetDimension R d -> PosetDimension R d' -> d = d'.` (Each is ≤ the other via `dimension_is_minimum` on the other's realizer + cardinality. `le_antisym`.)

- [ ] **Step 3:** Build `bash .claude/scripts/timed-build.sh 300 execution/Ordinal.vo 2`. Exit 0.
- [ ] **Step 4:** Commit `git add execution/Ordinal.v && git commit -m "feat(execution): barrier blocks, critical pairs within blocks, dim>=max"`.

---

## Task C3: No-alt-cycle propagation (`Ordinal.v` part 2) — the key guaranteed lemma

**Files:** `execution/Ordinal.v` (extend)

- [ ] **Step 1: Two bridging facts about blocks**

```coq
(* A whole-poset critical pair whose endpoints are in S is a sub-poset critical pair. *)
Lemma critical_pair_in_block :
  forall E (S : Ensemble (ep_carrier E)) x y
         (Hx : Ensembles.In _ S x) (Hy : Ensembles.In _ S y),
    IsCriticalPair (ep_order E) x y ->
    (* downward closure of S not required: see note *)
    IsCriticalPair (sub_order E S) (exist _ x Hx) (exist _ y Hy).
```
NOTE on `critical_pair_in_block`: `critical_down`/`critical_up` for the sub-poset
quantify over sub-poset elements `a ∈ S`, which is a SUBSET of the whole-poset
quantification, so they follow from the whole-poset critical pair directly
(`Strict (sub_order) a x → Strict (ep_order) (proj1_sig a) x`, then apply the
whole `critical_down`, land back in `S`). Incomparability restricts likewise. No
consistency hypothesis on `S` needed.

- [ ] **Step 2: The propagation lemma**

```coq
Lemma barrier_no_alt_cycle_propagation :
  forall E L U, IsBarrier E L U ->
    no_alt_cycle _ (sub_order E L) ->
    no_alt_cycle _ (sub_order E U) ->
    no_alt_cycle _ (ep_order E).
```

Strategy (contrapositive): assume an alternating cycle `cyc` of `ep_order E`-critical
pairs. Show it yields an alternating cycle in `sub_order E L` or `sub_order E U`.
1. By `barrier_critical_pairs`, every pair `(xi,yi)` in `cyc` has both endpoints in
   `L` or both in `U`.
2. **All pairs are in the same block.** Recall `IsAlternatingCycle ((x0,y0)::rest)`
   expands (via `check_alternating_cycle x0 y0 rest`) to the relations
   `ep_order E x_{i+1} y_i` (for consecutive pairs) and the closing
   `ep_order E x0 y_n`. Using `barrier_upper_disjoint_below` (no `U→L` edge): if a
   pair is in `L` (so `y_i ∈ L`), then in `ep_order E x_{i+1} y_i` we cannot have
   `x_{i+1} ∈ U` (that would be a `U→L` edge), so `x_{i+1} ∈ L`, hence the next pair
   is in `L`. Threading this around the cycle (the closing relation handles wrap-around)
   forces all pairs into one block. Prove by an auxiliary induction over the pair list
   that tracks "current block" along the `check_alternating_cycle` relations.
3. If all in `L`: map `cyc` to a list of `sub_order E L` pairs (`exist _ xi Hxi`, …);
   `critical_pair_in_block` makes each a sub-poset critical pair, and the
   `check_alternating_cycle` relations are the same values (both restrict to
   `ep_order E` on `L`-elements), so it is an `IsAlternatingCycle (sub_order E L)` —
   contradicting `no_alt_cycle _ (sub_order E L)`. Symmetric for `U`.

This is the most intricate proof in the file; if step 2's bookkeeping balloons,
factor the "same-block" claim into its own `Lemma cycle_stays_in_block`. Keep the
file < 500 lines (split into `Ordinal.v` + `OrdinalCycle.v` if needed — wire the new
module like the others).

- [ ] **Step 3: The reduction-lever corollary**

```coq
Lemma barrier_dim2 :
  forall E L U, IsBarrier E L U ->
    no_alt_cycle _ (sub_order E L) ->
    no_alt_cycle _ (sub_order E U) ->
    exists d, exec_has_dimension E d /\ d <= 2.
```
Strategy: `barrier_no_alt_cycle_propagation` gives `no_alt_cycle _ (ep_order E)`,
which is exactly the hypothesis of `exec_dim_le_2_of_no_alt_cycle E` (note its cycle
predicate uses `exec_critical_pair E = IsCriticalPair (ep_order E)`; align by
`unfold no_alt_cycle, exec_critical_pair`). Apply it.

- [ ] **Step 4:** Build `bash .claude/scripts/timed-build.sh 480 execution/Ordinal.vo 1`. Exit 0; zero admits.
- [ ] **Step 5:** Commit `git add execution/Ordinal.v && git commit -m "feat(execution): alternating cycles stay in blocks; barrier dim<=2 lever"`.

---

## Task C4: Iterated fully-synchronized decomposition (`Ordinal.v` part 3)

**Files:** `execution/Ordinal.v` (extend)

- [ ] **Step 1: `IsFullySync` + iteration**

```coq
(* cumulative union of the first k blocks *)
Definition union_upto (E : ExecPoset) (blocks : list (Ensemble (ep_carrier E))) (k : nat)
  : Ensemble (ep_carrier E) :=
  fun x => exists i, i < k /\ Ensembles.In _ (nth i blocks (Empty_set _)) x.

Definition IsFullySync (E : ExecPoset) (blocks : list (Ensemble (ep_carrier E))) : Prop :=
  (forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x) /\         (* nonempty *)
  (forall x, exists i, i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x) /\ (* cover *)
  (forall i j x, i < length blocks -> j < length blocks -> i <> j ->
     Ensembles.In _ (nth i blocks (Empty_set _)) x ->
     ~ Ensembles.In _ (nth j blocks (Empty_set _)) x) /\                          (* disjoint *)
  (forall k, 0 < k -> k < length blocks ->
     IsBarrier E (union_upto E blocks k)
                 (fun x => ~ Ensembles.In _ (union_upto E blocks k) x)).          (* each prefix split is a barrier *)

Lemma fully_sync_no_alt_cycle :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks -> no_alt_cycle _ (sub_order E blk)) ->
    no_alt_cycle _ (ep_order E).

Lemma fully_sync_dim2 :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks -> no_alt_cycle _ (sub_order E blk)) ->
    exists d, exec_has_dimension E d /\ d <= 2.
```

Strategy:
- `fully_sync_no_alt_cycle`: induction on `length blocks`. The prefix-barrier at `k=length-1`
  splits `ep_order E` into `L = union_upto (length-1)` (the first blocks) and `U = last block`.
  `barrier_no_alt_cycle_propagation` needs `no_alt_cycle (sub_order E L)` and
  `no_alt_cycle (sub_order E U)`. `U` is the last block (hypothesis). `L` is the first
  `length-1` blocks, themselves a fully-sync execution of the sub-poset — but to keep the
  induction tractable, induct directly: `no_alt_cycle (ep_order E)` follows once we have
  `no_alt_cycle` for the union-of-first-(length-1) sub-poset and the last block, applying
  `barrier_no_alt_cycle_propagation` to the top split, with the IH supplying the lower
  part. (If relating `sub_order E (union_upto …)` to a recursive `IsFullySync` is awkward,
  an alternative is a single combined induction proving directly: any alternating cycle of
  `ep_order E` lies within one block — generalizing `cycle_stays_in_block` from a 2-way to
  an n-way ordered partition. Prefer whichever is shorter; the n-way "cycle stays in one
  block" is conceptually clean: along the cycle the block-index can never increase past a
  barrier and return.)
- `fully_sync_dim2`: `fully_sync_no_alt_cycle` then `exec_dim_le_2_of_no_alt_cycle`.

If the iteration's sub-poset bookkeeping is heavy, the **n-way "cycle stays in one block"**
route (no recursion into sub-posets — just one induction over the cycle using all the
prefix barriers) is the recommended implementation. State it as:
```coq
Lemma alt_cycle_in_one_block :
  forall E blocks, IsFullySync E blocks ->
    forall cyc, (forall p, List.In p cyc -> IsCriticalPair (ep_order E) (fst p) (snd p)) ->
      IsAlternatingCycle (ep_order E) cyc ->
      exists i, i < length blocks /\
        (forall p, List.In p cyc -> Ensembles.In _ (nth i blocks (Empty_set _)) (fst p)
                                 /\ Ensembles.In _ (nth i blocks (Empty_set _)) (snd p)).
```
then `fully_sync_no_alt_cycle` maps that single block's cycle into its `sub_order` and
contradicts the hypothesis.

- [ ] **Step 2:** Build `bash .claude/scripts/timed-build.sh 480 execution/Ordinal.vo 1`. Exit 0.
- [ ] **Step 3:** Commit `git add execution/Ordinal.v && git commit -m "feat(execution): fully-synchronized decomposition; no-alt-cycle ⇒ dim<=2"`.

---

## Task C5: STRETCH — `dimension_iso` + `barrier_dimension` (deferrable)

**Files:** `execution/DimIso.v`, then `execution/Ordinal.v`

> Deferrable. If it stalls after real effort, STOP, deliver C0–C4 + C6 (a complete deliverable), and report `barrier_dimension`/`fully_sync_dimension`/`dimension_iso` as a tracked follow-up. **Never admit.**

- [ ] **Step 1: `dimension_iso` (`DimIso.v`)**

```coq
From Stdlib Require Import Ensembles Finite_sets Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.

Lemma dimension_iso :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S}
         (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
    (forall a a', R a a' <-> S (f a) (f a')) ->
    forall d, PosetDimension R d -> PosetDimension S d.
```
Strategy: given `PosetDimension R d` with realizer `r`, define `r' := Im r (fun L => fun b b' => L (g b) (g b'))`. Show: each `L' ∈ r'` is a linear extension of `S` (transport totality/extension through the bijection + order-iso); `r'` is a realizer of `S` (`S b b' ↔ R (g b)(g b') ↔ (forall L∈r, L (g b)(g b')) ↔ (forall L'∈r', L' b b')`); `cardinal r' = d` (the map `L ↦ L'` is injective because `g` is surjective — `L (g b)(g b')` determines `L` on all pairs since `g` is onto). For minimality: any realizer `r'` of `S` pulls back to a realizer of `R` of the same size (symmetric construction with `f`,`g` swapped), so `dimension_is_minimum` transports. Conclude `PosetDimension S d`. (~120–180 lines; the bijection bookkeeping is the bulk.)

- [ ] **Step 2:** Build `DimIso.vo`. Commit.

- [ ] **Step 3: `barrier_dimension` (`Ordinal.v`)**

```coq
Lemma barrier_dimension :
  forall E L U, IsBarrier E L U ->
    forall dL dU d,
      PosetDimension (sub_order E L) dL ->
      PosetDimension (sub_order E U) dU ->
      PosetDimension (ep_order E) d ->
      0 < dL -> 0 < dU -> d = Nat.max dL dU.
```
Strategy: build the order-iso `f : ep_carrier E -> {x|In L x} + {x|In U x}` (by `In L x` decision — `classic`/the barrier cover; map to `inl`/`inr`) and `g` back (`proj1_sig` of either side). Prove `ep_order E a a' <-> LinearSumRel (sub_order E L) (sub_order E U) (f a) (f a')`: within-L → `inl`/`inl` → `sub_order L` (the `LinearSumRel` `inl` case); within-U → `inr`/`inr`; `L→U` (`a∈L, a'∈U`) → `inl`/`inr` → `LinearSumRel` always-true case, and the barrier gives `ep_order E a a'` so both sides hold; `U→L` → `inr`/`inl` → `LinearSumRel` false, and `barrier_upper_disjoint_below` gives `~ ep_order E a a'`, so both sides false. Then `dimension_iso` transports `PosetDimension (ep_order E) d` to `PosetDimension (LinearSumRel …) d`, and `linear_sum_dimension` gives `d = max dL dU`. (Use `posdim_unique` from C2 to identify the summand dims `dL`,`dU` with the ones `linear_sum_dimension` consumes.)

- [ ] **Step 4: `fully_sync_dimension`** — iterate `barrier_dimension` by induction on `blocks` (or state for the binary case and note the iteration). If heavy, deliver only `barrier_dimension` and defer `fully_sync_dimension`.

- [ ] **Step 5:** Build `bash .claude/scripts/timed-build.sh 600 execution/Ordinal.vo 1`. Exit 0; zero admits.
- [ ] **Step 6:** Commit.

---

## Task C6: Concrete instance (`FrontierExamples.v`, test-only)

**Files:** `execution/FrontierExamples.v`

`E_min` (from `DimExamples.v`) has events `a=(0,0), b=(0,1), c=(1,0), d=(1,1)` with `a ≺ b,c,d`.

- [ ] **Step 1: The bottom barrier**

```coq
From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs.
From Execution Require Import Op Event Edges Rank Poset DimExamples Frontier Ordinal.

Definition Lmin : Ensemble (ep_carrier E_min) := fun x => proj1_sig x = (0,0).
Definition Umin : Ensemble (ep_carrier E_min) := fun x => proj1_sig x <> (0,0).

Example E_min_barrier : IsBarrier E_min Lmin Umin.

Example E_min_barrier_cps :
  forall x y, IsCriticalPair (ep_order E_min) x y ->
    (Ensembles.In _ Lmin x /\ Ensembles.In _ Lmin y) \/
    (Ensembles.In _ Umin x /\ Ensembles.In _ Umin y).
```

Strategy:
- `E_min_barrier`: cover/disjoint are `classic`/decidable on `proj1_sig x = (0,0)`. Both inhabited: `a` in `Lmin`, `b` in `Umin` (reuse the concrete events / `valid_event_min_cases` technique from `DimExamples.v`). "L below U": the only `Lmin` element is `a=(0,0)` (by `valid_event_min_cases`, `proj1_sig x = (0,0)`); for any `y∈Umin` (i.e. `proj1_sig y ∈ {(0,1),(1,0),(1,1)}`), `ep_order E_min a y` holds — reuse the `hb_a_b`/`hb_a_c`/`hb_a_d` paths proven in `DimExamples.v` (re-prove or import them; if not exported, re-establish via `rt_step`/`rt_trans`).
- `E_min_barrier_cps`: `apply (barrier_critical_pairs E_min Lmin Umin E_min_barrier)`.

- [ ] **Step 2:** Build `bash .claude/scripts/timed-build.sh 300 execution/FrontierExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3:** Commit `git add execution/FrontierExamples.v && git commit -m "test(execution): E_min bottom barrier and critical-pairs-in-blocks"`.

---

## Task C7: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `Frontier DimIso Ordinal` to the `Require Export` line in `execution/Execution.v` (NOT `FrontierExamples`). (If C5/`DimIso` was deferred and the file is an empty stub, still safe to export an empty module; but if `DimIso.v` has no content, omit it from the export to avoid confusion — match what was actually built.)
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 600 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions fully_sync_dim2.` and `Print Assumptions barrier_critical_pairs.` to `execution/Ordinal.v`, build, read the axiom blocks (expect only standard classical/choice axioms), then `git checkout -- execution/Ordinal.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "Frontier / ordinal decomposition" subsection listing `ConsistentCut`/`Frontier`/`IsBarrier` + structural lemmas (Frontier.v), `barrier_critical_pairs`/`barrier_dim_ge`/`barrier_no_alt_cycle_propagation`/`barrier_dim2`/`IsFullySync`/`fully_sync_dim2` (Ordinal.v), `dimension_iso`/`barrier_dimension` if built, and `E_min_barrier` (FrontierExamples.v). Match existing table style.
- [ ] **Step 6:** Commit `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export frontier/ordinal; index decomposition results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (frontiers/barriers) → C1; Component 2 (`dimension_iso`) → C5; Component 3 guaranteed group → C2 (`barrier_critical_pairs`, `barrier_dim_ge`) + C3 (`barrier_no_alt_cycle_propagation`, `barrier_dim2`) + C4 (`IsFullySync`, `fully_sync_no_alt_cycle`, `fully_sync_dim2`); Component 3 stretch (`barrier_dimension`, `fully_sync_dimension`) → C5; Component 4 (concrete) → C6; wiring/testing/audit → C0 + C7. All mapped.
- **Deferral discipline:** C5 is the only deferrable task and is isolated; C0–C4 + C6 form a complete deliverable (the dim≤2 reduction lever) without it.
- **Name consistency:** `sub_order`, `no_alt_cycle`, `barrier_*`, `fully_sync_*`, `IsBarrier`, `IsFullySync`, `dimension_iso`, `posdim_unique` used consistently.
- **Key reuse:** `subtype_is_poset`, `subposet_dimension_le`, `IsAlternatingCycle`/`check_alternating_cycle`, `exec_dim_le_2_of_no_alt_cycle`, `linear_sum_dimension`, `linear_sum_critical_pairs` — all confirmed present.
- **The propagation (C3) is the load-bearing guaranteed proof**; the n-way variant in C4 (`alt_cycle_in_one_block`) generalizes it and is the recommended route for the iteration.
- **Stdlib/Dimension name checks at execution time:** `subposet_dimension_le`'s exact post-section argument shape; `posdim_unique` may already exist (Search `dimension` `unique`); `Im`/`cardinal_Im_injective` for `dimension_iso`.

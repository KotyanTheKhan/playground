# n-way Fully-Synchronized dim≤2 — Implementation Plan (n-way slice 2 of 2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Prove `fully_sync_dim_le2` — a fully-synchronized execution whose blocks are each dim≤2 is itself dim≤2 — via a generic `fin_fully_sync_dim_le2` on bare finite posets (induction over the block list, recursing into the lower sub-poset), instantiated for `IsFullySync`.

**Architecture:** New `execution/FinFullySync.v` (generic ordinal-partition predicate + restriction machinery + the induction), `execution/FullySyncDim2.v` (the `ExecPoset`/`IsFullySync` instantiation), `execution/FinFullySyncExamples.v` (the `E_min` 2-block instance, test-only). Splitting the generic theorem from the ExecPoset instance keeps each file focused and under 500 lines.

**Tech Stack:** Coq/Rocq 9.1; `Posets` (`PosetClasses`, `FinitePoset`); `Dimension` (`DimDefs`, `Theorems`); execution `DimIso`, `FinPosetDimSurgery`, `FinPosetDim`, `Poset`, `Ordinal`, `FullySync`, `DimBridge`, `DimExamples`, `FrontierExamples`; Stdlib `Ensembles`/`Finite_sets`/`Finite_sets_facts`/`List`/`Image`/`ProofIrrelevance`/`FunctionalExtensionality`/`PropExtensionality`/`Arith`/`Lia`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/FinFullySync.v` | `fin_ordinal_partition`, `restrict_block`, `fin_sub_order_finite`, `restrict_partition`, `restricted_block_dim2`, `fin_block_iso_full`, `fin_fully_sync_dim_le2`. |
| `execution/FullySyncDim2.v` | `fully_sync_pairwise_below`, `fully_sync_dim_le2` (the `IsFullySync`/`ExecPoset` instance). |
| `execution/FinFullySyncExamples.v` | `E_min_is_fully_sync_2`, `E_min_dim_le_2_via_fully_sync` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `fin_ordinal_partition`, `restrict_block`, `fin_sub_order_finite`, `restrict_partition`, `restricted_block_dim2`, `fin_block_iso_full`, `fin_fully_sync_dim_le2`, `fully_sync_pairwise_below`, `fully_sync_dim_le2`, `E_min_is_fully_sync_2`, `E_min_dim_le_2_via_fully_sync`.

**Section convention** (FinFullySync.v): `Section FinFullySync. Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (Hfin : Finite A (Full_set A)).` — definitions/lemmas reference `R`/`Hfin`; after `End`, they take `R {HR} (Hfin)` leading args. `fin_sub_order`/`fin_is_barrier`/`fin_barrier_dim_le2`/`fin_dim_exists` from slice 1 take `R` as a leading explicit arg (confirm with `About fin_sub_order` etc.).

**IMPORTANT — confirm slice-1 signatures first.** Before writing G-dependent code, run `About fin_barrier_dim_le2.`, `About fin_sub_order.`, `About fin_is_barrier.`, `About fin_dim_exists.` and match their exact binder layout (which args are explicit vs implicit). The plan assumes `R` explicit, `HR` implicit/TC, `Hfin` explicit.

---

## Task H0: Scaffold

**Files:** create `execution/FinFullySync.v`, `execution/FullySyncDim2.v`, `execution/FinFullySyncExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the three stubs.
- [ ] **Step 2:** Add `FinFullySync`, `FullySyncDim2`, `FinFullySyncExamples` to the `(modules …)` list in `execution/dune` (in that order, after the finposet-lever modules).
- [ ] **Step 3:** Add the three `.v` paths to `_CoqProject` (same order, after the finposet-lever entries).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/FinFullySync.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/FinFullySync.v execution/FullySyncDim2.v execution/FinFullySyncExamples.v execution/dune _CoqProject
git commit -m "scaffold n-way fully-synchronized dim<=2 modules"
```

---

## Task H1: Predicate + finiteness + block-iso helpers (`FinFullySync.v`)

**Files:** `execution/FinFullySync.v`

- [ ] **Step 1: Imports, section, `fin_ordinal_partition`, `restrict_block`**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim.
Import ListNotations.

Section FinFullySync.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  Definition fin_ordinal_partition (blocks : list (Ensemble A)) : Prop :=
    (forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x) /\
    (forall x, exists i, i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x) /\
    (forall i j x, i < length blocks -> j < length blocks -> i <> j ->
       Ensembles.In _ (nth i blocks (Empty_set _)) x ->
       ~ Ensembles.In _ (nth j blocks (Empty_set _)) x) /\
    (forall i j, i < j -> j < length blocks ->
       forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                   Ensembles.In _ (nth j blocks (Empty_set _)) y -> R x y).

  Definition restrict_block (L B : Ensemble A) : Ensemble {z | Ensembles.In _ L z} :=
    fun z => Ensembles.In _ B (proj1_sig z).
End FinFullySync.
```

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 120 execution/FinFullySync.vo 2`. Exit 0.

- [ ] **Step 3: `fin_sub_order_finite`**

```coq
Lemma fin_sub_order_finite :
  forall L, Finite {z : A | Ensembles.In _ L z} (Full_set {z | Ensembles.In _ L z}).
```
Strategy: a subtype of a finite type is finite. `Hfin : Finite A (Full_set A)` ⟹ `exists n, cardinal A (Full_set A) n` (`finite_cardinal`). The subset `L` is finite (`Finite_downward_closed` with `Full_set A`: `L ⊆ Full_set A`), so `cardinal A L m` for some `m` (`finite_cardinal`). Then `cardinal_subtype_full A L m _ : cardinal {z | In L z} (Full_set _) m` (the helper from `Dimension.Theorems`, used in `execution/Finite.v`), and `cardinal_finite` gives `Finite`. (Confirm `cardinal_subtype_full`/`Finite_downward_closed`/`finite_cardinal`/`cardinal_finite` names with `Search`.)

- [ ] **Step 4: `fin_block_iso_full`** — a block equal to the full set is order-iso, so its sub-order has the same dimension as `R`.

```coq
Lemma fin_block_iso_full :
  forall (B : Ensemble A),
    (forall x, Ensembles.In _ B x) ->          (* B is the full set *)
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
              inhabited (PosetDimension R d).
```
Strategy: with `HBfull : forall x, In B x`, the maps `f : A -> {z | In B z} := fun x => exist _ x (HBfull x)` and `g := proj1_sig` are mutually inverse (`g (f x) = x` by `proj1_sig`; `f (g z) = z` by `proof_irrelevance` on the membership proof) and order-preserving (`R x x' <-> fin_sub_order R B (f x)(f x')`, both `= R x x'`). `dimension_iso {z|In B z} A (fin_sub_order R B) R g f …` transports `PosetDimension (fin_sub_order R B) d` to `PosetDimension R d`. `destruct` the `inhabited`, apply, re-`inhabits`.

- [ ] **Step 5: Build** — `bash .claude/scripts/timed-build.sh 300 execution/FinFullySync.vo 2`. Exit 0; zero admits.
- [ ] **Step 6: Commit** — `git add execution/FinFullySync.v && git commit -m "feat(execution): ordinal partition, subtype finiteness, full-block iso"`.

---

## Task H2: Restriction of partition + block-dim transport (`FinFullySync.v`)

**Files:** `execution/FinFullySync.v` (extend)

These are the two helpers the induction's recursive case needs. Here `L` is the
union of a prefix of blocks and `pre` is that prefix (every block in `pre` is `⊆ L`).

- [ ] **Step 1: `restricted_block_dim2`** — a prefix block's dim≤2 transports to its restriction in the `L`-subtype.

```coq
Lemma restricted_block_dim2 :
  forall (L B : Ensemble A),
    (forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->     (* B ⊆ L *)
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
      inhabited (PosetDimension
                  (fin_sub_order (fin_sub_order R L) (restrict_block R L B)) d).
```
(Note: `fin_sub_order` takes `R` as a leading arg; `fin_sub_order (fin_sub_order R L) (restrict_block R L B)` is the sub-order of the `L`-subtype poset restricted to `restrict_block L B`. Confirm `restrict_block`'s arg layout — it was defined with `R` in section scope, so post-section likely `restrict_block R L B` or `restrict_block L B`; match `About restrict_block`.)
Strategy: the double-subtype `{w : {z|In L z} | In (restrict_block L B) w}` is order-iso to `{z : A | In B z}`. Build:
- `f : {z | In B z} -> {w : {z|In L z} | restrict_block L B w}` : given `exist _ x HxB`, the underlying `x ∈ L` (by `B ⊆ L`), so `exist _ (exist _ x (sub HxB)) HxB'` where the outer membership `restrict_block L B (exist _ x _) = In B x = HxB`.
- `g` : peel both layers to `exist _ x HxB`.
- Mutually inverse via `proof_irrelevance`; order-preserving (both relations reduce to `R x x'` on the underlying `A`). `dimension_iso` transports.
This is the one genuinely fiddly iso — budget care. Keep it a focused ~60-line lemma.

- [ ] **Step 2: `restrict_partition`** — the prefix forms an ordinal partition of the `L`-subtype.

```coq
Lemma restrict_partition :
  forall (L : Ensemble A) (pre : list (Ensemble A)),
    (forall B, List.In B pre -> forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    fin_ordinal_partition R pre ->          (* pre is itself an ordinal partition (of its union) *)
    (forall x, Ensembles.In _ L x <-> exists i, i < length pre /\ Ensembles.In _ (nth i pre (Empty_set _)) x) ->
    fin_ordinal_partition (fin_sub_order R L) (map (restrict_block R L) pre).
```
Strategy: unfold both `fin_ordinal_partition`. The four clauses transfer through `proj1_sig`:
- nonempty: each `restrict_block L B` inhabited because `B` inhabited and `B ⊆ L` (lift the witness into the subtype).
- cover: from the `L = ⋃ pre` hypothesis, every `z : {w|In L w}` has `proj1_sig z ∈ some block i`, so `z ∈ restrict_block L (nth i pre)`. (`nth i (map (restrict_block L) pre) ∅ = restrict_block L (nth i pre ∅)` via `map_nth`-style; mind the default — use `nth_indep`/`map_nth` carefully, or `nth_error`.)
- disjoint / below: transfer from `pre`'s clauses (the relation `fin_sub_order R L` on subtype elements is `R` on their `proj1_sig`s).
This is bookkeeping-heavy (the `nth … (map f l)` rewrites); budget care but it's mechanical.

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 480 execution/FinFullySync.vo 1`. Exit 0; zero admits. If 124, split H2 into `execution/FinFullySyncRestrict.v`.
- [ ] **Step 4: Commit** — `git add execution/FinFullySync.v && git commit -m "feat(execution): restrict ordinal partition and block dimension to a prefix sub-poset"`.

---

## Task H3: The induction — `fin_fully_sync_dim_le2` (`FinFullySync.v`)

**Files:** `execution/FinFullySync.v` (extend)

- [ ] **Step 1: State the theorem**

```coq
Lemma fin_fully_sync_dim_le2 :
  forall (blocks : list (Ensemble A)),
    fin_ordinal_partition R blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (fin_sub_order R blk) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension R d) /\ d <= 2).
```

- [ ] **Step 2: Prove by strong induction on `length blocks`**

Strategy: `intros blocks`. Generalize and induct on `length blocks` with `lt_wf_ind` (so the IH is available for any strictly-shorter block list, over ANY `(A', R', Hfin')` — but here `A` is fixed; to recurse into the sub-poset you need the IH over a DIFFERENT carrier. So instead make the WHOLE lemma's proof an induction that re-invokes `fin_fully_sync_dim_le2` itself at the sub-poset — i.e. structure as: prove `fin_fully_sync_dim_le2` for `(A,R,Hfin)` assuming it holds for all smaller block-lists over all `(A',R',Hfin')`. The clean way: make it a `Fixpoint`-free well-founded recursion by proving an auxiliary `forall n blocks, length blocks <= n -> …` by induction on `n : nat` where the statement quantifies over `A R HR Hfin blocks`. State the aux as:

```coq
Lemma fin_fully_sync_dim_le2_aux :
  forall n,
    forall (A' : Type) (R' : A' -> A' -> Prop) (HR' : IsPoset A' R')
           (Hfin' : Finite A' (Full_set A')) (blocks : list (Ensemble A')),
      length blocks <= n ->
      @fin_ordinal_partition A' R' blocks ->
      (forall blk, List.In blk blocks ->
         exists d, inhabited (PosetDimension (@fin_sub_order A' R' blk) d) /\ d <= 2) ->
      (exists d, inhabited (PosetDimension R' d) /\ d <= 2).
```
Induct on `n`. (`fin_fully_sync_dim_le2` is then `fin_fully_sync_dim_le2_aux (length blocks) A R HR Hfin blocks (le_n _)`.) The aux quantifies over the carrier, so the recursive call at the `L`-sub-poset (with `length pre < length blocks <= n`, hence `<= n-1`) is exactly the IH.

Cases:
- **`blocks = []`:** cover clause says every `x : A` is in `nth i [] ∅` for some `i < 0` — impossible, so `A` is empty. Then `R`'s realizer can be empty ⟹ dimension 0. Provide `exists d` from `fin_dim_exists R' Hfin'` and bound `d <= 2`: with `A'` empty, any two "dimensions" — simplest, prove `dim = 0` is impossible to need >2... Actually: with empty carrier, `fin_dim_exists` gives some `d` with `PosetDimension R' d`; show `d <= 2` because the empty realizer (cardinality 0) is a realizer of an empty poset, so `dimension_is_minimum` gives `d <= 0 <= 2`. (Construct the empty realizer is a realizer: `realizer_intersection` holds vacuously both ways over empty carrier.) If this base case is fiddly, an alternative: handle `[]` by noting the block-hyp is vacuous and the cover makes `A'` empty, then `exists 0; split; [apply inhabits; <build PosetDimension R' 0 with empty realizer> | lia]`.
- **`blocks = pre ++ [Bk]`** (use `rev`/`exists last` to peel; or `destruct (list_snoc blocks)`): 
  - If `pre = []`: single block `[Bk]`, `Bk` is full (cover); `fin_block_iso_full R Bk … d` transports `Bk`'s dim≤2 to `R`. Done.
  - If `pre <> []`: set `L := fun x => exists i, i < length pre /\ In (nth i pre ∅) x` (= union of `pre`). Prove `fin_is_barrier R L Bk`:
    - cover: every `x` is in some block (cover of `blocks`); if its index `< length pre` then `x ∈ L`, else it's the last block `Bk`.
    - disjoint: `L` and `Bk` disjoint (a point in block `< length pre` is not in block `length pre`, by `blocks`'s disjoint clause).
    - inhabited: `L` (pre nonempty + its blocks nonempty), `Bk` (nonempty).
    - `L`-below-`Bk`: for `x ∈ L` (block `i < length pre`) and `y ∈ Bk` (block `length pre`), `i < length pre < length blocks`, so the partition's "below" clause gives `R x y`.
  - `apply (fin_barrier_dim_le2 R Hfin L Bk Hbar)`. Two goals:
    - `Bk` block dim≤2: from the `blocks` hypothesis at `Bk` (`List.In Bk blocks`); `fin_sub_order R Bk` matches.
    - `L` block dim≤2 (`exists d, inhabited (PosetDimension (fin_sub_order R L) d) /\ d<=2`): apply the IH (`fin_fully_sync_dim_le2_aux n …` with `n` from `length pre <= n`) at `(A' := {z|In L z}, R' := fin_sub_order R L, Hfin' := fin_sub_order_finite R Hfin L)`, partition `map (restrict_block R L) pre` (via `restrict_partition`), block-hyps via `restricted_block_dim2`. The recursion returns `exists d, inhabited (PosetDimension (fin_sub_order R L) d) /\ d<=2` — exactly the goal.

Develop the exact term-plumbing at execution time; the structure above is complete. The `pre ++ [Bk]` peeling: use `exists_last`/`rev` (`destruct (rev blocks)`), or prove a `snoc` view. Mind `nth`/`length` arithmetic for `pre ++ [Bk]` (`nth i (pre++[Bk]) ∅ = nth i pre ∅` for `i < length pre`, `= Bk` for `i = length pre`; Stdlib `app_nth1`/`app_nth2`).

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 600 execution/FinFullySync.vo 1`. Exit 0; zero admits. If it overruns, factor the barrier-construction (`fin_is_barrier R L Bk`) into its own lemma `fin_prefix_barrier`.
- [ ] **Step 4: Commit** — `git add execution/FinFullySync.v && git commit -m "feat(execution): n-way ordinal-partition dim<=2 by induction on blocks"`.

---

## Task H4: ExecPoset instantiation (`FullySyncDim2.v`)

**Files:** `execution/FullySyncDim2.v`

- [ ] **Step 1: Imports + `fully_sync_pairwise_below`**

```coq
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FullySync FinPosetDimSurgery FinPosetDim FinFullySync.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Lemma fully_sync_pairwise_below :
  forall E blocks, IsFullySync E blocks ->
    forall i j, i < j -> j < length blocks ->
      forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                  Ensembles.In _ (nth j blocks (Empty_set _)) y -> ep_order E x y.
```
Strategy: from `IsFullySync E blocks`, the prefix split at `k := j` is an `IsBarrier E (union_upto E blocks j) (complement)`. `x ∈ nth i blocks ∅` with `i < j` ⟹ `x ∈ union_upto E blocks j` (the `L` side; `union_upto` is `exists i', i' < j /\ In (nth i' …) x`, witness `i`). `y ∈ nth j blocks ∅` ⟹ `y ∉ union_upto E blocks j` (disjointness: `y` is in block `j`, and `union_upto j` only has blocks `< j`; use `IsFullySync`'s disjoint field), so `y ∈ complement` (the `U` side). The barrier's `Hbelow x y` gives `ep_order E x y`. (Confirm `IsFullySync`'s field accessors and `union_upto`'s definition by reading `FullySync.v`.)

- [ ] **Step 2: `fully_sync_dim_le2`**

```coq
Lemma fully_sync_dim_le2 :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) ->
    (exists d, exec_has_dimension E d /\ d <= 2).
```
Strategy:
- `Hfin : Finite (ep_carrier E) (Full_set _)` from `cardinal_finite _ _ (ep_size E) (ep_size_ok E)` (or via `event_cardinal`/`total`; match what's available — `ep_size_ok E : cardinal (ep_carrier E)(Full_set _)(ep_size E)`).
- Build `fin_ordinal_partition (ep_order E) blocks`: nonempty/cover/disjoint are `IsFullySync`'s first three fields verbatim; the "earlier-below-later" clause is `fully_sync_pairwise_below`.
- The block hypotheses: `fin_sub_order (ep_order E) blk` is definitionally `sub_order E blk`, so the given `forall blk, … inhabited (PosetDimension (sub_order E blk) d) …` supplies `… (PosetDimension (fin_sub_order (ep_order E) blk) d) …` (use `unfold`/`change` if the elaborator needs it).
- `apply (fin_fully_sync_dim_le2 (ep_order E) Hfin blocks Hpart Hblocks)`. Result `exists d, inhabited (PosetDimension (ep_order E) d) /\ d<=2`, which is `exists d, exec_has_dimension E d /\ d<=2` (definitional).
(Confirm `fin_fully_sync_dim_le2`'s binder layout via `About` — `R` explicit, `HR` TC from `hb_IsPoset`, `Hfin` explicit.)

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 360 execution/FullySyncDim2.vo 2`. Exit 0; zero admits.
- [ ] **Step 4: Commit** — `git add execution/FullySyncDim2.v && git commit -m "feat(execution): fully_sync_dim_le2 (ExecPoset n-way lever)"`.

---

## Task H5: Concrete `E_min` instance (`FinFullySyncExamples.v`)

**Files:** `execution/FinFullySyncExamples.v`

- [ ] **Step 1: `E_min_is_fully_sync_2` + `E_min_dim_le_2_via_fully_sync`**

```coq
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FullySync FinPosetDim FinFullySync FullySyncDim2
                              DimExamples FrontierExamples.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.

Example E_min_is_fully_sync_2 : IsFullySync E_min [Lmin; Umin].

Example E_min_dim_le_2_via_fully_sync :
  exists d, exec_has_dimension E_min d /\ d <= 2.
```
Strategy:
- `E_min_is_fully_sync_2`: read `FullySync.v` for `IsFullySync`'s exact shape (nonempty / cover / disjoint / prefix-barrier). Discharge each over `blocks = [Lmin; Umin]` (length 2):
  - nonempty: `Lmin` has `ev_a`, `Umin` has `ev_b` (from `FrontierExamples`/`DimExamples`).
  - cover: `valid_event_min_cases x` ⟹ `proj1_sig x ∈ {(0,0),(0,1),(1,0),(1,1)}`; `(0,0) ∈ Lmin` (block 0), the rest `∈ Umin` (block 1). (`Lmin = fun x => proj1_sig x = (0,0)`, `Umin = fun x => proj1_sig x <> (0,0)` from `FrontierExamples.v` — confirm.)
  - disjoint: blocks 0,1 disjoint (`= (0,0)` vs `<> (0,0)`).
  - prefix barrier (only `k=1`, since `0 < k < 2`): `union_upto E_min [Lmin;Umin] 1` = `{x | exists i<1, In (nth i …) x}` = `Lmin`; complement = `Umin`. So the obligation is `IsBarrier E_min Lmin Umin` — `exact E_min_barrier` (or reconcile `union_upto … 1` to `Lmin` via `Extensionality_Ensembles` first, then `E_min_barrier`). NOTE: `IsBarrier`'s `U` is literally `fun x => ~ In (union_upto …) x`; `E_min_barrier : IsBarrier E_min Lmin Umin`. Reconcile `union_upto E_min [Lmin;Umin] 1 = Lmin` and `(fun x => ~ In (union_upto …) x) = Umin` by ensemble extensionality, then transport `E_min_barrier`.
- `E_min_dim_le_2_via_fully_sync`: `apply (fully_sync_dim_le2 E_min [Lmin;Umin] E_min_is_fully_sync_2)`. Two block goals (`List.In blk [Lmin;Umin]`): for each, `exists d, inhabited (PosetDimension (sub_order E_min blk) d) /\ d<=2` — from `subposet_dimension_le (ep_order E_min) blk 2 Hd2` with `Hd2` from `E_min_dim_2` (`destruct E_min_dim_2 as [Hd2]`). A small local helper `E_min_block_dim2 : forall S, exists d, inhabited (PosetDimension (sub_order E_min S) d) /\ d<=2` (as in earlier example files) discharges both.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/FinFullySyncExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/FinFullySyncExamples.v && git commit -m "test(execution): E_min dim<=2 via the n-way fully-sync lever"`.

---

## Task H6: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `FinFullySync FullySyncDim2` to the `Require Export` line in `execution/Execution.v` (NOT `FinFullySyncExamples`).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 900 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions fin_fully_sync_dim_le2.` to `FinFullySync.v`, `Print Assumptions fully_sync_dim_le2.` to `FullySyncDim2.v`, `Print Assumptions E_min_dim_le_2_via_fully_sync.` to `FinFullySyncExamples.v`; build each; read the axiom blocks (expect only standard classical/choice axioms); then `git checkout -- execution/FinFullySync.v execution/FullySyncDim2.v execution/FinFullySyncExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add an "n-way fully-synchronized dim≤2" subsection: `fin_ordinal_partition`, `restrict_block`/`restrict_partition`/`restricted_block_dim2`/`fin_sub_order_finite`/`fin_block_iso_full`, `fin_fully_sync_dim_le2` (generic); `fully_sync_pairwise_below`, `fully_sync_dim_le2` (ExecPoset; **the genuine n-way dim≤2 lever**); `E_min_is_fully_sync_2`/`E_min_dim_le_2_via_fully_sync`. Match existing table style.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export n-way fully-sync dim<=2; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (predicate + theorem) → H1 (predicate/helpers) + H3 (theorem); Component 2 (restriction machinery) → H1 (`fin_sub_order_finite`, `fin_block_iso_full`) + H2 (`restrict_partition`, `restricted_block_dim2`); Component 3 (ExecPoset instance) → H4; Component 4 (concrete) → H5; wiring/testing/audit → H0 + H6. All mapped.
- **Hardest tasks:** H2 (`restricted_block_dim2` double-subtype iso; `restrict_partition` `nth`/`map` bookkeeping) and H3 (the carrier-quantified `_aux` strong induction with the sub-poset recursive call). Both flagged with split escapes.
- **Key recursion device:** `fin_fully_sync_dim_le2_aux` quantifies over `(A', R', HR', Hfin', blocks)` and inducts on a `nat` bound `n ≥ length blocks`, so the recursive call at the `L`-sub-poset (a different carrier) is a legitimate IH. Plain `induction blocks` would NOT give a carrier-general IH — this is the crux; do not shortcut it.
- **Name consistency:** `fin_ordinal_partition`, `restrict_block`, `fin_sub_order_finite`, `restrict_partition`, `restricted_block_dim2`, `fin_block_iso_full`, `fin_fully_sync_dim_le2`(`_aux`), `fully_sync_pairwise_below`, `fully_sync_dim_le2`, `E_min_is_fully_sync_2`, `E_min_dim_le_2_via_fully_sync`.
- **Reused (confirmed present):** `fin_sub_order`/`fin_is_barrier`/`fin_barrier_dim_le2`/`fin_dim_exists` (FinPosetDim/Surgery — VERIFY binder layout with `About`), `dimension_iso` (DimIso), `cardinal_subtype_full`/`subposet_dimension_le`/`cardinal_finite`/`finite_cardinal`/`Finite_downward_closed` (Dimension/Stdlib), `IsFullySync`/`union_upto` (FullySync), `sub_order`/`ep_size_ok` (Ordinal/Poset), `E_min`/`E_min_dim_2`/`Lmin`/`Umin`/`E_min_barrier`/`valid_event_min_cases`/`ev_a`/`ev_b` (examples).
- **Execution-time first step:** run the `About` checks listed in the file-structure note before writing H3/H4 (the slice-1 binder layout is load-bearing).

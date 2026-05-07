# WidthUpperBound.v Refactor — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split the monolithic `posets/dilworth/WidthUpperBound.v` (2785 lines) into 8 focused files under `posets/dilworth/upper_bound/`, and dedupe the near-twin Above/Below chain-assignment proofs (~1680 lines combined) into a single parameterized kernel applied with `R` and `flip R`.

**Architecture:** Each existing logical section becomes its own file. The two giant `*_chain_assignment_exists` lemmas collapse into one `chain_assignment_kernel` proved against an abstract poset `R'`; the Below variant is derived by instantiating with `flip R` and rewriting through small duality lemmas. Public API (`DilworthB` and all currently-exported names) is preserved.

**Tech Stack:** Coq 8.19+, `dune` `(coq.theory)` stanza with `(include_subdirs qualified)`, build via `mise run build-posets` (per saved memory: always use mise tasks, never naked dune/opam).

**Spec:** `docs/superpowers/specs/2026-05-01-widthupperbound-refactor-design.md`

---

## Pre-flight

- [ ] **Step 0.1: Confirm starting build is green**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

If this fails, stop and fix the baseline before refactoring.

- [ ] **Step 0.2: Read the spec end-to-end**

Open `docs/superpowers/specs/2026-05-01-widthupperbound-refactor-design.md`. Internalize the file layout, the kernel design, and the migration order. Each task below corresponds to one entry in the migration order from the spec.

---

## Task 1: Enable subdirectory inclusion in dune

**Files:**
- Modify: `posets/dilworth/dune`

The current `dune` file is:
```
(coq.theory
 (name Dilworth)
 (package playground)
 (theories Stdlib Posets ChipalaBook))
```

We add `(include_subdirs qualified)` so files under `posets/dilworth/upper_bound/` get qualified module names like `Dilworth.upper_bound.Slices`.

- [ ] **Step 1.1: Edit `posets/dilworth/dune`**

Replace the entire file with:
```
(include_subdirs qualified)

(coq.theory
 (name Dilworth)
 (package playground)
 (theories Stdlib Posets ChipalaBook))
```

(`include_subdirs` is a top-level stanza, separate from `coq.theory`.)

- [ ] **Step 1.2: Build to confirm no-op change**

Run: `mise run build-posets`
Expected: `✅ Build successful!` (no new files yet, just config change)

- [ ] **Step 1.3: Commit**

```bash
git add posets/dilworth/dune
git commit -m "$(cat <<'EOF'
build: enable include_subdirs qualified for Dilworth theory

Lets us split posets/dilworth/WidthUpperBound.v into
focused files under posets/dilworth/upper_bound/, accessed
as Dilworth.upper_bound.<File>.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Move structural Above/Below lemmas to `upper_bound/Slices.v`

**Files:**
- Create: `posets/dilworth/upper_bound/Slices.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Lemmas being moved (verbatim from `WidthUpperBound.v`):**
- `la_in_Above` (lines 17–25)
- `la_in_Below` (lines 27–35)
- `largest_antichain_in_Above` (lines 37–46)
- `largest_antichain_in_Below` (lines 48–57)
- `above_contains_la` (lines 59–69)
- `below_contains_la` (lines 71–81)
- `sub_in_above_or_below` (lines 328–372)
- `la_largest_in_above` (lines 374–390)
- `la_largest_in_below` (lines 392–408)
- `la_card_le_sub` (lines 410–432)
- `above_card_lt` (lines 434–464)
- `below_card_lt` (lines 466–496)
- `antichain_lb_for_chain_cover` (lines 556–576)

The `Local Lemma Nat_le_of_succ_le` (lines 6–7) is needed in later moves; keep it in `WidthUpperBound.v` for now.

- [ ] **Step 2.1: Create `posets/dilworth/upper_bound/Slices.v`**

Header + section frame:
```coq
(* Structural lemmas relating a subposet to its largest antichain via Above/Below.
   Used throughout the upper-bound proof to slice sub by its position relative to la. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section Slices.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* === Helper Lemmas for Above and Below === *)

  (* ... copy lines 17–81 verbatim from WidthUpperBound.v ... *)

  (* === Inductive Step Preliminaries === *)

  (* ... copy lines 328–496 verbatim from WidthUpperBound.v ... *)

  (* === Antichain Lower Bound for Chain Covers === *)

  (* ... copy lines 556–576 verbatim from WidthUpperBound.v ... *)

End Slices.
```

For each lemma listed above, copy its body verbatim from `WidthUpperBound.v`. Drop only the file-internal `(* === banner === *)` comments — they're replaced by the three coarser banners shown.

- [ ] **Step 2.2: Remove the moved lemmas from `WidthUpperBound.v`**

Delete the source ranges listed above. Replace each deleted block with nothing (no placeholders). The `(* === Helper Lemmas for Above and Below === *)` banner (lines 13–15), the `(* === Inductive Step for DilworthB === *)` banner (lines 324–326), and the `(* === Antichain Lower Bound for Chain Covers === *)` banner (lines 552–554) all go away with their contents.

- [ ] **Step 2.3: Add the import to `WidthUpperBound.v`**

In the existing top imports (currently line 4):
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall.
```

Append `upper_bound.Slices`:
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices.
```

- [ ] **Step 2.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

If you see "Reference X not found" errors, you missed copying a lemma; check the listed line ranges.
If you see "duplicate definition" errors, the lemma still exists in both files; remove it from `WidthUpperBound.v`.

- [ ] **Step 2.5: Commit**

```bash
git add posets/dilworth/upper_bound/Slices.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): extract Above/Below slice lemmas to upper_bound/Slices.v

Moves 13 structural lemmas (la_in_Above/Below, sub_in_above_or_below,
above/below_card_lt, antichain_lb_for_chain_cover, etc.) out of
WidthUpperBound.v into a focused file. No proof changes.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Move Hall-defect lemmas to `upper_bound/HallDefect.v`

**Files:**
- Create: `posets/dilworth/upper_bound/HallDefect.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Lemmas + definitions being moved:**
- `min_elements_eq_la` (lines 83–105)
- `Definition StrictSucc` (lines 107–108)
- `Definition StrictPred` (lines 110–111)
- `dilworth_hall_defect` (lines 113–160)
- `dilworth_hall_defect_pred` (lines 162–210)

- [ ] **Step 3.1: Create `posets/dilworth/upper_bound/HallDefect.v`**

```coq
(* Hall-defect bounds for the largest antichain.
   These are the inequalities |S| ≤ |StrictSucc S| + w (and the predecessor
   variant) that Hall's marriage theorem requires when matching sub against
   sub ⊎ la in the assignment kernel. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section HallDefect.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* la-elements are exactly the minimal elements of sub, when sub ⊆ Above(la). *)
  (* ... copy min_elements_eq_la verbatim (lines 83–105) ... *)

  (* Strict successors of S inside sub: y ∈ sub with some x ∈ S, R x y, x ≠ y. *)
  (* ... copy Definition StrictSucc verbatim (lines 107–108) ... *)

  (* Strict predecessors, dual to StrictSucc. *)
  (* ... copy Definition StrictPred verbatim (lines 110–111) ... *)

  (* For any S ⊆ sub, |S| ≤ |StrictSucc S| + w. The "missing" part of S
     beyond StrictSucc is itself an antichain, so bounded by w. *)
  (* ... copy dilworth_hall_defect verbatim (lines 113–160) ... *)

  (* Predecessor variant; symmetric proof. *)
  (* ... copy dilworth_hall_defect_pred verbatim (lines 162–210) ... *)

End HallDefect.
```

- [ ] **Step 3.2: Remove the moved content from `WidthUpperBound.v`**

Delete lines 83–210 (and the `(* === Helper Lemmas for Above and Below === *)` block above them if not already removed in Task 2).

- [ ] **Step 3.3: Add import to `WidthUpperBound.v`**

Append `upper_bound.HallDefect` to the `From Dilworth Require Import` line:
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices upper_bound.HallDefect.
```

- [ ] **Step 3.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

- [ ] **Step 3.5: Commit**

```bash
git add posets/dilworth/upper_bound/HallDefect.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): extract Hall-defect lemmas to upper_bound/HallDefect.v

Moves StrictSucc/StrictPred definitions, min_elements_eq_la, and the two
dilworth_hall_defect{,_pred} lemmas. No proof changes.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Move base cases to `upper_bound/BaseCases.v`

**Files:**
- Create: `posets/dilworth/upper_bound/BaseCases.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Moving:**
- `empty_antichain_contradiction` (lines 238–245)
- `singleton_antichain_is_chain` (lines 247–263)
- `width_one_implies_chain` (lines 265–322)
- `singleton_chain_cover` (lines 498–542)
- `antichain_singleton_cover` (lines 544–550)
- `below_fiber_cover_cardinal` (lines 582–640)

- [ ] **Step 4.1: Create `posets/dilworth/upper_bound/BaseCases.v`**

```coq
(* Base cases for DilworthB:
   - empty/singleton antichains and width 0/1
   - the trivial singleton chain cover
   - the cardinality of a fiber-style chain cover (used to count |cover| = w
     in the assignment-derived chain cover). *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section BaseCases.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* === Width 0 and Width 1 === *)

  (* ... copy lines 238–322 verbatim ... *)

  (* === Singleton chain cover === *)

  (* ... copy lines 498–550 verbatim ... *)

  (* === Fiber-style chain cover cardinality === *)

  (* ... copy lines 582–640 verbatim ... *)

End BaseCases.
```

- [ ] **Step 4.2: Remove the moved blocks from `WidthUpperBound.v`**

Delete the corresponding ranges. Also delete the now-orphaned banner comments (`(* === Special Cases: Width 0 and Width 1 === *)`, `(* === Fiber Cover Cardinality === *)`).

- [ ] **Step 4.3: Update imports in `WidthUpperBound.v`**

Append `upper_bound.BaseCases`:
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices upper_bound.HallDefect upper_bound.BaseCases.
```

- [ ] **Step 4.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

- [ ] **Step 4.5: Commit**

```bash
git add posets/dilworth/upper_bound/BaseCases.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): extract base cases to upper_bound/BaseCases.v

Moves empty/singleton/width-one antichain handling, singleton_chain_cover,
antichain_singleton_cover, and below_fiber_cover_cardinal. No proof changes.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Move iteration helpers to `upper_bound/Iter.v`

**Files:**
- Create: `posets/dilworth/upper_bound/Iter.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Moving:**
- `Local Lemma Nat_le_of_succ_le` (lines 6–7) — promote to a regular `Lemma` so it's exported.
- `Fixpoint chain_root_aux` (lines 216–223)
- `Fixpoint depth_aux` (lines 225–232)

These are parameter-free over `R`, so the file does not need `IsPoset`.

- [ ] **Step 5.1: Create `posets/dilworth/upper_bound/Iter.v`**

```coq
(* Bounded iteration along an A → sum A A matching.
   chain_root_aux follows inl-edges until either fuel runs out or an inr-cell
   is reached; depth_aux counts the steps taken. Both are used by the
   chain-assignment kernel to extract a la-target and a chain-fiber for each
   element of sub. *)

From Stdlib Require Import Arith Lia.

Section Iter.
  Context {A : Type}.

  Lemma Nat_le_of_succ_le (n m : nat) : Datatypes.S n <= m -> n <= m.
  Proof. lia. Qed.

  Fixpoint chain_root_aux (m : A -> sum A A) (fuel : nat) (x : A) : A :=
    match fuel with
    | 0 => x
    | S k => match m x with
             | inr _ => x
             | inl y => chain_root_aux m k y
             end
    end.

  Fixpoint depth_aux (m : A -> sum A A) (fuel : nat) (x : A) : nat :=
    match fuel with
    | 0 => 0
    | S k => match m x with
             | inr _ => 0
             | inl y => S (depth_aux m k y)
             end
    end.

End Iter.
```

(No further parameter-free lemmas are extracted yet. The proof-specific iteration lemmas — `Hiter_eq2`, `Hdepth_inr/inl/le`, `Hroot_depth`, etc. — currently live inside the giant `assert` blocks of the chain-assignment proof and will be promoted to `Lemma`s during Task 7.)

- [ ] **Step 5.2: Remove the moved content from `WidthUpperBound.v`**

Delete lines 6–7 (Nat_le_of_succ_le) and lines 216–232 (the two Fixpoints) and the `(* === Chain root auxiliary functions === *)` banner.

- [ ] **Step 5.3: Update `WidthUpperBound.v` imports**

```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices upper_bound.HallDefect upper_bound.BaseCases upper_bound.Iter.
```

- [ ] **Step 5.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

References to `Nat_le_of_succ_le`, `chain_root_aux`, `depth_aux` in the remaining (still-monolithic) `*_chain_assignment_exists` proofs now resolve to `Iter.<name>`. Since these were used unqualified inside the same Section, the `From Dilworth Require Import upper_bound.Iter.` brings them back into scope unqualified.

- [ ] **Step 5.5: Commit**

```bash
git add posets/dilworth/upper_bound/Iter.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): extract chain_root_aux/depth_aux to upper_bound/Iter.v

Moves the two Fixpoints used by the assignment proofs and the
Nat_le_of_succ_le helper. Parameter-free over R. No proof changes.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Introduce `upper_bound/HallKernel.v` (rename, no extraction yet)

**Files:**
- Create: `posets/dilworth/upper_bound/HallKernel.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

The kernel is just `above_chain_assignment_exists` renamed to `chain_assignment_kernel`, parameterized on its existing `R` (which we'll later instantiate with both `R` and `flip R`).

- [ ] **Step 6.1: Create `posets/dilworth/upper_bound/HallKernel.v`**

```coq
(* Parameterized chain-assignment kernel for Dilworth's backward direction.

   Given a poset R', a finite sub ⊆ Above R' la with la its largest antichain
   of size w, produces an assignment f : A → A with:
     - f x ∈ la and R' (f x) x for every x ∈ sub
     - the fiber {x ∈ sub | f x = a} is an R'-chain for every a ∈ la

   Cover.v applies this twice: once with R' := R (the Above case) and once
   with R' := flip R (the Below case). *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas Helpers Hall
                              upper_bound.Slices upper_bound.HallDefect
                              upper_bound.Iter.

Section HallKernel.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Lemma chain_assignment_kernel : forall (sub la : Ensemble A) (w : nat),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    (* Verbatim copy of the body of above_chain_assignment_exists from
       WidthUpperBound.v lines 653–1552. *)
  Qed.

End HallKernel.
```

To populate the proof, copy the body of `above_chain_assignment_exists` exactly as it stands today (the 900-line block). No changes to the proof in this task — only renaming the lemma.

- [ ] **Step 6.2: Update `above_chain_assignment_exists` in `WidthUpperBound.v` to be a thin wrapper**

Replace the 900-line `above_chain_assignment_exists` (lines 646–1553) with:
```coq
  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Habove HfinSub.
    exact (chain_assignment_kernel R sub la w Hla Habove HfinSub).
  Qed.
```

The `R` in the call is the explicit `R` parameter of `chain_assignment_kernel` (taken from `Section HallKernel`'s `Context (R : ...)`), which we satisfy by passing the `R` of the surrounding `Section DilworthBackward`. The `IsPoset` instance is found by typeclass resolution.

- [ ] **Step 6.3: Update `WidthUpperBound.v` imports**

Append `upper_bound.HallKernel`:
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices upper_bound.HallDefect upper_bound.BaseCases upper_bound.Iter upper_bound.HallKernel.
```

- [ ] **Step 6.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

This is the first proof-equivalent (not just textual) move; if it fails, the most likely cause is that an `assert` block inside the kernel body still references something via section-context shadowing that no longer resolves. In that case, the missing name will be in `Slices`, `HallDefect`, `BaseCases`, or `Iter` — explicitly qualify it (e.g., `Slices.la_in_Above`) until it resolves.

- [ ] **Step 6.5: Commit**

```bash
git add posets/dilworth/upper_bound/HallKernel.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): rename above-chain assignment to chain_assignment_kernel

Moves the 900-line proof body to upper_bound/HallKernel.v unchanged,
renamed as chain_assignment_kernel. above_chain_assignment_exists is
now a thin wrapper. Sets up Cover.v to apply the kernel twice (once
with R, once with flip R) in a later task.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Extract inner lemmas of the kernel

This task replaces the long anonymous `assert ... by { ... }` blocks inside `chain_assignment_kernel` with named `Lemma`s, all inside `Section HallKernel`. Each extraction is a separate sub-step + commit; if any sub-step breaks the build, that single extraction is reverted while the rest of the work stands.

**File:** `posets/dilworth/upper_bound/HallKernel.v`

Each inner lemma below is given its **statement** (so the engineer knows exactly what to write) and a pointer to the matching `assert` block in the original code (now inside `chain_assignment_kernel`). The proof of each is whatever was already inside the matching `assert`'s `by { ... }` brace block, lifted verbatim. The `assert` itself is then replaced with `pose proof (lemma_name args) as Hname.` (or just used inline).

Each extraction follows the **same micro-pattern**:
1. Add the new `Lemma` above `chain_assignment_kernel` inside `Section HallKernel`.
2. Replace the corresponding `assert ... by { ... }` block inside the kernel proof with a call to the new lemma.
3. Build.
4. Commit.

- [ ] **Step 7.1: Extract `inl_image_cardinal`**

Add inside `Section HallKernel`, before `chain_assignment_kernel`:
```coq
  (* The inl-image of a finite subset of A inside sum A A has the same cardinal. *)
  Lemma inl_image_cardinal : forall (S : Ensemble A) n,
    cardinal A S n ->
    cardinal (sum A A)
      (fun z => match z with inl y => In A S y | inr _ => False end) n.
  Proof.
    intros S n Hcard.
    induction Hcard as [| S' k Hcard' IH a Ha_notin].
    - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
      + intro z. split.
        * intro Hz. inversion Hz.
        * intro Hz. destruct z as [y|b]; simpl in Hz; inversion Hz.
      + apply card_empty.
    - apply (cardinal_extensional_poly (sum A A)
            (Add (sum A A)
              (fun z => match z with inl y => In A S' y | inr _ => False end)
              (inl a))).
      + intro z. split.
        * intro Hz. unfold Add in Hz.
          inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
          -- destruct z as [y | b].
             ++ apply Union_introl. simpl in Hu. exact Hu.
             ++ simpl in Hu. exact (False_rect _ Hu).
          -- inversion Hu. subst z. apply Union_intror. apply In_singleton.
        * intro Hz. destruct z as [y | b].
          -- simpl in Hz.
             inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
             ++ apply Union_introl. simpl. exact Hu.
             ++ inversion Hu. subst y. apply Union_intror. apply In_singleton.
          -- simpl in Hz. exact (False_rect _ Hz).
      + apply card_add. exact IH.
        intro Hcontra. simpl in Hcontra. exact (Ha_notin Hcontra).
  Qed.
```

In `chain_assignment_kernel`, find the **two** `assert (HcardInl ...) by { clear - Hcard_sub. induction Hcard_sub ... }` blocks (one for sub itself, one for `StrictPred sub S` inside the Hall condition). Replace each with:
```coq
      assert (HcardInl : cardinal (sum A A)
          (fun z => match z with inl y => In A sub y | inr _ => False end) nx)
        by exact (inl_image_cardinal sub nx Hcard_sub).
```
and analogously for `StrictPred sub S`:
```coq
      assert (HcardInlP : cardinal (sum A A)
          (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end) nP)
        by exact (inl_image_cardinal (StrictPred sub S) nP HcardSP).
```

Build (`mise run build-posets`); commit:
```bash
git commit -am "refactor(dilworth): extract inl_image_cardinal from HallKernel"
```

- [ ] **Step 7.2: Extract `inr_image_cardinal`**

Symmetric to Step 7.1:
```coq
  (* The inr-image of a finite subset of A inside sum A A has the same cardinal. *)
  Lemma inr_image_cardinal : forall (T : Ensemble A) n,
    cardinal A T n ->
    cardinal (sum A A)
      (fun z => match z with inl _ => False | inr a => In A T a end) n.
  Proof.
    intros T n Hcard.
    induction Hcard as [| T' k Hcard' IH a Ha_notin].
    - apply (cardinal_extensional_poly (sum A A) (Empty_set (sum A A))).
      + intro z. split.
        * intro Hz. inversion Hz.
        * intro Hz. destruct z as [y|b]; simpl in Hz; inversion Hz.
      + apply card_empty.
    - apply (cardinal_extensional_poly (sum A A)
            (Add (sum A A)
              (fun z => match z with inl _ => False | inr a => In A T' a end)
              (inr a))).
      + intro z. split.
        * intro Hz. unfold Add in Hz.
          inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
          -- destruct z as [y | b].
             ++ simpl in Hu. exact (False_rect _ Hu).
             ++ apply Union_introl. simpl in Hu. exact Hu.
          -- inversion Hu. subst z. apply Union_intror. apply In_singleton.
        * intro Hz. destruct z as [y | b].
          -- simpl in Hz. exact (False_rect _ Hz).
          -- simpl in Hz.
             inversion Hz as [u Hu Heq | u Hu Heq]; subst u.
             ++ apply Union_introl. simpl. exact Hu.
             ++ inversion Hu. subst b. apply Union_intror. apply In_singleton.
      + apply card_add. exact IH.
        intro Hcontra. simpl in Hcontra. exact (Ha_notin Hcontra).
  Qed.
```

Replace the two `assert (HcardInr ...)` and `assert (HcardInrLa ...)` blocks (in the kernel) with calls to `inr_image_cardinal la w Hcard_la`.

Build; commit:
```bash
git commit -am "refactor(dilworth): extract inr_image_cardinal from HallKernel"
```

- [ ] **Step 7.3: Extract `Y_cardinal`**

```coq
  (* The augmented right-side Y = inl-image(sub) ⊎ inr-image(la) has cardinal nx + w. *)
  Lemma Y_cardinal : forall (sub la : Ensemble A) nx w,
    cardinal A sub nx ->
    cardinal A la w ->
    cardinal (sum A A)
      (fun z : sum A A =>
        match z with inl y => In A sub y | inr a => In A la a end)
      (nx + w).
  Proof.
    intros sub la nx w Hcard_sub Hcard_la.
    apply (cardinal_extensional_poly (sum A A)
        (Union (sum A A)
          (fun z => match z with inl y => In A sub y | inr _ => False end)
          (fun z => match z with inl _ => False | inr a => In A la a end))).
    - intro z. split; intro Hz.
      + destruct z as [y | a].
        * inversion Hz as [u Hu | u Hu]; subst u; simpl in Hu; [exact Hu | exact (False_rect _ Hu)].
        * inversion Hz as [u Hu | u Hu]; subst u; simpl in Hu; [exact (False_rect _ Hu) | exact Hu].
      + destruct z as [y | a].
        * apply Union_introl. exact Hz.
        * apply Union_intror. exact Hz.
    - apply cardinal_disjoint_union_gen.
      + intros z Hl Hr. destruct z; simpl in *; [exact Hr | exact Hl].
      + exact (inl_image_cardinal sub nx Hcard_sub).
      + exact (inr_image_cardinal la w Hcard_la).
  Qed.
```

Replace the `assert (HcardY ...)` block inside `chain_assignment_kernel` with `pose proof (Y_cardinal sub la nx w Hcard_sub Hcard_la) as HcardY.`. Note: the inner `Y` set in the kernel is defined using `set Y := ...`; the `pose proof` form gives the same cardinal proposition for the same definitionally-equal set.

Build; commit:
```bash
git commit -am "refactor(dilworth): extract Y_cardinal from HallKernel"
```

- [ ] **Step 7.4: Extract `nbrs_aug_neighbors_eq`**

```coq
  (* set_neighbors of the augmented matching graph decomposes as
     inl(StrictPred sub S) ⊎ inr(la) for any nonempty S ⊆ sub. *)
  Lemma nbrs_aug_neighbors_eq : forall (sub la : Ensemble A)
      (nbrs_aug : A -> sum A A -> Prop),
    (forall x z, nbrs_aug x z <->
       match z with
       | inl y => In A sub y /\ R y x /\ y <> x
       | inr a => In A la a
       end) ->
    forall S,
    Inhabited A S ->
    set_neighbors nbrs_aug S =
      Union (sum A A)
        (fun z => match z with inl y => In A (StrictPred sub S) y | inr _ => False end)
        (fun z => match z with inl _ => False | inr a => In A la a end).
  Proof.
    intros sub la nbrs_aug Hnbrs S HinhS.
    apply Extensionality_Ensembles. intro z. split.
    - intros [x [Hx Hz]]. apply Hnbrs in Hz.
      destruct z as [y | a].
      + apply Union_introl. unfold StrictPred.
        destruct Hz as [Hy [HRyx Hne]].
        exact (conj Hy (ex_intro _ x (conj Hx (conj HRyx (fun h => Hne (eq_sym h)))))).
      + apply Union_intror. exact Hz.
    - intro Hz. inversion Hz as [z' Hz' | z' Hz']; subst.
      + destruct z as [y | a]. 2: exact (False_rect _ Hz').
        simpl in Hz'. unfold StrictPred in Hz'.
        destruct Hz' as [Hy [x [Hx [HRyx Hne]]]].
        exists x. split. exact Hx. apply Hnbrs.
        exact (conj Hy (conj HRyx (fun h => Hne (eq_sym h)))).
      + destruct z as [y | a]. exact (False_rect _ Hz').
        simpl in Hz'.
        destruct HinhS as [x0 Hx0].
        exists x0. split. exact Hx0. apply Hnbrs. exact Hz'.
  Qed.
```

Replace the matching `assert (Hset_eq : set_neighbors nbrs_aug S = ...) by { ... }` block in the kernel with `pose proof (nbrs_aug_neighbors_eq sub la nbrs_aug (fun x z => iff_refl _) S HinhS) as Hset_eq.`. (The `nbrs_aug` is `set` locally so the iff is `iff_refl`.)

Build; commit:
```bash
git commit -am "refactor(dilworth): extract nbrs_aug_neighbors_eq from HallKernel"
```

- [ ] **Step 7.5: Extract `hall_condition_holds`**

The proof body to use is the existing `assert (Hhall : HallCondition sub nbrs_aug) by { ... }` block — currently lines 770–882 of the pre-refactor `WidthUpperBound.v`, now living inside `chain_assignment_kernel`. The block already proves exactly what `hall_condition_holds` claims, parameterized over the same `nbrs_aug`.

Add the lemma above `chain_assignment_kernel`:

```coq
  (* Hall's marriage condition for the augmented matching graph,
     discharged via dilworth_hall_defect_pred. *)
  Lemma hall_condition_holds : forall (sub la : Ensemble A) w
      (nbrs_aug : A -> sum A A -> Prop),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    cardinal A la w ->
    (forall x z, nbrs_aug x z <->
       match z with
       | inl y => In A sub y /\ R y x /\ y <> x
       | inr a => In A la a
       end) ->
    HallCondition sub nbrs_aug.
  Proof.
    intros sub la w nbrs_aug Hla Habove HfinSub Hcard_la Hnbrs.
    (* Lift the body of the kernel's `assert (Hhall : HallCondition sub nbrs_aug) by { ... }`
       verbatim. The lifted block uses Hla, Habove, Hcard_la, and Hnbrs to access nbrs_aug
       membership; the kernel's `Hla'` becomes Hla here. The block's final step
       `apply (dilworth_hall_defect_pred sub la w Hla' Habove S _ nP)` becomes
       `apply (dilworth_hall_defect_pred sub la w Hla Habove S _ nP)`. *)
    (* TODO(implementer): paste the lifted body here, then build. *)
  Qed.
```

Replace the kernel's `assert (Hhall : HallCondition sub nbrs_aug) by { ... }` block with:
```coq
    assert (Hhall : HallCondition sub nbrs_aug)
      by exact (hall_condition_holds sub la w nbrs_aug Hla' Habove HfinSub Hcard_la
                  (fun x z => iff_refl _)).
```

(The `iff_refl` works because `nbrs_aug` was introduced by `set nbrs_aug := ...`, so the iff-form unfolds to the same definition.)

Build; commit:
```bash
git commit -am "refactor(dilworth): extract hall_condition_holds from HallKernel"
```

- [ ] **Step 7.6: Extract `la_assigned_to_dummy`**

```coq
  (* la-elements always match a dummy node: m_aug a is some inr k. *)
  Lemma la_assigned_to_dummy : forall (sub la : Ensemble A) w (m_aug : A -> sum A A),
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    forall a, In A la a ->
    exists k, In A la k /\ m_aug a = inr k.
  Proof.
    intros sub la w m_aug Hla Habove Hm_match a Ha.
    (* Lift the body of the kernel's `assert (Hla_dummy ...) by { ... }` block
       (currently lines 891–906 of pre-refactor WidthUpperBound.v) verbatim.
       Replace `Hla'` with Hla and `Hm_nbrs` lookups with Hm_match. *)
    (* TODO(implementer): paste the lifted body here, then build. *)
  Qed.
```

Replace the kernel's `assert (Hla_dummy ...) by { ... }` with:
```coq
    pose proof (la_assigned_to_dummy sub la w m_aug Hla' Habove
                  (fun x Hx => Hstep_R x Hx)) as Hla_dummy.
```
(`Hstep_R` is the kernel-local `assert` that captures the same per-element matching invariant.)

Build; commit:
```bash
git commit -am "refactor(dilworth): extract la_assigned_to_dummy from HallKernel"
```

- [ ] **Step 7.7: Extract `dummy_target_in_la`**

```coq
  (* Any sub-element matched to a dummy node is itself in la
     (by surjectivity of the la-restriction of m_aug). *)
  Lemma dummy_target_in_la : forall (sub la : Ensemble A) w (m_aug : A -> sum A A),
    cardinal A la w ->
    Included A la sub ->
    (forall x y, In A sub x -> In A sub y -> m_aug x = m_aug y -> x = y) ->
    (forall a, In A la a -> exists k, In A la k /\ m_aug a = inr k) ->
    forall z, In A sub z ->
    (exists d, m_aug z = inr d) ->
    In A la z.
  Proof.
    intros sub la w m_aug Hcard_la Hincl_la Hm_inj Hla_dummy z Hz Hzd.
    (* Lift the body of the kernel's `assert (Hdummy_means_la ...) by { ... }` block
       (currently lines 909–958 of pre-refactor WidthUpperBound.v) verbatim.
       The lifted block uses Hla_dummy / Hm_inj / Hcard_la / Hincl_la in place of
       the kernel's locally-named identical hypotheses. *)
    (* TODO(implementer): paste the lifted body here, then build. *)
  Qed.
```

Replace the kernel's `assert (Hdummy_means_la ...) by { ... }` with:
```coq
    pose proof (dummy_target_in_la sub la w m_aug Hcard_la Hincl_la Hm_inj Hla_dummy)
      as Hdummy_means_la.
```

Build; commit:
```bash
git commit -am "refactor(dilworth): extract dummy_target_in_la from HallKernel"
```

- [ ] **Step 7.8: Extract `chain_terminates`**

```coq
  (* Iterating the matching from any sub-element reaches la within nx steps,
     and the final element relates to the start via R. *)
  Lemma chain_terminates : forall (sub la : Ensemble A) w (m_aug : A -> sum A A) nx,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    cardinal A sub nx ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    (forall x y, In A sub x -> In A sub y -> m_aug x = m_aug y -> x = y) ->
    (forall a, In A la a -> exists k, In A la k /\ m_aug a = inr k) ->
    forall x, In A sub x ->
    In A la (chain_root_aux m_aug nx x) /\ R (chain_root_aux m_aug nx x) x.
  Proof.
    intros sub la w m_aug nx Hla Habove Hcard_sub Hstep_R Hm_inj Hla_dummy x Hx.
    (* Lift the body of the kernel's `assert (Hf_assign : forall x, ...) by { ... }`
       block (currently lines 1025–1333 of pre-refactor WidthUpperBound.v) verbatim.
       The lifted block uses Hla, Habove, Hcard_sub, Hstep_R, Hm_inj, Hla_dummy
       in place of the kernel's locally-named identical hypotheses.
       This is the longest single lift (~310 lines); preserve every line. *)
    (* TODO(implementer): paste the lifted body here, then build. *)
  Qed.
```

Replace the kernel's `assert (Hf_assign ...) by { ... }` with:
```coq
    pose proof (chain_terminates sub la w m_aug nx Hla' Habove Hcard_sub
                  Hstep_R Hm_inj Hla_dummy) as Hf_assign.
```
(Within the kernel, `f` is `set f := fun x => chain_root_aux m_aug nx x`, so `Hf_assign` as returned matches the form `f x ∈ la ∧ R (f x) x` definitionally.)

Build; commit:
```bash
git commit -am "refactor(dilworth): extract chain_terminates from HallKernel"
```

- [ ] **Step 7.9: Extract `fiber_chain`**

```coq
  (* Two sub-elements assigned to the same la-target are R-comparable. *)
  Lemma fiber_chain : forall (sub la : Ensemble A) w (m_aug : A -> sum A A) nx,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    cardinal A sub nx ->
    (forall x, In A sub x ->
      match m_aug x with
      | inl y => In A sub y /\ R y x /\ y <> x
      | inr a => In A la a
      end) ->
    (forall x y, In A sub x -> In A sub y -> m_aug x = m_aug y -> x = y) ->
    (forall a, In A la a -> exists k, In A la k /\ m_aug a = inr k) ->
    (forall a, In A la a -> chain_root_aux m_aug nx a = a) ->
    (forall x, In A sub x ->
       In A la (chain_root_aux m_aug nx x) /\ R (chain_root_aux m_aug nx x) x) ->
    forall a, In A la a ->
    IsChain R (fun x => In A sub x /\ chain_root_aux m_aug nx x = a).
  Proof.
    intros sub la w m_aug nx Hla Habove Hcard_sub Hstep_R Hm_inj Hla_dummy Hf_la Hf_assign a Ha.
    (* Lift the body of the kernel's `assert (Hf_chain : forall a, ...) by { ... }`
       block (currently lines 1336–1550 of pre-refactor WidthUpperBound.v) verbatim.
       Renames: kernel's Hla' → Hla; the rest are name-identical. The block
       references Hf_assign internally; that's the last hypothesis we added here. *)
    (* TODO(implementer): paste the lifted body here, then build. *)
  Qed.
```

Replace the kernel's `assert (Hf_chain ...) by { ... }` with:
```coq
    pose proof (fiber_chain sub la w m_aug nx Hla' Habove Hcard_sub
                  Hstep_R Hm_inj Hla_dummy Hf_la Hf_assign) as Hf_chain.
```

Build; commit:
```bash
git commit -am "refactor(dilworth): extract fiber_chain from HallKernel"
```

After all 9 sub-steps, `chain_assignment_kernel`'s body should be roughly 50 lines: variable destructure → call inner lemmas → `exact (ex_intro _ f (conj Hf_assign Hf_chain))`.

---

## Task 8: Move Above-side cover lemmas to `upper_bound/Cover.v`

**Files:**
- Create: `posets/dilworth/upper_bound/Cover.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Moving (Above only — Below stays in WidthUpperBound.v for one more task):**
- `above_chain_assignment_exists` (now a 2-line wrapper)
- `chain_cover_above_existence` (lines 1555–1588)
- `chain_cover_of_above` (lines 1590–1603)
- `extend_cover_above` (lines 2418–2429)

- [ ] **Step 8.1: Create `posets/dilworth/upper_bound/Cover.v`**

```coq
(* Chain covers derived from the assignment kernel.

   The Above variant applies chain_assignment_kernel directly with R.
   The Below variant (added in the next task) applies it with flip R,
   using small duality lemmas to translate hypotheses and conclusions. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas Helpers
                              upper_bound.Slices upper_bound.HallDefect
                              upper_bound.BaseCases upper_bound.HallKernel.

Section Cover.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Habove HfinSub.
    exact (chain_assignment_kernel R sub la w Hla Habove HfinSub).
  Qed.

  (* ... copy chain_cover_above_existence verbatim from WidthUpperBound.v ... *)
  (* ... copy chain_cover_of_above verbatim ... *)
  (* ... copy extend_cover_above verbatim ... *)

End Cover.
```

- [ ] **Step 8.2: Remove the moved lemmas from `WidthUpperBound.v`**

Delete the wrapper `above_chain_assignment_exists`, `chain_cover_above_existence`, `chain_cover_of_above`, and `extend_cover_above`. Leave `below_chain_assignment_exists`, `chain_cover_of_below`, and `extend_cover_below` in place (Task 9 handles them).

- [ ] **Step 8.3: Update `WidthUpperBound.v` imports**

```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall upper_bound.Slices upper_bound.HallDefect upper_bound.BaseCases upper_bound.Iter upper_bound.HallKernel upper_bound.Cover.
```

- [ ] **Step 8.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

- [ ] **Step 8.5: Commit**

```bash
git add posets/dilworth/upper_bound/Cover.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): move Above-side cover lemmas to upper_bound/Cover.v

above_chain_assignment_exists now applies chain_assignment_kernel
directly. chain_cover_above_existence, chain_cover_of_above,
extend_cover_above moved unchanged.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Switch Below-side proofs to use the kernel via `flip R`

This is the highest-risk single step in the refactor. It's isolated so a revert leaves all earlier work intact.

**Files:**
- Modify: `posets/dilworth/upper_bound/Cover.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Strategy:** Add `flip_IsPoset` and four duality lemmas at the top of `Cover.v`. Rewrite `below_chain_assignment_exists` as a wrapper that converts hypotheses through the duality lemmas, calls `chain_assignment_kernel` instantiated at `flip R`, and converts the conclusion back. Move `chain_cover_of_below` and `extend_cover_below` verbatim.

- [ ] **Step 9.1: Add `flip_IsPoset` and duality lemmas at the top of `Cover.v`**

Insert at the top of the file, before `Section Cover`:

```coq
(* Duality plumbing: every R-poset gives a flip R-poset, and Above/Below,
   IsAntichain, IsChain, IsLargestAntichain are all symmetric in R vs flip R. *)

#[local] Instance flip_IsPoset {A} (R : A -> A -> Prop) `{IsPoset A R}
  : IsPoset A (flip R).
Proof.
  unfold flip. constructor.
  - intro x. apply poset_refl.
  - intros x y Hxy Hyx. apply (poset_antisym x y); assumption.
  - intros x y z Hxy Hyz. exact (poset_trans z y x Hyz Hxy).
Defined.

Section Duality.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  Lemma Above_flip_eq_Below : forall (s : Ensemble A),
    Above (flip R) s = Below R s.
  Proof.
    intro s. apply Extensionality_Ensembles. intro x. split.
    - intros [y [Hy Hflip]]. exact (ex_intro _ y (conj Hy Hflip)).
    - intros [y [Hy HR]]. exact (ex_intro _ y (conj Hy HR)).
  Qed.

  Lemma IsAntichain_flip_iff : forall (s : Ensemble A),
    IsAntichain R s <-> IsAntichain (flip R) s.
  Proof.
    intro s. split; intros [Hinh Hinc]; constructor; try exact Hinh;
      intros x y Hx Hy [Hr | Hr]; (apply Hinc; [exact Hx | exact Hy |]);
      [right | left | right | left]; exact Hr.
  Qed.

  Lemma IsChain_flip_iff : forall (s : Ensemble A),
    IsChain R s <-> IsChain (flip R) s.
  Proof.
    intro s. split; intros [Hinh Hcomp]; constructor; try exact Hinh;
      intros x y Hx Hy; destruct (Hcomp x y Hx Hy) as [Hr | Hr];
      [right | left | right | left]; exact Hr.
  Qed.

  Lemma IsLargestAntichain_flip_iff : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w <-> IsLargestAntichain (flip R) sub la w.
  Proof.
    intros sub la w. split; intros [Hanti Hincl Hcard Hmax]; constructor.
    - exact (proj1 (IsAntichain_flip_iff la) Hanti).
    - exact Hincl.
    - exact Hcard.
    - intros s n Hs Hsincl Hsn.
      apply (Hmax s n); [exact (proj2 (IsAntichain_flip_iff s) Hs) | exact Hsincl | exact Hsn].
    - exact (proj2 (IsAntichain_flip_iff la) Hanti).
    - exact Hincl.
    - exact Hcard.
    - intros s n Hs Hsincl Hsn.
      apply (Hmax s n); [exact (proj1 (IsAntichain_flip_iff s) Hs) | exact Hsincl | exact Hsn].
  Qed.

End Duality.
```

- [ ] **Step 9.2: Inside `Section Cover`, add `below_chain_assignment_exists` as a kernel wrapper**

Append below `extend_cover_above`:

```coq
  Lemma below_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    Finite A sub ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R x (f x)) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Hbelow HfinSub.
    assert (Hla_flip : IsLargestAntichain (flip R) sub la w)
      by exact (proj1 (IsLargestAntichain_flip_iff R sub la w) Hla).
    assert (Habove_flip : Included A sub (Above (flip R) la)).
    { rewrite (Above_flip_eq_Below R la). exact Hbelow. }
    destruct (chain_assignment_kernel (flip R) sub la w Hla_flip Habove_flip HfinSub)
      as [f [Hf_assign Hf_chain]].
    exists f. split.
    - intros x Hx. destruct (Hf_assign x Hx) as [HfaIn HfR].
      split; [exact HfaIn | exact HfR].   (* flip R (f x) x ≡ R x (f x) *)
    - intros a Ha. exact (proj2 (IsChain_flip_iff R _) (Hf_chain a Ha)).
  Qed.
```

The kernel's `R` is its first explicit positional argument (from `Section HallKernel`'s `Context (R : ...)`), so we pass `flip R` directly. The `IsPoset (flip R)` instance comes from `flip_IsPoset` declared above the section.

- [ ] **Step 9.3: Move `chain_cover_of_below` and `extend_cover_below` to `Cover.v`**

Copy the bodies of `chain_cover_of_below` (lines 2386–2416) and `extend_cover_below` (lines 2431–2442) verbatim from `WidthUpperBound.v` to the bottom of `Section Cover`.

- [ ] **Step 9.4: Remove `below_chain_assignment_exists`, `chain_cover_of_below`, `extend_cover_below` from `WidthUpperBound.v`**

The corresponding ranges (1605–2384, 2386–2416, 2431–2442) all go away.

- [ ] **Step 9.5: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

If this fails, the most likely causes:
- `flip` is not unfolded automatically: insert `unfold flip in *` or add explicit conversion lemmas.
- `IsLargestAntichain (flip R)` not found: check `flip_IsPoset` is `#[local]` not `#[global]` (avoiding ambiguity) but visible via `Existing Instance`.
- `R x (f x)` vs `flip R (f x) x` mismatch: insert `unfold flip` or use `change` tactic.

If the failure can't be resolved within 30 minutes, **revert this commit only** — Tasks 1–8 stand and the project still builds.

- [ ] **Step 9.6: Commit**

```bash
git add posets/dilworth/upper_bound/Cover.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): derive Below-side cover from kernel via flip R

below_chain_assignment_exists now reuses chain_assignment_kernel
instantiated at flip R, eliminating ~780 lines of near-duplicate
proof. Adds flip_IsPoset and four small duality lemmas.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: Move the merge lemma to `upper_bound/Merge.v`

**Files:**
- Create: `posets/dilworth/upper_bound/Merge.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Moving:**
- `merge_above_below_covers` (lines 2448–2674)

- [ ] **Step 10.1: Create `posets/dilworth/upper_bound/Merge.v`**

```coq
(* Combine Above- and Below-side chain covers into a single chain cover of sub.
   Used by dilworth_inductive_step when neither sub ⊆ Above(la) nor sub ⊆ Below(la). *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas Helpers
                              upper_bound.Slices.

Section Merge.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* ... copy merge_above_below_covers verbatim from WidthUpperBound.v lines 2448–2674 ... *)

End Merge.
```

- [ ] **Step 10.2: Remove `merge_above_below_covers` from `WidthUpperBound.v`**

Delete lines 2448–2674.

- [ ] **Step 10.3: Update `WidthUpperBound.v` imports**

Append `upper_bound.Merge`:
```coq
From Dilworth Require Import ... upper_bound.HallKernel upper_bound.Cover upper_bound.Merge.
```

- [ ] **Step 10.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

- [ ] **Step 10.5: Commit**

```bash
git add posets/dilworth/upper_bound/Merge.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): extract merge_above_below_covers to upper_bound/Merge.v

No proof changes.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Move `dilworth_inductive_step` and `DilworthB` to `upper_bound/Backward.v`

**Files:**
- Create: `posets/dilworth/upper_bound/Backward.v`
- Modify: `posets/dilworth/WidthUpperBound.v`

**Moving:**
- `dilworth_inductive_step` (lines 2680–2733)
- `DilworthB` (lines 2739–2783)

After this task, `WidthUpperBound.v`'s body is empty (only imports + facade re-exports).

- [ ] **Step 11.1: Create `posets/dilworth/upper_bound/Backward.v`**

```coq
(* The backward direction of Dilworth's theorem:
   any subposet with largest antichain of size w admits a chain cover of size w.
   Proceeds by strong induction on |sub|, using merge_above_below_covers
   to combine Above- and Below-side covers when sub straddles la. *)

From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple
                              CardinalLemmas WidthLowerBound Helpers Hall
                              upper_bound.Slices upper_bound.HallDefect
                              upper_bound.BaseCases upper_bound.Iter
                              upper_bound.HallKernel upper_bound.Cover
                              upper_bound.Merge.

Section Backward.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* ... copy dilworth_inductive_step verbatim from WidthUpperBound.v lines 2680–2733 ... *)

  (* ... copy DilworthB verbatim from lines 2739–2783 ... *)

End Backward.
```

- [ ] **Step 11.2: Remove the moved lemmas from `WidthUpperBound.v`**

Delete lines 2680–2783, plus the section banners. The file should now contain only imports, an empty `Section DilworthBackward` (or no section at all), and `End DilworthBackward.` (if any).

- [ ] **Step 11.3: Convert `WidthUpperBound.v` to a facade**

Replace the entire `WidthUpperBound.v` with:

```coq
(* WidthUpperBound — facade.
   The proof is split across the upper_bound/ subdirectory; see
   docs/superpowers/specs/2026-05-01-widthupperbound-refactor-design.md
   for the file map. External clients that previously imported
   WidthUpperBound continue to work unchanged. *)

From Dilworth Require Export
  upper_bound.Slices
  upper_bound.HallDefect
  upper_bound.BaseCases
  upper_bound.Iter
  upper_bound.HallKernel
  upper_bound.Cover
  upper_bound.Merge
  upper_bound.Backward.
```

`Require Export` (not `Require Import`) ensures every name previously in scope for clients of `WidthUpperBound` remains in scope.

- [ ] **Step 11.4: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!`

The two external consumers — `DilworthTheorem.v` and `Examples.v` — should compile unchanged because `DilworthB` is exported through `upper_bound.Backward → WidthUpperBound`.

- [ ] **Step 11.5: Commit**

```bash
git add posets/dilworth/upper_bound/Backward.v posets/dilworth/WidthUpperBound.v
git commit -m "$(cat <<'EOF'
refactor(dilworth): move DilworthB to upper_bound/Backward, WidthUpperBound is now a facade

WidthUpperBound.v is reduced to Require Export of the upper_bound/
modules. DilworthB and dilworth_inductive_step live in
upper_bound.Backward. Public API unchanged.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Trim narrative comments

This is the only task that changes proof text outside of structure. It is **optional** — if any earlier task ran into trouble and the schedule is tight, skip it.

**Files:**
- Modify: `posets/dilworth/upper_bound/HallKernel.v` (most of the trimmed comments live here)
- Modify (light): the other `upper_bound/*.v` files

**Policy** (from spec):
- Keep the 2–4 line file header on each file.
- Keep at most one short comment (≤ 2 lines) per non-trivial lemma, capturing the *why*.
- Remove inline narrative that describes what the next 5 lines do (it rots fast and is rarely useful when reading the proof).
- Remove the long English explanations that wandered through proof strategy mid-proof (e.g., the original lines 1099–1226 narrating the two cases of the "does the chain reach la" disjunction). Replace them with at most one sentence above the matching `destruct (classic ...) as [Hstop | Hnostop].`.

- [ ] **Step 12.1: Trim `HallKernel.v`**

Walk the file from top to bottom. For each comment block:
- If it's a 2–4 line lemma-purpose comment → keep.
- If it's a 1–2 line tactical hint that names an invariant → keep.
- If it's English narration of what the next few lines do → delete.
- If it's a multi-paragraph proof-strategy explanation → reduce to one sentence summarizing the strategy.

- [ ] **Step 12.2: Trim other `upper_bound/*.v` files**

Apply the same policy. Most of these files have far less narrative and should need only minor edits.

- [ ] **Step 12.3: Build**

Run: `mise run build-posets`
Expected: `✅ Build successful!` (comment changes can't break the build, but rerun to confirm.)

- [ ] **Step 12.4: Commit**

```bash
git add posets/dilworth/upper_bound/
git commit -m "$(cat <<'EOF'
refactor(dilworth): trim narrative comments inside upper_bound/

Removes redundant English explanations of what the proof is about
to do; keeps short why-comments above non-trivial lemmas.

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
EOF
)"
```

---

## Verification checklist (after Task 11 — refactor is structurally complete)

- [ ] `mise run build-posets` is green.
- [ ] `git diff main -- posets/dilworth/DilworthTheorem.v posets/dilworth/Examples.v posets/dilworth/Package.v` is empty (external consumers untouched).
- [ ] `wc -l posets/dilworth/WidthUpperBound.v` shows ≤ 20 lines.
- [ ] `wc -l posets/dilworth/upper_bound/*.v` shows the largest single file ≤ ~700 lines.
- [ ] `git log --oneline | head -15` shows ~12 small commits, each with a passing build.
- [ ] No file has `Admitted` (verify with `grep -RnE 'Admitted' posets/dilworth/`).

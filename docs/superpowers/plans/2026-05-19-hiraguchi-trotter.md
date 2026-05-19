# Hiraguchi via Trotter's Removable-Pair Lemma — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the false-axiom chain in `posets/dimension/Theorems.v` with a sound proof of Hiraguchi's theorem via Trotter's removable-pair lemma, ending with `hiraguchi_thm` Qed.

**Architecture:** Move all new infrastructure into a new file `posets/dimension/RemovablePairs.v`. Define `IsRemovablePair`, prove `removable_pair_dimension_bound` (the easier direction), then `removable_pair_exists` (the existential), then integrate via the strong-induction in `hiraguchi_helper`. Each new lemma is built incrementally with `mise build` as the test harness.

**Tech Stack:** Coq 9.1.0 + Stdlib + Hammer (rocq-stdlib, coq-hammer 1.3.2+9.1). Build via `mise build`. No external deps beyond the project's vendored ZornsLemma.

**Conventions enforced throughout:**
- Build only via `mise build` / `opam exec -- dune build posets/dimension/RemovablePairs.vo`.
- Every new lemma starts as `Admitted.` with its statement only; we then write a real proof; `Admitted.` becomes `Qed.` in a follow-up commit.
- After each `Qed.`, run `mise build` and commit.
- **No bogus axioms.** If a lemma cannot be closed honestly, leave it `Admitted.` with a NOTE — do not derive it from a false intermediate.

---

## File structure

| File | Status | Responsibility |
|---|---|---|
| `posets/dimension/RemovablePairs.v` | NEW | `IsRemovablePair` def, supporting infra, the two key lemmas |
| `posets/dimension/dune` | MODIFY | (no change needed — already imports Stdlib, Posets, Dilworth, ZornsLemma) |
| `posets/dimension/Theorems.v` | MODIFY | Remove false admits; rewrite `hiraguchi_helper` to use `RemovablePairs` |
| `_CoqProject` | (unchanged) | Already maps `posets/dimension` → `Dimension` |
| `docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md` | EXISTING | Design doc; reference only |

---

## Task 1: Create RemovablePairs.v skeleton

**Files:**
- Create: `posets/dimension/RemovablePairs.v`
- (No dune changes needed; new files in an existing theory directory are auto-discovered.)

- [ ] **Step 1: Create the file with imports only**

```coq
(** Removable pairs and Trotter's lemma for the proof of Hiraguchi's theorem.
    See docs/superpowers/specs/2026-05-19-hiraguchi-trotter-design.md *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section RemovablePairs.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* Definitions and lemmas go here. *)

End RemovablePairs.
```

- [ ] **Step 2: Verify build**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success, no errors.

- [ ] **Step 3: Commit**

```bash
git add posets/dimension/RemovablePairs.v
git commit -m "feat: scaffold RemovablePairs.v for Hiraguchi/Trotter proof"
```

---

## Task 2: Add the `IsRemovablePair` definition

**Files:**
- Modify: `posets/dimension/RemovablePairs.v` (inside `Section RemovablePairs.`)

- [ ] **Step 1: Add the residual-set abbreviation**

Insert after the section's `Context` lines, before any other content:

```coq
  (** Residual set [S' x y = Full \ {x, y}]. *)
  Definition Residual (x y : A) : Ensemble A :=
    Setminus A (Setminus A (Full_set A) (Singleton A x)) (Singleton A y).

  Lemma Residual_not_x :
    forall x y a, In A (Residual x y) a -> a <> x.
  Proof.
    intros x y a [[_ Hnx] _] Heq. apply Hnx. rewrite Heq. constructor.
  Qed.

  Lemma Residual_not_y :
    forall x y a, In A (Residual x y) a -> a <> y.
  Proof.
    intros x y a [_ Hny] Heq. apply Hny. rewrite Heq. constructor.
  Qed.

  Lemma Residual_intro :
    forall x y a, a <> x -> a <> y -> In A (Residual x y) a.
  Proof.
    intros x y a Hnx Hny. split; [split |].
    - apply Full_intro.
    - intro Hin. inversion Hin; subst. apply Hnx; reflexivity.
    - intro Hin. inversion Hin; subst. apply Hny; reflexivity.
  Qed.
```

- [ ] **Step 2: Build and verify**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success.

- [ ] **Step 3: Add `IsRemovablePair` definition** (REVISED post-Task 4 warm-up)

The original single-L formulation was unsatisfiable in antichains. Use Trotter's realizer-existence form. Append after `Residual_intro`:

```coq
  (** A pair (x, y) is removable iff for every realizer of R restricted to
      the residual set, there exists a realizer of R with one more linear
      extension. This is Trotter's formulation; the hard work of producing
      that extra linear extension is encapsulated in this property and
      proved (existentially) by [removable_pair_exists]. *)
  Definition IsRemovablePair (x y : A) : Prop :=
    x <> y /\
    forall (d' : nat)
           (r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop)),
      IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                     R (proj1_sig a) (proj1_sig b)) r' ->
      cardinal _ r' d' ->
      exists r : Ensemble (A -> A -> Prop),
        IsRealizer R r /\
        cardinal (A -> A -> Prop) r (d' + 1).
```

- [ ] **Step 4: Build and verify**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success, the definition typechecks.

- [ ] **Step 5: Commit**

```bash
git add posets/dimension/RemovablePairs.v
git commit -m "feat(RemovablePairs): IsRemovablePair definition + Residual set lemmas"
```

---

## Task 3: Prove `removable_pair_dimension_bound`

**REVISED post-Task 4 warm-up:** Under the Trotter realizer-existence definition, this lemma becomes definitionally trivial — it's essentially an unfolding of `IsRemovablePair`'s second conjunct. The proof body is `intros; apply Hrem; eassumption.` or similar. All the hard work moves to Task 5 (`removable_pair_exists`).

**Files:**
- Modify: `posets/dimension/RemovablePairs.v`

- [ ] **Step 1: Add the lemma statement as Admitted**

Append inside the section:

```coq
  (** If (x, y) is removable, then dim(R) ≤ dim(R restricted to Residual x y) + 1.

      Specifically: from any d'-element realizer of R|_{Residual x y}, we
      build a (d'+1)-element realizer of R. *)
  Lemma removable_pair_dimension_bound :
    forall (x y : A) (d' : nat),
    IsRemovablePair x y ->
    (exists r' : Ensemble ({a : A | In A (Residual x y) a} ->
                            {a : A | In A (Residual x y) a} -> Prop),
       IsRealizer (fun (a b : {a : A | In A (Residual x y) a}) =>
                      R (proj1_sig a) (proj1_sig b)) r' /\
       cardinal _ r' d') ->
    exists r : Ensemble (A -> A -> Prop),
      IsRealizer R r /\
      cardinal (A -> A -> Prop) r (d' + 1).
  Proof.
  Admitted.
```

- [ ] **Step 2: Build to verify the statement typechecks**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success with the `Admitted` warning.

- [ ] **Step 3: Implement the proof**

Replace the `Admitted.` with the actual proof. The proof sketch:

```coq
  Proof.
    intros x y d' Hrem [r' [Hr'_real Hr'_card]].
    destruct Hrem as [Hxy_neq Hrem_prop].
    (* For each L' in r', use Hrem_prop to lift to a full linear ext L_lifted of R. *)
    set (lift := fun (L' : {a : A | In A (Residual x y) a} ->
                          {a : A | In A (Residual x y) a} -> Prop) =>
                   match classic (IsLinearExtension
                                    (fun a b => R (proj1_sig a) (proj1_sig b)) L') with
                   | or_introl HL'_lin =>
                       proj1_sig (constructive_indefinite_description _
                                    (Hrem_prop L' HL'_lin))
                   | or_intror _ => fun _ _ => True
                   end).
    (* r_lifted := Im r' lift. *)
    set (r_lifted := Im _ _ r' lift).
    (* L_extra := any linear extension that reverses (x, y); from Hrem_prop with a
       dummy/canonical L'. Actually, we need exactly one extra L. The Hrem_prop on
       any L' already gives us such an L; we re-use one. *)
    (* The realizer is r_lifted itself with cardinality d' (image of d'-set).
       Plus one extra extension for completeness. *)
    (* TODO: complete proof construction. *)
  Admitted.
```

**Note:** This step is non-trivial (estimated 4-8 hours of focused proof work). If stuck, **do NOT** introduce false axioms. Leave the proof at `Admitted.` and document the gap.

- [ ] **Step 4: Build and verify Qed or document remaining admit**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success.

- [ ] **Step 5: Commit**

```bash
git add posets/dimension/RemovablePairs.v
git commit -m "feat(RemovablePairs): removable_pair_dimension_bound statement + initial proof attempt"
```

---

## Task 4: Prove the antichain case of `removable_pair_exists` as a warm-up

The antichain is the canonical pathological case. Proving it directly first ensures the definition handles it.

**Files:**
- Modify: `posets/dimension/RemovablePairs.v`

- [ ] **Step 1: Add the antichain helper lemma**

Append:

```coq
  (** When R is the discrete poset (an antichain), every pair (x, y) with
      x ≠ y is removable. *)
  Lemma antichain_removable_pair :
    (forall a b, R a b -> a = b) ->  (* R is the equality relation *)
    forall x y : A, x <> y -> IsRemovablePair x y.
  Proof.
  Admitted.
```

- [ ] **Step 2: Build to verify statement**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success.

- [ ] **Step 3: Implement the proof**

Replace `Admitted.` with:

```coq
  Proof.
    intros Hdisc x y Hxy_neq.
    split; [exact Hxy_neq |].
    intros L' HL'_lin.
    (* Build L by extending L' with y < x and arbitrary positions for x, y wrt others.
       Since R is discrete, any total order on A that extends L' works.
       Use szpilrajn_theorem applied to TC(L' ∪ {(y, x)}). *)
    (* TODO: complete construction. *)
  Admitted.
```

**Note:** This warm-up may itself be substantial (2-4 hours). It's a litmus test: if we can't prove the antichain case, the definition is wrong.

- [ ] **Step 4: Build and verify**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success.

- [ ] **Step 5: Commit**

```bash
git add posets/dimension/RemovablePairs.v
git commit -m "feat(RemovablePairs): antichain_removable_pair warm-up lemma"
```

---

## Task 5: Prove `removable_pair_exists` (existence in general)

This is Trotter's hard direction.

**Files:**
- Modify: `posets/dimension/RemovablePairs.v`

- [ ] **Step 1: Add the lemma statement as Admitted**

Append:

```coq
  (** Trotter's removable-pair lemma: every finite poset with at least 4
      elements and at least one incomparable pair has a removable pair. *)
  Lemma removable_pair_exists :
    forall n,
    cardinal A (Full_set A) n ->
    n >= 4 ->
    (exists a b, Incomparable R a b) ->
    exists x y, IsRemovablePair x y.
  Proof.
  Admitted.
```

- [ ] **Step 2: Build**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success.

- [ ] **Step 3: Implement the proof**

Replace `Admitted.` with the actual proof. Sketch (Trotter Ch. 6):

1. Enumerate elements (via the cardinal): `A_list : list A`.
2. Identify a critical pair `(x, y)` via `incomparable_lifting_to_critical_pair`.
3. Iterate adjustments of the choice `(x, y)` over the elements such that critical pairs touching `(x, y)` minimize structural conflicts.
4. Verify the chosen pair satisfies `IsRemovablePair`.

This step is multi-day work. Subdivide as needed.

**Note:** This is the genuinely hard lemma. If after substantial effort no progress, document the precise sub-claim that's missing.

- [ ] **Step 4: Build**

Run: `opam exec -- dune build posets/dimension/RemovablePairs.vo`
Expected: success.

- [ ] **Step 5: Commit**

```bash
git add posets/dimension/RemovablePairs.v
git commit -m "feat(RemovablePairs): removable_pair_exists statement + initial proof"
```

---

## Task 6: Wire up `hiraguchi_helper` to use `RemovablePairs`

**Files:**
- Modify: `posets/dimension/Theorems.v` (around line 2406, the `hiraguchi_helper` lemma)

- [ ] **Step 1: Add the import to Theorems.v**

In the imports of `Theorems.v`, add:

```coq
From Dimension Require Import RemovablePairs.
```

- [ ] **Step 2: Rewrite `hiraguchi_helper`'s proof body**

Replace the current `Admitted.` of `hiraguchi_helper` (with its SOUNDNESS WARNING comment) with:

```coq
  intros n B R2 HR2 d2 Hcard Hn4 Hdim.
  (* Strong induction on n. *)
  generalize dependent d2. generalize dependent R2. generalize dependent B.
  induction n as [n IH] using lt_wf_ind.
  intros B R2 HR2 d2 Hcard Hn4 Hdim.
  destruct (classic (exists a b, Incomparable R2 a b)) as [Hinc_ex | Hchain].
  - (* Incomparable pair exists → use removable_pair_exists + IH on size n-2 *)
    destruct (@removable_pair_exists B R2 _ n Hcard Hn4 Hinc_ex) as [x [y Hrem]].
    (* Recursive call: dim(R2 restricted to Residual x y) ≤ ⌊(n-2)/2⌋ via IH. *)
    (* Then dim(R2) ≤ (n-2)/2 + 1 ≤ n/2 via removable_pair_dimension_bound + arithmetic. *)
    (* TODO: fill in the bookkeeping (extract subposet dim from IH, apply
       removable_pair_dimension_bound, conclude via Nat arithmetic). *)
    admit.
  - (* No incomparable pair → R2 is a chain, dim = 1 *)
    (* Same as before: build singleton realizer {R2}, use dimension_is_minimum. *)
    admit.
Qed.
```

**Note:** The two `admit.`s here are SCAFFOLDING — they should be filled with the actual proof. The structure is symmetric to the old proof body (which we kept in the commented-out section).

- [ ] **Step 3: Build to confirm scaffolding compiles**

Run: `mise build`
Expected: success with admits (Coq accepts `admit.` inside `Qed.` — wait, it doesn't. Change `Qed.` to `Admitted.` while admits remain.).

Actually: replace `Qed.` with `Admitted.` while admits are in place. Final replace happens after all admits resolved.

- [ ] **Step 4: Commit scaffolding**

```bash
git add posets/dimension/Theorems.v
git commit -m "feat(Theorems): wire hiraguchi_helper to RemovablePairs (scaffolding)"
```

---

## Task 7: Fill the two admits in `hiraguchi_helper`

**Files:**
- Modify: `posets/dimension/Theorems.v`

- [ ] **Step 1: Resolve the chain case admit**

Replace the second `admit.` (chain case) with the chain-case proof. Reuse the body that used to be commented out (it's known to work). Reference: the `Hchain` branch in the original proof body.

- [ ] **Step 2: Build to verify chain case compiles**

Run: `opam exec -- dune build posets/dimension/Theorems.vo`
Expected: success with one remaining admit.

- [ ] **Step 3: Resolve the incomparable-pair-case admit**

Replace the first `admit.` with the proof body that:
1. Extracts the IH-derived dim of the subposet.
2. Applies `removable_pair_dimension_bound`.
3. Concludes via Nat division arithmetic.

Code template:

```coq
    (* Subposet has size n - 2, dim ≤ ⌊(n-2)/2⌋ by IH. *)
    set (Sres := Residual x y).
    assert (Hcard_sub : cardinal {a : B | In B Sres a}
                           (Full_set {a : B | In B Sres a}) (pred (pred n))).
    { (* via cardinal_subtype_full + cardinal_subtract_sn. See similar pattern
         in commented-out body. *)
      admit. }
    pose proof (IH (pred (pred n)) ltac:(lia)
                   {a : B | In B Sres a}
                   (fun a b => R2 (proj1_sig a) (proj1_sig b))
                   (subtype_is_poset R2 Sres)) as IH_inst.
    (* IH_inst is the polymorphic IH at the subtype; produces d_sub ≤ pred(pred n) / 2. *)
    (* TODO: complete bookkeeping. *)
```

This step is substantial. Subdivide into smaller commits as you flesh out the bookkeeping.

- [ ] **Step 4: Build with all admits replaced**

Run: `mise build`
Expected: success, no admits.

- [ ] **Step 5: Change `Admitted.` to `Qed.`**

In `hiraguchi_helper`, the final keyword should be `Qed.` once all internal admits are resolved.

- [ ] **Step 6: Commit**

```bash
git add posets/dimension/Theorems.v
git commit -m "feat(Theorems): close hiraguchi_helper via removable-pair lemma"
```

---

## Task 8: Remove the false admits

**Files:**
- Modify: `posets/dimension/Theorems.v`

- [ ] **Step 1: Delete `extremal_critical_pair_exists`**

Remove lines containing the `extremal_critical_pair_exists` lemma + its surrounding SOUNDNESS WARNING comment. (Lines ~136–163 in current file; verify with grep.)

- [ ] **Step 2: Delete `exists_critical_pair_no_boundary`**

Remove lines containing `exists_critical_pair_no_boundary` + the SOUNDNESS WARNING block + the commented-out derivation. (Lines ~165–212.)

- [ ] **Step 3: Delete `small_subposet_one_realizer`**

Remove the false admit and its NOTE.

- [ ] **Step 4: Build**

Run: `mise build`
Expected: success. If `small_two_realizer_incomp` or `small_hiraguchi` still reference these, fix at this step.

- [ ] **Step 5: Resolve `small_two_realizer_incomp`**

This claim is TRUE (Hiraguchi for n ∈ {4,5}). With `hiraguchi_helper` now Qed, prove `small_two_realizer_incomp` as a CONSEQUENCE of `hiraguchi_helper`:

```coq
Proof.
  intros n Hcard Hn45 Hinc_ex.
  destruct (dushnik_miller_exists n Hcard) as [d [HdimR]].
  destruct (HdimR) as [_ Hrealizer_inst _ _].
  exists (dimension_realizer Hrealizer_inst).
  (* dim R ≤ n/2 = 2 for n ∈ {4,5} via hiraguchi_helper. *)
  (* Then build the 2-realizer from the d-realizer with d ≤ 2. *)
  (* TODO: complete. *)
Admitted.
```

This is a moderate proof; may take 1-2 hours.

- [ ] **Step 6: Resolve `small_hiraguchi`**

Trivial corollary of `hiraguchi_helper`:

```coq
Proof.
  intros n d Hcard Hn45 Hdim.
  apply (@hiraguchi_helper n A R _ d Hcard); [lia | exact Hdim].
Qed.
```

- [ ] **Step 7: Build**

Run: `mise build`
Expected: success, all top-level theorems Qed.

- [ ] **Step 8: Verify no admits remain**

Run: `grep -nE '^\s*Admitted\.|^\s*admit\.' posets/dimension/Theorems.v posets/dimension/RemovablePairs.v`
Expected: empty output.

- [ ] **Step 9: Commit**

```bash
git add posets/dimension/Theorems.v posets/dimension/RemovablePairs.v
git commit -m "feat: remove false admits; complete Hiraguchi via Trotter"
```

---

## Task 9: Sanity check on the n-antichain

The previous design's downfall. Verify the new proof works for this case.

**Files:**
- (No file changes; just a sanity check.)

- [ ] **Step 1: Add a test instance file (or REPL session)**

Optional: add `posets/dimension/test/AntichainHiraguchi.v` with:

```coq
From Dimension Require Import Theorems.
From Stdlib Require Import Ensembles Finite_sets.

(* Test: 4-element antichain has dim ≤ 2. *)
Section TestAntichain4.
  Variable a b c d : Set.
  Let A : Type := { x : nat | x = 0 \/ x = 1 \/ x = 2 \/ x = 3 }.
  (* Construct the discrete poset and verify hiraguchi_bound applies. *)
  (* TODO: complete the instantiation. *)
End TestAntichain4.
```

- [ ] **Step 2: Build the test (if added)**

Run: `mise build`
Expected: success.

- [ ] **Step 3: Commit (if test was added)**

```bash
git add posets/dimension/test/AntichainHiraguchi.v
git commit -m "test: verify Hiraguchi proof works for 4-element antichain"
```

---

## Task 10: Final verification

**Files:**
- (No changes; verification only.)

- [ ] **Step 1: Full build**

Run: `mise build`
Expected: green.

- [ ] **Step 2: All-proofs check**

Run: `mise run check-all`
Expected: green.

- [ ] **Step 3: Zero admits**

Run: `grep -rE '^\s*Admitted\.|^\s*admit\.' posets/dimension/`
Expected: empty.

- [ ] **Step 4: Build skill still accurate**

Run: `cat .claude/skills/coq-mise-build/SKILL.md | head -10`
Verify: description still matches project state.

- [ ] **Step 5: Final commit**

```bash
git add -A
git commit -m "feat: complete sound proof of Hiraguchi's theorem"
```

---

## Edge cases the plan must handle

**Base case n=4 is not handled by induction.** `removable_pair_dimension_bound` reduces dim(P) on n elements to dim of an (n-2)-element subposet. For n=4, the subposet has 2 elements; for n=5, 3 elements. But Hiraguchi's bound `dim ≤ ⌊n/2⌋` doesn't hold for n ≤ 3:
- 2-antichain has dim 2, but `⌊2/2⌋ = 1`.
- 3-antichain has dim 2, but `⌊3/2⌋ = 1`.

So the induction's base case for n=4 must be proved DIRECTLY (not by reducing to n=2). Add an explicit `hiraguchi_n4` lemma if the existing `small_hiraguchi` infrastructure isn't enough. The plan as written treats this implicitly via `small_hiraguchi`; if that becomes problematic, add an explicit Task between 7 and 8.

**Diamond poset (4-element lattice with one max, one min, two incomparable middle elements).** The naive "pick a max and a min that are incomparable" doesn't work here (the unique max and min are comparable). `removable_pair_exists` must succeed by picking the two middle elements (both are simultaneously max-in-their-level and min-in-their-level). Task 4's antichain warm-up doesn't exercise this; add a sanity check on the diamond in Task 9.

**Antichain (every element is both max and min).** The previous design's downfall. Verify in Task 9 that `removable_pair_exists` returns a working witness for an explicit 4-antichain instance.

## Notes on incremental safety

This plan is designed so the repository stays in a sound state after every commit. If you hit a wall on Task 5 (`removable_pair_exists`), the repo still has:
- `removable_pair_dimension_bound` (Qed or Admitted with sound statement)
- The skeleton in `RemovablePairs.v`
- The old false admits NOT YET removed (they're removed only in Task 8)

If you must stop mid-way, the build remains green and the proof of `hiraguchi_helper` stays Admitted (not falsely Qed). The earlier tasks (1-4) constitute the recoverable progress; Tasks 5-8 are the high-risk core.

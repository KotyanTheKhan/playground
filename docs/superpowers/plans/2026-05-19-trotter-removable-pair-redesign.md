# Trotter Removable Pair — Redesign Plan

> **For agentic workers:** Each step is a self-contained Coq proof obligation in `posets/dimension/RemovablePairs.v` or `posets/dimension/Theorems.v`. Build via `mise build`.

**Goal:** Close `non_antichain_removable_pair_exists` (Trotter's Removable Pair Lemma) by introducing boundary-aware lift infrastructure.

**Architecture:** Generalize `lift_and_force_is_poset` to accept a finite set `B` of boundary CP reversals. Build a per-L' selection function that assigns each linear extension of the residual a boundary set. Compose to construct a (d'+1)-realizer of R.

---

## Step 1: Define boundary reversal predicate

**File:** `posets/dimension/RemovablePairs.v`
**Where:** new section before `non_antichain_removable_pair_exists`

```coq
(** A "boundary reversal set" for a critical pair (x', y') is a finite
    list of pairs (p, q) with each (p, q) a critical pair of R having
    exactly one endpoint in {x', y'}, together with consistency: no two
    pairs in the set conflict with each other or with (x', y'). *)
Definition IsBoundaryReversalSet (x' y' : A) (B : list (A * A)) : Prop :=
  Forall (fun pq => IsCriticalPair R (fst pq) (snd pq) /\
                    (fst pq = x' \/ fst pq = y' \/
                     snd pq = x' \/ snd pq = y')) B.
```

Plus helper lemmas:
- `boundary_set_finite : forall x' y' B, IsBoundaryReversalSet x' y' B -> Finite _ (fun pq => List.In pq B)`

---

## Step 2: Generalize `lift_and_force_is_poset` to accept boundary set

**File:** `posets/dimension/Theorems.v` (new lemma, NOT replacing existing one)

```coq
Lemma lift_and_force_with_boundary_is_poset :
  forall (x' y' : A) (S' : Ensemble A) (B : list (A * A))
         (L' : {a : A | In A S' a} -> {a : A | In A S' a} -> Prop),
  IsCriticalPair R x' y' ->
  S' = Setminus A (Setminus A (Full_set A) (Singleton A x')) (Singleton A y') ->
  IsLinearExtension
    (fun a b : {a : A | In A S' a} => R (proj1_sig a) (proj1_sig b)) L' ->
  IsBoundaryReversalSet x' y' B ->
  (* Acyclicity precondition: TC of (R ∪ L'_lift ∪ {(x',y')} ∪ B_reversed) is asymmetric *)
  (forall a, ~ clos_trans A
    (fun a b => R a b
             \/ (exists ha hb, L' (exist _ a ha) (exist _ b hb))
             \/ (a = x' /\ b = y')
             \/ List.In (b, a) B  (* reversed boundary edges *)) a a) ->
  IsPoset A
    (clos_trans A
       (fun a b =>
          R a b
          \/ (exists ha hb, L' (exist _ a ha) (exist _ b hb))
          \/ (a = x' /\ b = y')
          \/ List.In (b, a) B)).
```

Strategy: directly derive antisymmetry from the asymmetry precondition; transitivity from `clos_trans`; reflexivity from `R`. The acyclicity precondition is the joint-consistency Trotter requires — it's discharged at the call site.

**Why this is tractable:** the original `lift_and_force_is_poset`'s 400-line proof established the path invariant exactly to show *no cycles exist*. By taking acyclicity as a precondition, we shift the work onto the caller. The poset structure (refl, trans, antisym) then follows mechanically.

---

## Step 3: Build `cp_lift_function_with_boundary`

**File:** `posets/dimension/Theorems.v`

```coq
Lemma cp_lift_function_with_boundary :
  forall (x' y' : A) (S' : Ensemble A) (B : list (A * A)),
  IsCriticalPair R x' y' ->
  S' = ... (residual) ... ->
  IsBoundaryReversalSet x' y' B ->
  (* per-L' acyclicity precondition *)
  (forall L', IsLinearExtension (...) L' ->
              forall a, ~ clos_trans A (... with B ...) a a) ->
  exists lift_b : (subtype rel) -> (A -> A -> Prop),
    forall L',
      IsLinearExtension (...) L' ->
      IsLinearExtension R (lift_b L') /\
      (lift_b L') x' y' /\
      (forall p q, List.In (p, q) B -> (lift_b L') q p) /\  (* reverses B *)
      (* L'-restriction equivalence on residual, same as cp_lift_function *)
      ...
```

Built via `szpilrajn_theorem` on the boundary-augmented TC, just like `cp_lift_function` is built on the (x',y')-augmented TC.

---

## Step 4: Per-L' boundary assignment

**File:** `posets/dimension/RemovablePairs.v`

```coq
Lemma boundary_assignment_exists :
  forall (x' y' : A) (L' : ...realizer of R|residual...),
  IsCriticalPair R x' y' ->
  IsLinearExtension (...) L' ->
  exists B : list (A * A),
    IsBoundaryReversalSet x' y' B /\
    (forall a, ~ clos_trans A (... with B ...) a a) /\
    (* B "covers" boundary CPs not reversed by L_extra alone *)
    (forall p q, IsCriticalPair R p q ->
                 (p = x' \/ p = y' \/ q = x' \/ q = y') ->
                 (p, q) <> (y', x') ->
                 List.In (p, q) B \/ (lift_b L') q p).
```

This is the key combinatorial step. **Strategy:** for each boundary CP `(p, q)` not equal to `(y', x')`, decide whether to include it in `B` based on whether `L'` already orients its residual endpoint "the right way." Trotter's argument shows this can always be done consistently.

**Fallback:** if the general consistency proof is too hard, weaken the claim to: there exists an `(x', y')` (not just any CP) for which boundary assignment exists. Use the CP digraph's extremal structure.

---

## Step 5: Compose into `non_antichain_removable_pair_exists`

**File:** `posets/dimension/RemovablePairs.v` (replace current Admitted)

```coq
Proof.
  intros n Hcard Hn4 Hstrict Hinc.
  destruct Hinc as [a [b Hinc]].
  destruct (critical_pair_exists_from_incomparable n Hcard a b Hinc) as [x' [y' Hcp]].
  exists x', y'. split.
  - (* x' <> y': from Hcp incomparability + reflexivity *)
    ...
  - intros d' r' Hr'_real Hr'_card.
    (* For each L' ∈ r', get a boundary assignment B(L') *)
    (* Build the lifted r_lifted using cp_lift_function_with_boundary *)
    (* L_extra: szpilrajn(R ∪ {(y', x')}) *)
    (* Use cp_realizer_separation to conclude *)
    ...
Qed.
```

---

## Risk areas

**Risk A — Step 2 acyclicity precondition discharge:** Steps 4 produces a boundary assignment but proving its acyclicity (no cycles in TC of `R ∪ L' ∪ {(x',y')} ∪ B_reversed`) is the hard combinatorial step. Trotter's argument uses the structure of the critical-pair digraph + an extremal pair.

**Mitigation:** Start by proving Step 2 with the precondition as hypothesis (no combinatorics yet). If the precondition cannot be discharged in Step 4, we have at least *factored* the gap into a precise consistency claim.

**Risk B — Step 4 may itself need to be axiomatized:** if even the per-L' boundary assignment is too deep, accept Step 4 as a focused Admitted helper. The previous bare admit (the entire Trotter lemma) becomes a *named*, *specific* combinatorial claim with a clean interface.

---

## Execution order

1. **Step 1** (definitions) — ~30 lines, trivial. Single agent.
2. **Step 2** (generalized poset lemma) — ~150 lines, moderate. Single agent.
3. **Step 3** (lift function with boundary) — ~80 lines, moderate. Single agent.
4. **Step 4** (boundary assignment existence) — DEEP. Try, fall back to focused Admitted.
5. **Step 5** (compose) — ~50 lines if Step 4 closes; otherwise wraps Admitted Step 4.

Even if Step 4 remains Admitted, the gap is now a *clean, specific consistency claim* rather than the entire Trotter lemma. Mathematically equivalent surface area but vastly more auditable.

---

## Build discipline

- All steps must keep `mise build` green.
- No false axioms.
- Each commit message includes step number and the lemma names added/changed.

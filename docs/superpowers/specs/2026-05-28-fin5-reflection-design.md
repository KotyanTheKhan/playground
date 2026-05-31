# Design: Fin.t 5 Boolean Reflection for n=5 Exhaustiveness

**Date:** 2026-05-28
**Branch:** `dimension_finish`
**Motivation:** Close `EdgeCount4.v:221` exhaustiveness admit; reduce 5^N cartesian-destruct compile blowup across `EdgeCount*` files.

---

## Problem

The `EdgeCount4` cascade ends with an `Admitted` claim:

> If 5 elements `a..e` cover the carrier, are pairwise distinct, and `edge_count_5 R2 = 4`, then SOME of the 10 iso-class patterns (classes 11-20) must match.

The 10 negations `Hn11..Hn20` together with `Hec = 4` should force `False`. Naive proof: enumerate the 210 ways to pick 4-of-10 unordered pairs as comparable, orient each, check transitivity, and identify the iso class — ~3000 cases.

Same shape will hit again at `EdgeCount5` (15 classes), `EdgeCount6..9` (similar). And each per-class helper already pays a 5^7 = 78,125 cartesian-destruct cost (e.g. `EdgeCount4_4claw_up:69-81`) just to dispatch strict edges over the carrier covering.

## Approach: reflect to `Fin.t 5`

Replace the abstract `B`-poset reasoning at this leaf level with a decidable boolean reflection over `Fin.t 5`, then transport.

### Layer 1: `N5Reflect.v` — purely computational, no `B`

```coq
Definition M5 := Fin.t 5 -> Fin.t 5 -> bool.

Definition is_poset_b (M : M5) : bool := ...    (* refl ∧ antisym ∧ trans *)
Definition strict_b (M : M5) (i j : Fin.t 5) : bool := M i j && negb (Fin.eqb i j).
Definition edge_count_b (M : M5) : nat := ...   (* sum over 20 ordered pairs *)

Definition is_4claw_up_b   (M : M5) : bool := ... (* 10 such *)
Definition is_4claw_down_b (M : M5) : bool := ...
...
Definition is_K32mm_b      (M : M5) : bool := ...

Lemma exhaustive_4edge :
  forall M : M5,
    is_poset_b M = true ->
    edge_count_b M = 4 ->
    is_4claw_up_b M = true \/ is_4claw_down_b M = true \/
    ... \/ is_K32mm_b M = true.
Proof.
  (* By `vm_compute` over the finite space of M5 satisfying is_poset_b ∧ edge_count_b = 4. *)
  ...
Qed.
```

Why this is cheap to prove: `M5` has 2^25 inhabitants, but `is_poset_b M = true` filters down to ~63 (OEIS A000112(5)). `vm_compute` enumerates and verifies in seconds.

If full enumeration of 2^25 matrices via `forallb` is too heavy for the kernel, alternative: enumerate **edge sets** rather than matrices.

```coq
Definition edge := (Fin.t 5 * Fin.t 5)%type.
Definition all_pairs : list edge := ...  (* 25 ordered pairs *)
Definition from_edge_list (es : list edge) : M5 := ...
(* Enumerate sublists; restrict to those forming a poset with 4 strict pairs. *)
```

### Layer 2: `N5Transport.v` — bridges abstract `B` ↔ `Fin.t 5`

```coq
Section Transport.
  Context {B : Type} (R2 : B -> B -> Prop) `{IsPoset B R2}.
  Variables a b c d e : B.

  (* Hypotheses: pairwise distinct + Hcov : forall x, x = a \/ ... \/ x = e + Hcard *)

  Definition to_fin (x : B) : Fin.t 5 := ...  (* via Hcov + classical choice *)
  Definition from_fin (i : Fin.t 5) : B := ...
  Definition R2_matrix : M5 := fun i j =>
    excluded_middle_informative (R2 (from_fin i) (from_fin j)).

  Lemma R2_matrix_is_poset : is_poset_b R2_matrix = true.
  Lemma R2_matrix_edge_count_eq : edge_count_b R2_matrix = edge_count_5 R2 a b c d e.

  (* For each pattern, prove the boolean and the abstract existential agree. *)
  Lemma is_4claw_up_b_iff :
    is_4claw_up_b R2_matrix = true <->
    (exists r l1 l2 l3 l4 : B, ... R2 r l1 ... R2 r l4).
  ...
End Transport.
```

### Layer 3: closing the admit

In `EdgeCount4.v`, replace `admit.` with:

```coq
(* All Hn11..Hn20 in scope. *)
pose proof (R2_matrix_is_poset ...) as Hp.
pose proof (R2_matrix_edge_count_eq ...) as Hec_b.
rewrite Hec in Hec_b.   (* Hec_b : edge_count_b _ = 4 *)
destruct (exhaustive_4edge _ Hp Hec_b) as
  [H11 | [H12 | ... | H20]];
  [ apply is_4claw_up_b_iff in H11; contradict Hn11
  | apply is_4claw_down_b_iff in H12; contradict Hn12
  | ...
  | apply is_K32mm_b_iff in H20; contradict Hn20 ].
```

## Per-class helpers (`EdgeCount4_*.v`) — separate concern

The 5^7 `destruct (Hcov ...)` cartesian inside `four_claw_up_closure` is independent of the reflection refactor. Same fix template applies though: instead of destructing every variable over `Hcov`, **carry strict_indicator accounting** and derive case-by-case.

Concrete refactor for one helper (`EdgeCount4_4claw_up.v`):
- Replace cartesian destruct on `Hcov r/l1/l2/l3/l4/x/y` with sequential destructs:
  ```
  destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]]; subst x;
    destruct (Hcov y) as [Hy | [Hy | [Hy | [Hy | Hy]]]]; subst y;
      try (exfalso; congruence);
      try (case_to_known_edge).
  ```
- Even better: prove a generic `Lemma edges_from_4_known : 4 known edges + edge_count=4 → ∀ x y, R2 x y ∧ x≠y → (x,y) is one of the 4 known`. Use it from each helper.

This is **task #10** (compile-time refactor) — independent of the admit closure.

## Plan

### Session R1 — reflection core (this session)
- Create `posets/dimension/N5Exhaustive/N5Reflect.v`:
  - `M5`, `is_poset_b`, `strict_b`, `edge_count_b`.
  - 10 pattern booleans `is_<pattern>_b`.
  - `Lemma exhaustive_4edge` (proof via `vm_compute` or structured enumeration).
- Target: <500 lines, <2 min Qed.

### Session R2 — transport layer
- Create `posets/dimension/N5Exhaustive/N5Transport.v`:
  - Bijection `to_fin`/`from_fin` from Hcov.
  - `R2_matrix_is_poset`, `R2_matrix_edge_count_eq`.
  - 10 `is_<pattern>_b_iff` lemmas.

### Session R3 — wire into EdgeCount4
- Replace `admit.` in `EdgeCount4.v:220` with transport invocation.
- Verify full build green.
- Commit: drop admit count 3 → 2.

### Session R4 (optional) — extend to EdgeCount5/6_9
- Same reflection extends to k=5..9 (each class set just grows).
- Closes a second admit (`n5_residual_classes_two_realizer`) downstream.

### Session R5 (optional, parallel) — per-helper compile-time refactor
- Replace 5^7 cartesian destruct in each `EdgeCount*_*.v` helper with sequential or `edges_from_k_known` lemma.
- Target: <60s per helper.

## Risks

- **vm_compute exhaustion**: if `forall M : M5, ...` enumerates 2^25 matrices, kernel may OOM or take minutes. Fallback: enumerate edge subsets up to size 4 via list.
- **Bijection complexity**: building `to_fin` from Hcov requires `excluded_middle_informative` 5 times. Likely OK with Opaque marking.
- **Pattern boolean correctness**: each `is_<pattern>_b` must match the abstract `exists` shape exactly. Easy to get wrong; cover with `is_<pattern>_b_iff` Qed.

## Open questions

1. Should `is_poset_b` enforce transitive closure (`forall i j k, M i j → M j k → M i k`) or take it as proven separately? Probably enforce.
2. Should patterns share a common combinator (`has_4_edges_of_shape : list (Fin.t 5 * Fin.t 5) -> M5 -> bool`)? Likely yes — cuts duplication.

---

## Useful paths

- Target admit: `posets/dimension/N5Exhaustive/EdgeCount4.v:220`
- Related admit (will be closed by R4): `posets/dimension/N5DispatcherShapes.v:38`
- Status doc: `docs/superpowers/specs/2026-05-28-status.md`
- This plan: `docs/superpowers/specs/2026-05-28-fin5-reflection-design.md`

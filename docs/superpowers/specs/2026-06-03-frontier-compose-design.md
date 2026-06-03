# Frontier composition of executions — Slice A: antichain dichotomy — Design

**Date:** 2026-06-03
**Branch:** `frontier-compose`
**Arc:** Connect two dim-2 executions by a frontier; characterize when dimension
is preserved.
- **Slice A (this spec):** the cleanest case — two **antichains** joined by a
  frontier `F` give a *bipartite poset*. Prove the **dichotomy**: a non-crossing
  (**Ferrers**) `F` preserves `dim ≤ 2`; the **S₃ / crown** frontier (3+3,
  `i≠j`) forces `dim = 3`.
- **Slice B (later):** general dim-2 `P,Q` + a realizer-aligned non-crossing `F`
  (sufficient condition, realizer-staircase construction).

**Goal of Slice A:** the composition operator on antichains, a sufficient
preservation theorem (`Ferrers F ⟹ dim ≤ 2`), and a concrete counterexample
(`dim(crown₃) = 3`) — showing connection-by-frontier does NOT always preserve
dimension, and pinning the boundary at "crossing."
**Depends on:** `Posets.PosetClasses` (`IsPoset`); `Dimension.DimDefs`
(`PosetDimension`, `IsRealizer`, `IsLinearExtension`, `dimension_is_minimum`);
`Dimension.CriticalPairs` (`IsAlternatingCycle`,
`critical_pairs_reversible_iff_no_alternating_cycle`) — *candidate* route for the
bounds; `ZornsLemma`/Stdlib `Finite_sets` for finiteness; Stdlib `Arith`/`Lia`.

## Honest difficulty + risk

This Slice is **harder than the clock slices** (which reused `stamp_iff`). Two
real proofs:
1. **`Ferrers F ⟹ dim ≤ 2`** (positive) — a 2-realizer construction (the
   incomparability graph of a Ferrers bipartite poset is a comparability graph).
2. **`dim(crown₃) ≥ 3`** (negative lower bound) — the genuine research bit; the
   repo has the alternating-cycle theorem but **no existing dimension result on
   the crown**, and its `no_alt_cycle` bridge carries a documented caveat (review
   finding 4: the `dim≤2 ⟸ no_alt_cycle` direction is recorded, the converse is
   *not* established there).

**Mitigation / plan structure:** implement **positive-first** so the preservation
result always lands. The exact proof route for each direction (explicit 2-realizer
vs the critical-pairs/alternating-cycle machinery) is chosen at implementation
after a short feasibility spike on the `dim≤2 ⟺ no-alt-cycle` bridge. **No silent
admits** — if the `dim ≥ 3` lower bound proves intractable in this slice, escalate
(the positive result + the crown's *upper* bound `dim ≤ 3` + the explicit
alternating cycle as a documented obstruction still constitute a meaningful
deliverable).

## Component 1 — the composition operator (`execution/FrontierCompose.v`)

```coq
Inductive Carrier (A B : Type) : Type := inA (a : A) | inB (b : B).
Arguments inA {A B}. Arguments inB {A B}.

(* compose two antichains A, B by a one-way frontier F : A -> B -> Prop *)
Definition compose_le {A B} (F : A -> B -> Prop) (x y : Carrier A B) : Prop :=
  match x, y with
  | inA a, inA a' => a = a'      (* A is an antichain *)
  | inB b, inB b' => b = b'      (* B is an antichain *)
  | inA a, inB b  => F a b       (* frontier edges (one-way) *)
  | inB _, inA _  => False
  end.

#[export] Instance compose_IsPoset {A B} (F : A -> B -> Prop) :
  IsPoset (Carrier A B) (compose_le F).
```
`compose_IsPoset` holds for **any** `F` (no Ferrers needed): refl by `eq`/`F`-diag
is not required (refl is same-element, `a=a`/`b=b`); antisym — cross both-ways is
`False`, same-side is `eq`-antisym; trans — one-way edges cannot form a cycle, and
A→A→B / A→B→B compose through `eq`. (Mirrors `rhb_IsPoset`'s structure.)

Finiteness: `A`, `B` are finite (e.g. `Fin m`, `Fin n` or a `Finite (Full_set _)`
hypothesis); `Carrier A B` is then finite — needed for `PosetDimension`.

## Component 2 — non-crossing condition + positive theorem (`FrontierCompose.v`)

```coq
(* no crossing 2x2 : rows of F are nested *)
Definition Ferrers {A B} (F : A -> B -> Prop) : Prop :=
  forall a1 a2 b1 b2, F a1 b1 -> F a2 b2 -> F a1 b2 \/ F a2 b1.

Theorem ferrers_dim_le2 :
  forall {A B} (F : A -> B -> Prop),
    Finite (Full_set A) -> Finite (Full_set B) ->
    Ferrers F ->
    forall d, PosetDimension (compose_le F) d -> d <= 2.
```

Proof route (chosen at implementation; both reduce to library APIs):
- **(R1) Explicit 2-realizer.** `Ferrers` ⟹ the rows `{b : F a b}` are linearly
  ordered by ⊆ ⟹ a "staircase." Build `M1`, `M2`: two linear extensions agreeing
  on the cross-edges (`inA a < inB b ⟺ F a b`) and *reversing* the within-A and
  within-B antichains, so `M1 ∩ M2 = compose_le F`; `dimension_is_minimum`. The
  within-side reversal keeps A,B antichains; Ferrers makes the cross-edges
  transitively consistent with one shared within-side order.
- **(R2) No alternating cycle.** Show a `Ferrers F` admits **no** alternating
  cycle among the critical pairs of `compose_le F`, then apply the
  `no_alt_cycle ⟹ dim ≤ 2` lever (the proven direction). Reuses
  `critical_pairs_reversible_iff_no_alternating_cycle`; lighter if the bridge fits.

Helper (connect "non-crossing" to a threshold form, the easy half):
```coq
(* a threshold frontier is Ferrers (the converse, Ferrers => threshold on finite A,B,
   is classical but heavier; not required for ferrers_dim_le2). *)
Lemma threshold_Ferrers :
  forall {A B} (phi : A -> nat) (psi : B -> nat) (F : A -> B -> Prop),
    (forall a b, F a b <-> phi a <= psi b) -> Ferrers F.
```

## Component 3 — the crown counterexample (`FrontierCompose.v`)

```coq
(* crown_3 : A = B = Fin 3 ; F i j := i <> j  (= StandardExampleRel 3 1) *)
Definition crownF (a b : Fin.t 3) : Prop := a <> b.
Definition crown3 := compose_le crownF.

Theorem crown3_dim_eq_3 : forall d, PosetDimension crown3 d -> d = 3.
```
- **Upper bound `dim ≤ 3`:** an explicit 3-realizer (three linear extensions whose
  intersection is `crown3`), via `dimension_is_minimum`'s companion / a direct
  realizer cardinality-3 witness.
- **Lower bound `dim ≥ 3`:** the three critical pairs `(inA i, inB i)` (`i=0,1,2`,
  each `inA i ∥ inB i` since `¬ crownF i i`) form an **alternating cycle**; by
  (the `dim ≤ 2 ⟹ no alternating cycle` direction of) the critical-pairs theorem,
  no 2-realizer exists, so `d ≥ 3`. *(The risky proof — see risk section; the
  alternating cycle itself is exhibited concretely regardless.)*

Together: `dim crown3 = 3` — connecting two 3-event antichains by the `i≠j`
frontier raises dimension from 2 to 3.

## Component 4 — examples (`execution/FrontierComposeExamples.v`, test-only)

- A concrete **Ferrers** frontier on `Fin 2`/`Fin 2` (e.g. `F i j := i <= j`,
  a staircase) with `Ferrers F` proven (via `threshold_Ferrers` or directly) and
  `dim ≤ 2` via `ferrers_dim_le2`.
- The **crown** instance: `¬ Ferrers crownF` (witnessed by `crownF 0 1`, `crownF 1 0`,
  `¬crownF 0 0`, `¬crownF 1 1` — so the sufficient condition does not apply), and the
  real payoff `dim crown3 = 3` via `crown3_dim_eq_3`. (Note: `¬Ferrers` alone is *not*
  what forces dim 3 — a lone 2×2 crossing is S₂, still dim 2 — the 3×3 crown structure
  is; `crown3_dim_eq_3` is the load-bearing claim.)
- The contrast (`Ferrers ⟹ dim 2` vs `crown ⟹ dim 3`) IS the dichotomy.

## Files, wiring, testing

- New: `execution/FrontierCompose.v` (exported), `execution/FrontierComposeExamples.v`
  (test). *(Pure poset-dimension theory reusing `Dimension`; lives in `execution/`
  for narrative cohesion with the frontier/clock arc — it does not use `ExecPoset`.)*
- `execution/dune` + `_CoqProject`: add both (after the RoundSem entries); ensure
  `Dimension`/`CriticalPairs` are in the `(theories …)` (they already are).
- `execution/Execution.v`: add `FrontierCompose` to the `Require Export`.
- `docs/INDEX.md`: a subsection (new "Frontier composition" group);
  `execution/DIM2_CLOCK.md`: a note that connecting executions by a frontier
  preserves dim-2 iff non-crossing (Ferrers), with the crown as the canonical
  counterexample.
- All builds via the wrapper; **zero `Admitted`** (or escalate); files < 500 lines;
  watch `Qed` time on the realizer/lower-bound proofs.
- `Print Assumptions ferrers_dim_le2 crown3_dim_eq_3` recorded.

## Acceptance criteria

1. `Carrier`/`compose_le`/`compose_IsPoset`; `Ferrers`; `threshold_Ferrers`.
   Zero admits.
2. `ferrers_dim_le2` (non-crossing frontier preserves `dim ≤ 2`). Zero admits.
3. `crown3_dim_eq_3` (the S₃ frontier gives `dim = 3`) — OR, if the lower bound is
   escalated, `dim ≤ 3` + the explicit alternating cycle as a documented
   obstruction, with the gap flagged (NOT admitted).
4. Examples (a Ferrers frontier dim ≤ 2; the crown dim = 3). Whole-project green;
   `INDEX.md` + `DIM2_CLOCK.md` updated.

## Out of scope / honestly noted

- **Slice A is antichains only.** General dim-2 `P,Q` is Slice B.
- **Sufficient, not iff.** `Ferrers F ⟹ dim ≤ 2` is one-directional; the exact
  characterization is `dim ≤ 2 ⟺ Ferrers-dimension(F) ≤ 2` (F = intersection of two
  Ferrers relations), which is heavier and NOT attempted here. A single 2×2
  crossing (S₂) is still dim 2 — only the 3×3 crown breaks it.
- **No bridge to `Schedule`/`blo`.** This is abstract bipartite-poset dimension;
  the "executions" are antichains (all-concurrent rounds). Connecting richer real
  executions is conceptually Slice B / future.
- The `dim ≥ 3` lower bound is the load-bearing risk; see the risk section.

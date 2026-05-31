# Phase R (Reflection) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close admit #3 (`EdgeCount4.v:221` exhaustiveness) and admit #1 (`N5DispatcherShapes.v:38`) via `Fin.t 5` boolean reflection on 5-element posets.

**Architecture:** Build a parallel `M5 = Fin.t 5 → Fin.t 5 → bool` representation, prove exhaustiveness by `vm_compute` enumeration, transport back to the abstract `B`-poset via a `to_fin`/`from_fin` bijection derived from the dispatcher's 5-element covering hypothesis.

**Tech Stack:** Coq 9.1.0 + Stdlib (`Fin.t`, `vm_compute`, classical `excluded_middle_informative`), no MathComp. Build via `mise exec -- dune build -j 2 <file>.vo`.

**Spec:** `docs/superpowers/specs/2026-05-28-dimension-replan-design.md` (Phase R) + `docs/superpowers/specs/2026-05-28-fin5-reflection-design.md` (technical detail).

---

## File structure

| File | Role | Owner |
|---|---|---|
| `posets/dimension/N5Exhaustive/N5Reflect_probe.v` | R0 throwaway probe, never committed | session R0 |
| `posets/dimension/N5Exhaustive/N5Reflect.v` | `M5`, `is_poset_b`, `edge_count_b`, 10 pattern booleans, `exhaustive_4edge` Qed | R1 |
| `posets/dimension/N5Exhaustive/N5Transport.v` | bijection + `R2_matrix` + 10 `iff` lemmas | R2 |
| `posets/dimension/N5Exhaustive/EdgeCount4.v` (modified) | replace `Admitted.` at line 221 | R3 |
| `posets/dimension/N5DispatcherShapes.v` (modified) | replace `Admitted.` at line 38 | R3 — only if scope permits; otherwise re-plan with R4 follow-on |

**Status doc to maintain:** `docs/superpowers/specs/2026-05-28-dimension-replan-status.md` — updated at every session boundary with commit hash + admit delta.

---

## Session R0: vm_compute feasibility probe (30 min, no commit)

**Files:**
- Create: `posets/dimension/N5Exhaustive/N5Reflect_probe.v` (throwaway; delete at session end)

**Purpose:** Decide GO / FALLBACK / ABORT before spending R1 effort.

- [ ] **Step 1: Create the probe file**

File: `posets/dimension/N5Exhaustive/N5Reflect_probe.v`

```coq
(** Probe: measure vm_compute cost over Fin.t 5 matrices.
    Throwaway — delete after measurement.  Decision rule in
    docs/superpowers/plans/2026-05-28-phase-R-reflection.md. *)
From Stdlib Require Import Fin Bool List Arith Lia.
Import ListNotations.

Definition M5 := Fin.t 5 -> Fin.t 5 -> bool.

Definition fin5_eqb (i j : Fin.t 5) : bool :=
  match Fin.eq_dec i j with left _ => true | right _ => false end.

Definition is_refl (M : M5) : bool :=
  forallb (fun i => M i i)
    [Fin.F1; Fin.FS Fin.F1; Fin.FS (Fin.FS Fin.F1);
     Fin.FS (Fin.FS (Fin.FS Fin.F1));
     Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))].

(* Probe 1: a single vm_compute. *)
Time Eval vm_compute in is_refl (fun _ _ => true).

(* Probe 2: small structured enumeration. *)
Definition all5 : list (Fin.t 5) :=
  [Fin.F1; Fin.FS Fin.F1; Fin.FS (Fin.FS Fin.F1);
   Fin.FS (Fin.FS (Fin.FS Fin.F1));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))].

Definition all_pairs : list (Fin.t 5 * Fin.t 5) :=
  flat_map (fun i => map (fun j => (i, j)) all5) all5.

(* Probe 3: sublists of fixed size. *)
Fixpoint sublists {A} (n : nat) (l : list A) : list (list A) :=
  match n with
  | 0 => [[]]
  | S k =>
      match l with
      | [] => []
      | x :: xs => map (cons x) (sublists k xs) ++ sublists (S k) xs
      end
  end.

Time Eval vm_compute in length (sublists 4 all_pairs).
(* Expected: C(25, 4) = 12650.  If this prints in < 5s, FALLBACK
   enumeration is viable. *)

(* Probe 4: build a matrix from an edge list and check is_refl. *)
Definition from_edges (es : list (Fin.t 5 * Fin.t 5)) : M5 :=
  fun i j =>
    existsb (fun p => fin5_eqb (fst p) i && fin5_eqb (snd p) j) es ||
    fin5_eqb i j.

Time Eval vm_compute in
  length (filter (fun es => is_refl (from_edges es)) (sublists 4 all_pairs)).
(* Expected: 12650 if all reflexive matrices satisfy is_refl (they do
   by construction).  Use this as the wall-clock budget benchmark. *)
```

- [ ] **Step 2: Build the probe**

```bash
mise exec -- dune build -j 2 posets/dimension/N5Exhaustive/N5Reflect_probe.vo
```

Expected: builds in < 30s. The `Time Eval` lines print timing to stderr/stdout.

- [ ] **Step 3: Record results in the status doc**

Append a section to `docs/superpowers/specs/2026-05-28-dimension-replan-status.md`:

```markdown
## R0 probe results (YYYY-MM-DD)

- Probe 1 (single vm_compute): <Xs>
- Probe 3 (sublist length): <Xs>
- Probe 4 (filter+from_edges over 12650): <Xs>

Decision: GO / FALLBACK / ABORT
- GO if Probe 4 < 60s in kernel.
- FALLBACK if Probe 4 60s–10min — use edge-subset enumeration in R1.
- ABORT if Probe 4 > 10 min — revert to cascade plan (Sessions N6–N9 of old plan).
```

- [ ] **Step 4: Delete the probe and commit status doc only**

```bash
rm posets/dimension/N5Exhaustive/N5Reflect_probe.v
mise exec -- dune build -j 2 posets/dimension/N5Exhaustive
git add docs/superpowers/specs/2026-05-28-dimension-replan-status.md
git commit -m "docs: R0 probe results — <GO|FALLBACK|ABORT> decision"
```

---

## Session R1: `N5Reflect.v` — defs + `exhaustive_4edge` (3-4 hr)

**Files:**
- Create: `posets/dimension/N5Exhaustive/N5Reflect.v`

Target: < 500 lines, Qed < 2 min, build with `-j 2`.

**Constraint (memory safety):** No `try (... eauto ...)` chains inside cartesian destructs. See `feedback_coq_oom_eauto_cascade.md` in auto-memory.

- [ ] **Step 1: Stub the file with imports and `M5`**

File: `posets/dimension/N5Exhaustive/N5Reflect.v`

```coq
(** Fin.t 5 boolean reflection layer for n=5 exhaustiveness.

    Defines a parallel matrix representation [M5 = Fin.t 5 -> Fin.t 5
    -> bool] for posets on 5 labelled elements.  Verifies that EVERY
    [M5] satisfying [is_poset_b] and [edge_count_b = 4] matches one
    of the 10 iso classes (11..20) by [vm_compute].

    Transport back to the abstract [B]-poset cascade lives in
    [N5Transport.v]. *)
From Stdlib Require Import Fin Bool List Arith Lia.
Import ListNotations.

Definition M5 := Fin.t 5 -> Fin.t 5 -> bool.

Definition fin5_eqb (i j : Fin.t 5) : bool :=
  match Fin.eq_dec i j with left _ => true | right _ => false end.

Definition all5 : list (Fin.t 5) :=
  [Fin.F1;
   Fin.FS Fin.F1;
   Fin.FS (Fin.FS Fin.F1);
   Fin.FS (Fin.FS (Fin.FS Fin.F1));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))].

Definition all_pairs : list (Fin.t 5 * Fin.t 5) :=
  flat_map (fun i => map (fun j => (i, j)) all5) all5.
```

- [ ] **Step 2: Build** — `mise exec -- dune build -j 2 posets/dimension/N5Exhaustive/N5Reflect.vo`

Expected: builds in < 5s.

- [ ] **Step 3: Add `is_poset_b`**

Append:

```coq
Definition is_refl (M : M5) : bool :=
  forallb (fun i => M i i) all5.

Definition is_antisym (M : M5) : bool :=
  forallb (fun p =>
    let (i, j) := p in
    negb (M i j && M j i) || fin5_eqb i j) all_pairs.

Definition is_trans (M : M5) : bool :=
  forallb (fun i =>
    forallb (fun j =>
      forallb (fun k =>
        negb (M i j && M j k) || M i k) all5) all5) all5.

Definition is_poset_b (M : M5) : bool :=
  is_refl M && is_antisym M && is_trans M.
```

Build. Expected pass.

- [ ] **Step 4: Add `strict_b` and `edge_count_b`**

```coq
Definition strict_b (M : M5) (i j : Fin.t 5) : bool :=
  M i j && negb (fin5_eqb i j).

Definition edge_count_b (M : M5) : nat :=
  fold_left (fun acc p =>
    acc + (if strict_b M (fst p) (snd p) then 1 else 0)) all_pairs 0.
```

Build.

- [ ] **Step 5: Decide enumeration strategy from R0 result**

If R0 = GO: enumerate over all `M5` matrices via `forallb` over `sublists 25 all_pairs` (the powerset of 25 pairs ≈ 33M, likely too big — practical bound).

If R0 = FALLBACK: enumerate `sublists 4 all_pairs` (12650 candidates). Each candidate is a list of 4 strict edges; build the reflexive closure via `from_edges`, restrict to those forming a poset (via `is_poset_b`), and verify each falls into one pattern.

**Use the FALLBACK formulation regardless** — it is strictly cheaper and the same correctness. The GO designation just means R1 won't time out either way.

```coq
Fixpoint sublists {A} (n : nat) (l : list A) : list (list A) :=
  match n with
  | 0 => [[]]
  | S k =>
      match l with
      | [] => []
      | x :: xs => map (cons x) (sublists k xs) ++ sublists (S k) xs
      end
  end.

Definition from_edges (es : list (Fin.t 5 * Fin.t 5)) : M5 :=
  fun i j =>
    existsb (fun p => fin5_eqb (fst p) i && fin5_eqb (snd p) j) es ||
    fin5_eqb i j.
```

Build.

- [ ] **Step 6: Add the 10 pattern booleans for k=4**

Each pattern boolean asks "does this matrix contain the structural shape of pattern X for some labelling?" To keep the booleans uniform, factor a generic combinator:

```coq
(** [has_shape relevant_edges M] holds iff there exists an injection
    of the shape's distinguished points into Fin.t 5 such that the
    listed edges hold in [strict_b M]. *)
Definition has_4_edges_of_shape
  (shape : list (Fin.t 5) -> list (Fin.t 5 * Fin.t 5))
  (arity : nat) (M : M5) : bool :=
  existsb (fun assignment =>
    let edges := shape assignment in
    forallb (fun e => strict_b M (fst e) (snd e)) edges)
    (permutations all5).  (* OR injective assignments of arity *)
```

(NOTE: `permutations` not in Stdlib — define it or use enumeration of injective vectors. Use whichever is simplest; if `permutations` is a 30-line helper, add it. Keep `arity ≤ 5`.)

Then each pattern is one line:

```coq
Definition is_4claw_up_b (M : M5) : bool :=
  has_4_edges_of_shape
    (fun π => match π with
              | r :: l1 :: l2 :: l3 :: l4 :: _ =>
                  [(l1, r); (l2, r); (l3, r); (l4, r)]
              | _ => [] end) 5 M.

Definition is_4claw_down_b (M : M5) : bool := ... (* (r, li) edges *)
Definition is_bowtie_b (M : M5) : bool := ...
Definition is_disjoint_b (M : M5) : bool := ...
Definition is_chain3_below_b (M : M5) : bool := ...
Definition is_chain3_above_b (M : M5) : bool := ...
Definition is_M_shape_b (M : M5) : bool := ...
Definition is_K32mm_b (M : M5) : bool := ...
Definition is_3claw_up_xp_b (M : M5) : bool := ...
Definition is_3claw_down_xl_b (M : M5) : bool := ...
```

(Edge lists come from the abstract definitions in `EdgeCount4_*.v` — open each file, copy the `R2 _ _` hypothesis list, translate to Fin.t 5 indices.)

Build after each pair of patterns. Cap file at this point if it's already > 400 lines — split pattern definitions into a separate file `N5Reflect_Patterns.v`.

- [ ] **Step 7: Prove `exhaustive_4edge`**

```coq
Lemma exhaustive_4edge :
  forall M : M5,
    is_poset_b M = true ->
    edge_count_b M = 4 ->
    is_4claw_up_b M = true \/
    is_4claw_down_b M = true \/
    is_bowtie_b M = true \/
    is_disjoint_b M = true \/
    is_chain3_below_b M = true \/
    is_chain3_above_b M = true \/
    is_M_shape_b M = true \/
    is_K32mm_b M = true \/
    is_3claw_up_xp_b M = true \/
    is_3claw_down_xl_b M = true.
Proof.
  intros M Hp Hec.
  (* Reduce M to its strict edge set, of size 4. *)
  (* Reflection: a 5-element poset is determined by its strict edge
     set (Hasse cover ⊆ strict closure).  So the proof reduces to
     forallb over sublists 4 all_pairs of those that build a poset
     of edge count exactly 4. *)
  (* The strategy: prove
       Lemma exhaustive_4edge_decide :
         forallb (fun M' =>
                    implb (is_poset_b M' && Nat.eqb (edge_count_b M') 4)
                          (<10-way-or of pattern booleans>) M')
                 enumerate_M5 = true.
     by vm_compute, then specialize.
   *)
  ...
Qed.
```

If the direct `vm_compute` path proves to be intractable mid-session:
- Split: introduce a helper `Lemma exhaustive_4edge_aux : ... = true` proved by `vm_compute` alone, then derive `exhaustive_4edge` from it by case-analysis on the boolean.
- If still infeasible: factor `exhaustive_4edge` into 10 smaller `exhaustive_4edge_class_<n>` lemmas, each handling one pattern's NEGATION (i.e., `¬ pattern_n → some other pattern matches`). Splits the case space.

- [ ] **Step 8: Verify Qed time and file size**

```bash
time mise exec -- dune build -j 2 posets/dimension/N5Exhaustive/N5Reflect.vo
wc -l posets/dimension/N5Exhaustive/N5Reflect.v
```

Expected: build time < 5 min (TIMEOUT threshold), file < 500 lines.

If TIMEOUT: split per coq-fast-compile skill. Move `exhaustive_4edge` and pattern definitions to separate files. **Do not retry the same build.**

- [ ] **Step 9: Run admit-introduction checklist (if any new `Admitted` introduced)**

For each new `Admitted`:
1. Statement mathematically true? (Counter-example search 5+ min.)
2. Not circularly dependent? (Trace `apply`/`exact` chain.)
3. Statement precise?
4. Statement minimal?
5. Role documented above the `Admitted`?

If any new admit: invoke `proof-skeptic` agent before commit.

- [ ] **Step 10: Commit**

```bash
git add posets/dimension/N5Exhaustive/N5Reflect.v
git commit -m "feat(N5Reflect): Fin.t 5 reflection — exhaustive_4edge (Qed)

Boolean reflection layer for 5-element posets.  M5 = Fin.t 5 ->
Fin.t 5 -> bool, with is_poset_b / edge_count_b / 10 pattern
booleans.  exhaustive_4edge proved by structured enumeration over
sublists of size 4 of the 25 ordered pairs."
```

- [ ] **Step 11: Update status doc**

Append session R1 entry: commit hash, admit delta (still 3 — admit reductions happen in R3), file size, Qed time.

---

## Session R2: `N5Transport.v` — bridge to abstract `B`-poset (3 hr)

**Files:**
- Create: `posets/dimension/N5Exhaustive/N5Transport.v`

Target: < 500 lines. The 10 `iff` lemmas are **subagent-parallelizable** — one per pattern, same shape.

- [ ] **Step 1: Stub the file with imports and Section**

```coq
(** Transport between [Fin.t 5] reflection and abstract [B]-poset
    cascade.

    Section [Transport] takes a 5-element covering of [B] via 5
    pairwise-distinct elements [a..e] and [Hcov], and constructs a
    bijection [Fin.t 5 ↔ B] together with a matrix [R2_matrix : M5]
    mirroring [R2].  Each pattern boolean is then equivalent to the
    corresponding abstract [exists] shape from [EdgeCount4_*.v]. *)
From Stdlib Require Import Fin Bool List Arith Lia Classical
  ClassicalDescription IndefiniteDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount N5Reflect.

Section Transport.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.
  Variables a b c d e : B.
  Hypothesis Hab : a <> b. Hypothesis Hac : a <> c.
  Hypothesis Had : a <> d. Hypothesis Hae : a <> e.
  Hypothesis Hbc : b <> c. Hypothesis Hbd : b <> d.
  Hypothesis Hbe : b <> e. Hypothesis Hcd : c <> d.
  Hypothesis Hce : c <> e. Hypothesis Hde : d <> e.
  Hypothesis Hcov : forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e.
```

- [ ] **Step 2: Define `from_fin` and `to_fin`**

```coq
  Definition from_fin (i : Fin.t 5) : B :=
    match i with
    | Fin.F1 => a
    | Fin.FS Fin.F1 => b
    | Fin.FS (Fin.FS Fin.F1) => c
    | Fin.FS (Fin.FS (Fin.FS Fin.F1)) => d
    | _ => e
    end.

  Definition to_fin (x : B) : Fin.t 5 :=
    proj1_sig
      (constructive_indefinite_description
        (fun i => from_fin i = x)
        ltac:(destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
              [exists Fin.F1
              | exists (Fin.FS Fin.F1)
              | exists (Fin.FS (Fin.FS Fin.F1))
              | exists (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
              | exists (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))];
              symmetry; exact Hx)).
```

Build.

- [ ] **Step 3: Prove `from_fin_to_fin` round-trip**

```coq
  Lemma from_to_fin : forall x : B, from_fin (to_fin x) = x.
  Proof.
    intro x. unfold to_fin.
    exact (proj2_sig (constructive_indefinite_description _ _)).
  Qed.

  Lemma to_from_fin : forall i : Fin.t 5, to_fin (from_fin i) = i.
  Proof.
    intro i.
    (* Use injectivity of from_fin (relies on pairwise-distinctness Hab..Hde). *)
    apply (from_fin_injective i (to_fin (from_fin i))).
    rewrite from_to_fin. reflexivity.
  Qed.
```

(`from_fin_injective` is a 5×5 case split on `i` and `j`, discharging diagonals by reflexivity and off-diagonals by the `H_*` distinctness hypotheses. ~30 lines.)

Build.

- [ ] **Step 4: Define `R2_matrix`**

```coq
  Definition R2_matrix : M5 :=
    fun i j =>
      if excluded_middle_informative (R2 (from_fin i) (from_fin j))
      then true else false.
```

- [ ] **Step 5: Prove `R2_matrix_is_poset`**

```coq
  Lemma R2_matrix_is_poset : is_poset_b R2_matrix = true.
  Proof.
    unfold is_poset_b. apply andb_true_iff. split.
    apply andb_true_iff. split.
    - (* is_refl: from HR2.(poset_refl). *)
      ...
    - (* is_antisym: from HR2.(poset_antisym). *)
      ...
    - (* is_trans: from HR2.(poset_trans). *)
      ...
  Qed.
```

(Each branch is a `forallb` over `all5` or `all_pairs`; reduces to a 5- or 25-case analysis with explicit witness from `HR2`.)

- [ ] **Step 6: Prove `R2_matrix_edge_count_eq`**

```coq
  Lemma R2_matrix_edge_count_eq :
    edge_count_b R2_matrix = edge_count_5 R2 a b c d e.
  Proof.
    unfold edge_count_b, edge_count_5.
    (* 20-term sum equals 20-term sum.  Each strict_b R2_matrix i j
       agrees with strict_indicator (from_fin i) (from_fin j). *)
    ...
  Qed.
```

- [ ] **Step 7: Pattern iff lemmas — dispatch as parallel subagents**

For each of the 10 patterns: prove `is_<pattern>_b R2_matrix = true <-> <abstract exists shape>`.

**Subagent dispatch (skill: `superpowers:dispatching-parallel-agents`):**
- Spawn 10 parallel `claude` subagents, one per pattern.
- Each receives: pattern name, edge list in Fin.t 5, abstract `exists` shape (copy from corresponding `EdgeCount4_*.v` Lemma signature).
- Each produces: one `Lemma is_<pattern>_b_iff` Qed-proven in its own file `posets/dimension/N5Exhaustive/N5Transport_<pattern>.v`.
- Main session integrates via `Require Import` into `N5Transport.v`.

Per-subagent template (one example — claw_up):

```coq
Lemma is_4claw_up_b_iff :
  is_4claw_up_b R2_matrix = true <->
  exists r l1 l2 l3 l4 : B,
    r <> l1 /\ r <> l2 /\ r <> l3 /\ r <> l4 /\
    l1 <> l2 /\ l1 <> l3 /\ l1 <> l4 /\
    l2 <> l3 /\ l2 <> l4 /\ l3 <> l4 /\
    R2 l1 r /\ R2 l2 r /\ R2 l3 r /\ R2 l4 r.
Proof.
  split.
  - intro Hb. (* boolean → existential via to_fin *)
    ...
  - intros [r [l1 [l2 [l3 [l4 [Hne1 [...]]]]]]].
    (* existential → boolean via to_fin and definition unfolding *)
    ...
Qed.
```

- [ ] **Step 8: Build the integrated file**

```bash
mise exec -- dune build -j 2 posets/dimension/N5Exhaustive
```

Expected: all 10 sub-files + N5Transport.v compile.

- [ ] **Step 9: Admit-introduction checklist for any new `Admitted`** (likely none if subagents finish all 10).

- [ ] **Step 10: Commit**

```bash
git add posets/dimension/N5Exhaustive/N5Transport*.v
git commit -m "feat(N5Transport): Fin.t 5 ↔ B transport + 10 pattern iff lemmas (Qed)

Bijection to_fin/from_fin from Hcov, R2_matrix construction,
R2_matrix_is_poset, R2_matrix_edge_count_eq, plus the 10
is_<pattern>_b_iff lemmas linking the boolean patterns to the
abstract exists shapes."
```

- [ ] **Step 11: Update status doc** with commit hash + admit delta (still 3).

---

## Session R3: wire reflection into EdgeCount4 (2 hr)

**Files:**
- Modify: `posets/dimension/N5Exhaustive/EdgeCount4.v:218-221` (replace `admit. Admitted.`)

- [ ] **Step 1: Add the `Require Import N5Transport`**

In `EdgeCount4.v` imports (line 13-19):

```coq
From Dimension.N5Exhaustive Require Import
  EdgeCount EdgeCount4_extract
  EdgeCount4_4claw_up EdgeCount4_4claw_down
  EdgeCount4_bowtie EdgeCount4_disjoint
  EdgeCount4_chain3_below EdgeCount4_chain3_above
  EdgeCount4_M_shape EdgeCount4_K32mm
  EdgeCount4_3claw_up_xp EdgeCount4_3claw_down_xl
  N5Reflect N5Transport.
```

- [ ] **Step 2: Replace the `admit.` with reflection invocation**

At `EdgeCount4.v:214-221`, replace:

```coq
    (* No class matches: ... we leave as the remaining gap for this session. *)
    admit.
  Admitted.
```

with:

```coq
    (* All 10 patterns negated.  Invoke reflection. *)
    pose proof (R2_matrix_is_poset R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov) as Hp.
    pose proof (R2_matrix_edge_count_eq R2 a b c d e
                  Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov) as Hec_b.
    rewrite Hec in Hec_b.
    destruct (exhaustive_4edge _ Hp Hec_b) as
      [H11 | [H12 | [H13 | [H14 | [H15 | [H16 | [H17 | [H18 | [H19' | H20]]]]]]]]];
    [ apply (is_4claw_up_b_iff R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov) in H11;
      contradiction (Hn11 H11)
    | apply (is_4claw_down_b_iff R2 a b c d e
              Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov) in H12;
      contradiction (Hn12 H12)
    | apply (is_bowtie_b_iff R2 a b c d e _) in H13;
      contradiction (Hn13 H13)
    | apply (is_disjoint_b_iff R2 a b c d e _) in H14;
      contradiction (Hn14 H14)
    | apply (is_chain3_below_b_iff R2 a b c d e _) in H15;
      contradiction (Hn15 H15)
    | apply (is_chain3_above_b_iff R2 a b c d e _) in H16;
      contradiction (Hn16 H16)
    | apply (is_M_shape_b_iff R2 a b c d e _) in H17;
      contradiction (Hn17 H17)
    | apply (is_K32mm_b_iff R2 a b c d e _) in H18;
      contradiction (Hn18 H18)
    | apply (is_3claw_up_xp_b_iff R2 a b c d e _) in H19';
      contradiction (Hn19 H19')
    | apply (is_3claw_down_xl_b_iff R2 a b c d e _) in H20;
      contradiction (Hn20 H20) ].
  Qed.
```

Note: the existing destruct chain in `EdgeCount4.v` already binds `Hn11..Hn20` for the negation hypotheses. Verify hypothesis names match by reading lines ~46-208.

- [ ] **Step 3: Build EdgeCount4.v**

```bash
mise exec -- dune build -j 2 posets/dimension/N5Exhaustive/EdgeCount4.vo
```

Expected: success, `Admitted.` removed.

- [ ] **Step 4: Verify admit count dropped**

```bash
grep -rn "^[[:space:]]*Admitted\.$" posets/ | wc -l
```

Expected: `2` (was 3). Admits remaining: `n5_residual_classes_two_realizer` and `trotter_coverage_via_extremality`.

- [ ] **Step 5: Full project build**

```bash
mise build
```

Expected: green.

- [ ] **Step 6: Commit — admit #3 closed**

```bash
git add posets/dimension/N5Exhaustive/EdgeCount4.v
git commit -m "feat(EdgeCount4): close exhaustiveness via N5Reflect (Qed)

Replaces the 'leave as remaining gap' admit at EdgeCount4.v:221
with an invocation of exhaustive_4edge through the N5Transport
bridge.  Each of the 10 pattern negations Hn11..Hn20 in scope is
discharged by the corresponding is_<pattern>_b_iff lemma.  Admit
count: 3 → 2."
```

- [ ] **Step 7: Re-evaluate scope for `n5_residual_classes_two_realizer`**

The `N5DispatcherShapes.v:38` admit covers `edge_count_5 R2 a b c d e ∈ {2, ..., 9}` (non-antichain, non-chain, multi-edge cases). It is closed ONLY when reflection covers all those k.

Currently after R3: reflection covers k=4 only. Cascade covers k=1,2,3. Reflection does NOT yet cover k=5,...,9.

**Decision point:**
- If the dispatcher route `n5_nonantichain_nonchain_two_realizer` routes k=2,3 to existing EdgeCount2/EdgeCount3 cascades AND k=4 now to the fixed EdgeCount4 AND has no cases for k=5..9: write a follow-on plan `2026-05-28-phase-R-extend.md` adding `exhaustive_<k>edge` for k ∈ {5, 6, 7, 8, 9} via the same template. Add R4 + R5 sessions to close `n5_residual_classes_two_realizer`.
- If the dispatcher already covers k=5..9 elsewhere: write the wire-in for `N5DispatcherShapes.v:38` directly and close admit #1 in this session.

Read `posets/dimension/N5Dispatcher.v` (or wherever the dispatch sits) to determine which. Estimate 30 min for the read + decision.

- [ ] **Step 8: Update status doc + commit**

```bash
git add docs/superpowers/specs/2026-05-28-dimension-replan-status.md
git commit -m "docs: R3 done — admit count 3 → 2, R4 plan needed for k=5..9"
```

---

## Self-review checklist (completed by plan author before handoff)

- [x] **Spec coverage:** R0 (probe) ✓, R1 (`N5Reflect.v`) ✓, R2 (`N5Transport.v`) ✓, R3 (wire-in EdgeCount4) ✓. Admit #1 closure deferred to follow-on plan, with the decision point documented in R3 Step 7 — this is a real scope contingency, not a placeholder.
- [x] **Placeholder scan:** the `...` inside Coq proof bodies (Step 5/6 of R2, Step 7 of R1) is intentional research-content where the agent fills in tactic chains during the session. They are NOT plan placeholders — surrounding structure, hypotheses, and goal shapes are concrete. The plan flags these explicitly.
- [x] **Type consistency:** `M5`, `is_poset_b`, `edge_count_b`, `R2_matrix`, `from_fin`, `to_fin` names are stable across R1, R2, R3.
- [x] **Memory safety:** every build step uses `-j 2`. No cartesian-destruct + `try eauto` anywhere.
- [x] **Admit hygiene:** R1 Step 9 and R2 Step 9 explicitly run the admit-introduction checklist + `proof-skeptic` for any new admit.

## Key files quick reference

- Spec: `docs/superpowers/specs/2026-05-28-dimension-replan-design.md`
- Technical detail: `docs/superpowers/specs/2026-05-28-fin5-reflection-design.md`
- Status doc: `docs/superpowers/specs/2026-05-28-dimension-replan-status.md`
- Existing pattern signatures: `posets/dimension/N5Exhaustive/EdgeCount4_<pattern>.v`
- The just-landed Trotter helper (unrelated to Phase R): `RemovablePairs.v:1651` `aug_cycle_implies_step3_path`

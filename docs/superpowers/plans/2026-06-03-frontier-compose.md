# Frontier composition (Slice A) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Composing two antichains by a frontier `F` (`compose_le F`): prove a non-crossing (threshold/Ferrers) `F` keeps `dim ≤ 2`, and the S₃ crown `F` (`i≠j`) forces `dim ≥ 3` — the "when does connection preserve dimension" dichotomy.

**Architecture:** One new file `execution/FrontierCompose.v` (abstract poset-dimension theory reusing `Dimension`). Positive direction = explicit 2-realizer keyed on a threshold `(φ,ψ)` (modeled on `layered_chains_dim_le2`). Negative direction = the 3 crown critical pairs, any two of which form an alternating cycle, plus a pigeonhole over any realizer (uses the *forward* reversibility direction only).

**Tech Stack:** Coq/Rocq 9.1, Stdlib `List`/`Arith`/`Lia`/`Fin`/`Ensembles`/`Finite_sets`/`Classical`, the `Dimension` library (`DimDefs`, `CriticalPairs`, `Theorems`), `Posets.PosetClasses`. Builds via `bash .claude/scripts/timed-build.sh <secs> <target> 2`.

**Spec:** `docs/superpowers/specs/2026-06-03-frontier-compose-design.md`. **Branch:** `frontier-compose`.

**Plan-stage refinement of the spec (intentional):** the positive direction is delivered as **`threshold_dim_le2`** (F in threshold form `φ a ≤ ψ b`), which is the directly-buildable form of "non-crossing," plus **`threshold_Ferrers`** (threshold ⟹ Ferrers). The fully-general `ferrers_dim_le2` needs `Ferrers ⟹ threshold` (heavy finite combinatorics) and is **deferred** (noted in docs). The negative core is **`crown3_dim_ge_3`** (dim ≥ 3 — the load-bearing "preservation fails"); `dim = 3` via an explicit 3-realizer is a **stretch** (Task 4, optional).

**Key API (verified):**
- `PosetDimension {A R} (d:nat)` — fields `dimension_realizer` (Ensemble of relations), `dimension_is_realizer`, `dimension_cardinality : cardinal _ dimension_realizer d`, `dimension_is_minimum : forall r n, IsRealizer r -> cardinal _ r n -> d <= n` (`DimDefs.v`).
- `IsLinearExtension R L` / `IsRealizer R realizer` (`DimDefs.v`); realizer = set of linear extensions whose intersection is R.
- `IsCriticalPair R x y` — `critical_incomparable : Incomparable R x y`, `critical_down : forall a, Strict R a x -> R a y`, `critical_up : forall b, Strict R y b -> R x b` (`CriticalPairs.v:83`).
- `critical_pair_realizer_iff` (`CriticalPairs.v:~424`): for an inhabited all-linear realizer, `IsRealizer R realizer <-> (forall x y, IsCriticalPair R x y -> exists L, In _ realizer L /\ L y x)`.
- `IsAlternatingCycle R pairs` / `check_alternating_cycle` (`CriticalPairs.v:187`). The theorem `critical_pairs_reversible_iff_no_alternating_cycle` is in a section with `Context (S : Ensemble (A*A))`; its FORWARD direction: `(exists L, IsLinearExtension R L /\ forall x y, In _ S (x,y) -> L y x) -> ~ (exists cycle, ... /\ IsAlternatingCycle R cycle)`.
- Realizer 2-construction + cardinal-≤-2 pattern: copy `layered_chains_dim_le2` (`execution/BarrierExecDim.v:14-128`) / `disjoint_chains_dim_le2` (`execution/DisjointChainsDim.v:14-100`).

---

### Task 1: composition operator, `compose_IsPoset`, Ferrers/threshold + register

**Files:**
- Create: `execution/FrontierCompose.v`
- Modify: `execution/dune` (add `FrontierCompose` after `RoundSemExamples`), `_CoqProject` (add the file)

- [ ] **Step 1: Create `execution/FrontierCompose.v`**

```coq
(* Composing two antichains by a frontier F : the bipartite poset compose_le F.
   Dichotomy (this file): non-crossing (threshold/Ferrers) F => dim <= 2;
   the S3 crown F (i<>j) => dim >= 3. Abstract poset-dimension theory. *)
From Stdlib Require Import List Arith Lia Fin Ensembles Finite_sets Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Theorems.
Import ListNotations.

Inductive Carrier (A B : Type) : Type := inA (a : A) | inB (b : B).
Arguments inA {A B} a. Arguments inB {A B} b.

Definition compose_le {A B} (F : A -> B -> Prop) (x y : Carrier A B) : Prop :=
  match x, y with
  | inA a, inA a' => a = a'
  | inB b, inB b' => b = b'
  | inA a, inB b  => F a b
  | inB _, inA _  => False
  end.

#[export] Instance compose_IsPoset {A B} (F : A -> B -> Prop) :
  IsPoset (Carrier A B) (compose_le F).
Proof.
  constructor.
  - intro x. destruct x; reflexivity.
  - intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl;
      intros Hxy Hyx; try (subst; reflexivity); try contradiction.
  - intros x y z; destruct x as [a|b]; destruct y as [a'|b']; destruct z as [a''|b''];
      simpl; intros Hxy Hyz; try contradiction; subst; try reflexivity; try assumption.
Qed.

Definition Ferrers {A B} (F : A -> B -> Prop) : Prop :=
  forall a1 a2 b1 b2, F a1 b1 -> F a2 b2 -> F a1 b2 \/ F a2 b1.

Lemma threshold_Ferrers :
  forall {A B} (phi : A -> nat) (psi : B -> nat) (F : A -> B -> Prop),
    (forall a b, F a b <-> phi a <= psi b) -> Ferrers F.
Proof.
  intros A B phi psi F Hthr a1 a2 b1 b2 H1 H2.
  apply Hthr in H1; apply Hthr in H2.
  destruct (Nat.le_ge_cases (phi a1) (phi a2)) as [Hle | Hge].
  - left.  apply Hthr. lia.
  - right. apply Hthr. lia.
Qed.
```

Implementer notes: if `compose_IsPoset`'s `constructor`/bullet shape differs, read `rhb_IsPoset` (`execution/RoundSem.v`) for the 3-field pattern. The trans case is a finite case split (8 constructor combos); `subst; (reflexivity || assumption || contradiction)` should close each.

- [ ] **Step 2: Register** — `execution/dune`: add `  FrontierCompose` after `  RoundSemExamples`. `_CoqProject`: add `execution/FrontierCompose.v` after `execution/RoundSemExamples.v`.

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 240 execution/FrontierCompose.vo 2`. Expected exit 0.

- [ ] **Step 4: Commit**
```bash
git add execution/FrontierCompose.v execution/dune _CoqProject
git commit -m "feat(frontier-compose): compose_le + compose_IsPoset + Ferrers/threshold"
```

---

### Task 2: positive — `threshold_dim_le2` (non-crossing preserves dim ≤ 2)

**Files:** Modify `execution/FrontierCompose.v` (append).

- [ ] **Step 1: Append the two-linear-extension realizer and the theorem**

Statement (the implementer builds the proof; see the construction below):
```coq
(* A,B carry injective indices (for tiebreaks); use Fin.t for concreteness.
   F threshold: F a b <-> phi a <= psi b. *)
Theorem threshold_dim_le2 :
  forall {mA mB} (phi : Fin.t mA -> nat) (psi : Fin.t mB -> nat)
         (F : Fin.t mA -> Fin.t mB -> Prop),
    (forall a b, F a b <-> phi a <= psi b) ->
    forall d, PosetDimension (compose_le F) d -> d <= 2.
```

Construction (mirror `layered_chains_dim_le2` in `execution/BarrierExecDim.v`):
- `idx : Fin.t m -> nat := proj1_sig (Fin.to_nat ·)` (an injective index).
- `M1 x y :=` lexicographic on key1, where
  `key1 (inA a) := (phi a, 0, idx a)`, `key1 (inB b) := (psi b, 1, idx b)` — i.e.
  `M1 x y := lex3 (key1 x) (key1 y)` (with the standard `<=`-lex closing ties reflexively).
- `M2 x y :=` lexicographic on key2, where `key2 (inA a) := (0, idx a)`,
  `key2 (inB b) := (1, idx b)` — i.e. **side first (all A before all B), then the
  index in the SAME direction** ... **no:** within-side must be REVERSED vs M1, so
  use `key2 (inA a) := (0, mA - idx a)`, `key2 (inB b) := (1, mB - idx b)` (reverse
  the index), side-major. `M2 x y := lex2 (key2 x)(key2 y)`.
- Prove `IsLinearExtension (compose_le F) M1` and `… M2`:
  * total + poset: `M1`/`M2` are lex orders on injective keys (use `lt_eq_lt_dec`/`lia`),
    so total, refl, antisym (keys injective ⟹ equal keys ⟹ equal element: `Fin`
    index injective + side tag), trans by `lia`.
  * extends `compose_le F`: `inA a < inB b` (= `F a b` = `phi a <= psi b`): in M1,
    `key1(inA a)=(phi a,0,_) <=lex (psi b,1,_)` iff `phi a < psi b` or (`=` and `0<1`)
    iff `phi a <= psi b` ✓; in M2, side `0 < 1` ⟹ `a < b` always ✓. Same-side equal
    elements: refl.
- `Hcap : forall x y, compose_le F x y <-> M1 x y /\ M2 x y`:
  * cross `inA a, inB b`: M1 ⟺ `phi a<=psi b`, M2 always; so `M1∧M2 ⟺ phi a<=psi b ⟺ F a b ⟺ compose_le`. ✓
  * cross `inB b, inA a`: M1 (`b<a` iff `psi b<phi a`) ∧ M2 (`b<a` never) ⟹ never; compose_le also never. ✓
  * same side `inA a, inA a'`: M1 by `(phi,idx)`, M2 by reverse `idx`; `M1∧M2` ⟹ `idx a <= idx a' ∧ idx a >= idx a'` ⟹ `idx a = idx a'` ⟹ `a = a'` (= compose_le). ✓ similarly `inB`.
- Realizer `{M1, M2}`, `cardinal ≤ 2` (copy the `Hcard`/`card_add` block from
  `layered_chains_dim_le2`), then `dimension_is_minimum Hdim … : d <= 2`.

Implementer note: this is a real construction (~150–220 lines). The closest template is `layered_chains_dim_le2` (BarrierExecDim.v:14–128) — copy its skeleton (build L1/L2, prove `IsLinearExtension`, prove `Hcap`, build the realizer ensemble, `Hcard`, `dimension_is_minimum`) and replace the `(lay,comp)` keys with the `(phi/psi, side, idx)` keys above. Do NOT `admit`. If a sub-lemma (e.g. lex totality) is fiddly, factor it out. Report BLOCKED with the specific goal if the construction stalls.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 360 execution/FrontierCompose.vo 2`. Exit 0.

- [ ] **Step 3: Commit**
```bash
git add execution/FrontierCompose.v
git commit -m "feat(frontier-compose): threshold_dim_le2 (non-crossing frontier preserves dim<=2)"
```

---

### Task 3: negative — `crown3_dim_ge_3` (the S₃ frontier raises dimension)

**Files:** Modify `execution/FrontierCompose.v` (append).

- [ ] **Step 1: Append the crown, its critical pairs, the alternating cycle, and the lower bound**

```coq
Definition crownF (a b : Fin.t 3) : Prop := a <> b.
Definition crown3 : Carrier (Fin.t 3) (Fin.t 3) -> Carrier (Fin.t 3) (Fin.t 3) -> Prop
  := compose_le crownF.

(* each (inA i, inB i) is a critical pair of crown3 *)
Lemma crown_critical : forall i : Fin.t 3, IsCriticalPair crown3 (inA i) (inB i).
(* Proof: critical_incomparable: ~(crown3 (inA i)(inB i) \/ crown3 (inB i)(inA i))
   = ~(crownF i i \/ False) = ~(i<>i) -- holds.  critical_down: Strict crown3 a (inA i)
   -> crown3 a (inB i): a must be inA j with j=i (A antichain) and a<>inA i (Strict)
   -- impossible, vacuous OR a=inB.. (no b<inA), so down-closure vacuous/trivial.
   critical_up symmetric. Mostly a case analysis on a/b being inA/inB. *)

(* any two distinct crown critical pairs form an alternating cycle of length 2 *)
Lemma crown_alt_cycle : forall i j : Fin.t 3, i <> j ->
  IsAlternatingCycle crown3 [(inA i, inB i); (inA j, inB j)].
(* Proof: IsAlternatingCycle [(x0,y0);(x1,y1)] = (both critical, via crown_critical)
   /\ check_alternating_cycle x0 y0 [(x1,y1)]
   = R x1 y0 /\ check x0 y1 [] = crown3 (inA j)(inB i) /\ crown3 (inA i)(inB j)
   = (j<>i) /\ (i<>j) -- both hold. *)

(* the load-bearing result: connecting two 3-antichains by i<>j gives dim >= 3 *)
Theorem crown3_dim_ge_3 : forall d, PosetDimension crown3 d -> 3 <= d.
```

Lower-bound proof strategy (the substantive proof):
1. From `PosetDimension crown3 d`: let `r := dimension_realizer`, with `IsRealizer crown3 r` and `cardinal _ r d`. `r` is inhabited and all-linear.
2. By `critical_pair_realizer_iff` (forward), for each `i`, `crown_critical i` gives `exists L, In _ r L /\ L (inB i) (inA i)` — pick `Li` reversing the i-th critical pair.
3. **`Li` are pairwise distinct:** if `Li = Lj` (`i<>j`) reverses both `(inA i,inB i)` and `(inA j,inB j)`, then with `S := {(inA i,inB i),(inA j,inB j)}` the FORWARD direction of `critical_pairs_reversible_iff_no_alternating_cycle` (instantiated at this `S`) says: `(exists L linear, reverses S) -> no alt cycle in S`. But `crown_alt_cycle i j` exhibits an alt cycle in `S` → contradiction. So `i <> j -> Li <> Lj`.
4. **Pigeonhole:** `L0, L1, L2` are three distinct elements of `r`, so `cardinal _ r d -> 3 <= d`. Construct via: `r` contains `Add (Add (Add Empty L0) L1) L2` as a subset of distinct elements ⟹ `cardinal r d >= 3` (use `incl_card_le` / `cardinal` monotonicity from `Finite_sets_facts`, or `card_add` lower bounds in `posets/dimension/Theorems.v`).

Implementer notes: Steps 1–3 are direct applications of the cited lemmas. Step 4 (the Ensembles pigeonhole: 3 distinct members ⟹ cardinal ≥ 3) is the fiddliest — look in `posets/dimension/Theorems.v` (`cardinal_subtract_sn` and neighbors) and Stdlib `Finite_sets_facts` (`incl_card_le`, `cardinal_unicity`) for the right lemma; the goal is "an injective image of a 3-element set into `r` bounds `cardinal r` below by 3." Do NOT `admit`. If Step 4 stalls after a genuine search, report BLOCKED with the exact goal — the controller will decide whether to escalate (the spec permits delivering `dim ≥ 3` via the obstruction with the gap flagged, never silently admitted).

To instantiate `critical_pairs_reversible_iff_no_alternating_cycle` at a 2-element `S`: `S := fun p => p = (inA i, inB i) \/ p = (inA j, inB j)` (as an `Ensemble (Carrier*Carrier)`); the theorem's section `Context (S)` is satisfied by passing this `S`.

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 480 execution/FrontierCompose.vo 2`. Exit 0.

- [ ] **Step 3: Print Assumptions** — temporarily append `Print Assumptions crown3_dim_ge_3. Print Assumptions threshold_dim_le2.`, build, read output (expect classical axioms `classic`/`constructive_*`/`proof_irrelevance`/`Extensionality_Ensembles`; NO `admit`/`Admitted`), then remove and rebuild green.

- [ ] **Step 4: Commit**
```bash
git add execution/FrontierCompose.v
git commit -m "feat(frontier-compose): crown3_dim_ge_3 (S3 frontier raises dimension to >= 3)"
```

---

### Task 4 (STRETCH, optional): `crown3_dim_eq_3` via an explicit 3-realizer

**Files:** Modify `execution/FrontierCompose.v` (append). **Skip if Task 3 ran long; `dim ≥ 3` is the headline.**

- [ ] **Step 1:** Build three linear extensions `N0,N1,N2` of `crown3` (the standard S₃ realizer: `Nk` places `inA k` just above the other `inA`s and `inB k` just below the other `inB`s so that `inA k ∥ inB k` is the only cross-incomparability `Nk` leaves) and prove `crown3 = N0 ∩ N1 ∩ N2`, giving a realizer of cardinality 3 ⟹ `d <= 3` via `dimension_is_minimum`. Combine with `crown3_dim_ge_3`:
```coq
Theorem crown3_dim_eq_3 : forall d, PosetDimension crown3 d -> d = 3.
Proof. intros d Hd. pose proof (crown3_dim_ge_3 d Hd). (* + d <= 3 *) lia. Qed.
```

- [ ] **Step 2: Build + Step 3: Commit** (`feat(frontier-compose): crown3_dim_eq_3 (exact, via explicit 3-realizer)`). If the 3-realizer proves too costly, **skip this task** — note it as future work.

---

### Task 5: examples `FrontierComposeExamples.v`

**Files:** Create `execution/FrontierComposeExamples.v`; modify `execution/dune` + `_CoqProject`.

- [ ] **Step 1: Create the examples**

```coq
(* Frontier composition dichotomy: worked instances (test-only). *)
From Stdlib Require Import List Arith Lia Fin.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Execution Require Import FrontierCompose.
Import ListNotations.

(* a non-crossing (threshold) frontier on Fin 2 / Fin 2: F i j := idx i <= idx j *)
Definition phi2 (a : Fin.t 2) : nat := proj1_sig (Fin.to_nat a).
Definition psi2 (b : Fin.t 2) : nat := proj1_sig (Fin.to_nat b).
Definition Fstair (a b : Fin.t 2) : Prop := phi2 a <= psi2 b.

Example stair_ferrers : Ferrers Fstair.
Proof. apply (threshold_Ferrers phi2 psi2 Fstair). intros a b. unfold Fstair. reflexivity. Qed.

Example stair_dim_le2 : forall d, PosetDimension (compose_le Fstair) d -> d <= 2.
Proof. apply (threshold_dim_le2 phi2 psi2 Fstair). intros a b. unfold Fstair. reflexivity. Qed.

(* the crown is NOT non-crossing, and its composite has dim >= 3 *)
Example crown_not_ferrers : ~ Ferrers crownF.
Proof.
  intro HF. unfold Ferrers, crownF in HF.
  (* witnesses i=F1,j=F2: crownF F1 F2 (1<>2), crownF F2 F1, but ~crownF F1 F1, ~crownF F2 F2 *)
  (* pick two distinct Fin.t 3 elements and discharge by decide/lia on their indices *)
Admitted. (* implementer: replace with the concrete crossing witnesses; do NOT leave admitted *)

Example crown_dim_ge_3 : forall d, PosetDimension crown3 d -> 3 <= d.
Proof. exact crown3_dim_ge_3. Qed.
```

Implementer: replace the `Admitted` in `crown_not_ferrers` with concrete `Fin.t 3` witnesses (two distinct elements `i,j`; `crownF i j` and `crownF j i` hold, `crownF i i`/`crownF j j` fail; the `HF` instance gives `crownF i i \/ crownF j j`, both false → contradiction). NO admits in the committed file.

- [ ] **Step 2: Register** (`dune` + `_CoqProject`, after `FrontierCompose`). **Step 3: Build** `bash .claude/scripts/timed-build.sh 300 execution/FrontierComposeExamples.vo 2`. **Step 4: Commit** (`test(frontier-compose): Ferrers staircase dim<=2 vs crown dim>=3`).

---

### Task 6: export + docs + whole-project green

**Files:** Modify `execution/Execution.v`, `docs/INDEX.md`, `execution/DIM2_CLOCK.md`.

- [ ] **Step 1: Export** — `execution/Execution.v`: append ` FrontierCompose` to the `Require Export` line.
- [ ] **Step 2: INDEX.md** — add a "Frontier composition" subsection: `compose_le`/`compose_IsPoset`; `Ferrers`/`threshold_Ferrers`; `threshold_dim_le2` (non-crossing preserves dim ≤ 2); `crownF`/`crown3`/`crown_critical`/`crown_alt_cycle`/`crown3_dim_ge_3` (the S₃ frontier ⟹ dim ≥ 3). State the dichotomy and that `ferrers_dim_le2` (full Ferrers) is deferred (needs Ferrers⟹threshold).
- [ ] **Step 3: DIM2_CLOCK.md** — a note: connecting two executions by a frontier preserves dim-2 when the frontier is non-crossing (threshold/Ferrers) and can raise it to 3 otherwise (the crown), with `threshold_dim_le2` / `crown3_dim_ge_3` as the witnesses.
- [ ] **Step 4: Whole-project build** — `bash .claude/scripts/timed-build.sh 1800 @all 4`. Exit 0.
- [ ] **Step 5: Commit** (`docs(frontier-compose): export + INDEX + DIM2_CLOCK dichotomy note`).

---

## Self-Review

**Spec coverage:** Component 1 (compose_le/IsPoset/Ferrers) → Task 1; Component 2 (positive) → Task 2 (as `threshold_dim_le2`, the buildable form; full `ferrers_dim_le2` deferred — noted); Component 3 (crown) → Tasks 3 (`dim≥3`, core) + 4 (`=3`, stretch); Component 4 (examples) → Task 5; wiring/docs/green → Tasks 1,5,6. ✓

**Placeholder scan:** Task 5's `crown_not_ferrers` ships with an `Admitted` placeholder that the step text explicitly orders replaced before commit (concrete `Fin.t 3` witnesses). The three hard proofs (`threshold_dim_le2`, `crown_critical`/`crown_alt_cycle`, `crown3_dim_ge_3` pigeonhole) are given as statements + detailed strategies citing exact template lemmas — intentional for research-grade proofs, with explicit "no admit / report BLOCKED" instructions.

**Type consistency:** `compose_le`/`Carrier`/`inA`/`inB`/`Ferrers`/`threshold_Ferrers`/`threshold_dim_le2`/`crownF`/`crown3`/`crown_critical`/`crown_alt_cycle`/`crown3_dim_ge_3` names and signatures are consistent across tasks. `crown3 = compose_le crownF`. The positive uses `Fin.t mA/mB` (for injective tiebreak indices); examples instantiate at `Fin.t 2`/`Fin.t 3`.

**Risk notes:** the load-bearing proofs are `threshold_dim_le2` (Task 2 — copy `layered_chains_dim_le2`) and the `crown3_dim_ge_3` pigeonhole (Task 3, Step 1.4 — the Ensembles `cardinal ≥ 3` step). Both have concrete routes; if either stalls, the implementer reports BLOCKED (no silent admit) and the controller decides escalation. `crown_critical`/`crown_alt_cycle` are small case-analyses. Task 4 is optional.

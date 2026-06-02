# True-barrier execution dim ≤ 2 (addresses finding 1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development.

**Goal:** Prove a fully-synchronized (true N-way barrier) execution has dim ≤ 2 for **arbitrary N**, closing finding 1's N>4 gap for the synchronized regime.

**Architecture:** `execution/BarrierExecDim.v` — `layered_chains_dim_le2` (generic, extends `disjoint_chains_dim_le2` with a layer level), the barrier order `blo` from a schedule, `hb_idx_le`, `blo_IsPoset`, `barrier_execution_dim_le2`. `execution/BarrierExecDimExamples.v` — an N=5 instance. Reuses finding 2 (`disjoint_chains_dim_le2`, `hb_same_index_msg`, `fb_comp`).

**Tech Stack:** Rocq 9.1; `DimDefs`, `DisjointChainsDim` (finding 2), `Rank`, `Schedule`, `ScheduleWf`, `SyncShape`, `Ordinal`. Builds via the wrapper.

---

## Task BE0: Scaffold
**Files:** create `execution/BarrierExecDim.v`, `execution/BarrierExecDimExamples.v`; modify `execution/dune`, `_CoqProject`.
- [ ] **Step 1: `execution/BarrierExecDim.v`**
```coq
(* True N-way barriers: the fully-synchronized execution order `blo` (every index a
   full barrier) has dimension <= 2 for ANY process count -- addresses review finding 1. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                           ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape
                              DisjointChainsDim.
Import ListNotations.
#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.
```
- [ ] **Step 2: `execution/BarrierExecDimExamples.v`**
```coq
(* N=5 barrier execution has dim <= 2 (beyond the pairwise model's <=4 reach) (test-only). *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                              Ordinal DisjointChainsDim BarrierExecDim.
Import ListNotations.
```
- [ ] **Step 3/4:** add `BarrierExecDim`, `BarrierExecDimExamples` to `execution/dune` + `_CoqProject` (after `DisjointChainsDimExamples`).
- [ ] **Step 5: build** `bash .claude/scripts/timed-build.sh 120 execution/BarrierExecDimExamples.vo 2` → EXIT=0.
- [ ] **Step 6: commit** `git add -A && git commit -m "chore(execution): scaffold BarrierExecDim modules"`.

---

## Task BE1: generic `layered_chains_dim_le2` (`BarrierExecDim.v`)
Append. **Model on the already-compiled `execution/DisjointChainsDim.v` `disjoint_chains_dim_le2`** — this is that proof with an extra `lay` level prepended to the lexicographic key (both `L1`/`L2` order `lay` forward; only `comp` differs forward/reverse). Read that file first; mirror its `IsLinearExtension`/`IsRealizer`/`cardinal` plumbing (including the `Ensembles.Add`/`Ensembles.Empty_set` qualification it needed).

```coq
Lemma layered_chains_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (lay comp : A -> nat),
    (forall x y, lay x < lay y -> R x y) ->
    (forall x y, R x y -> lay x <= lay y) ->
    (forall x y, R x y -> lay x = lay y -> comp x = comp y) ->
    (forall x y, lay x = lay y -> comp x = comp y -> R x y \/ R y x) ->
    forall d, PosetDimension R d -> d <= 2.
Proof.
  intros A R HR lay comp Hbar Hresp Hrcomp Hchain d Hdim.
  set (L1 := fun x y : A => lay x < lay y \/
               (lay x = lay y /\ (comp x < comp y \/ (comp x = comp y /\ R x y)))).
  set (L2 := fun x y : A => lay x < lay y \/
               (lay x = lay y /\ (comp y < comp x \/ (comp x = comp y /\ R x y)))).
  (* HL1, HL2 : IsLinearExtension R L1/L2 ; Hcap : R x y <-> L1 x y /\ L2 x y ;
     HReal : IsRealizer R {L1,L2} ; Hcard : cardinal <= 2 ; dimension_is_minimum => d<=2 *)
  ...
Qed.
```
Proof obligations (mirror `disjoint_chains_dim_le2`, adding the `lay` case split):
- **`IsLinearExtension R L1`** (`constructor` → `IsTotalOrder` → `IsPoset` fields `poset_refl`/`poset_antisym`/`poset_trans`, then `total_comparable`, then `linear_extends`):
  - refl: `lay x = lay x /\ (comp x = comp x /\ R x x)` → right;right (`poset_refl`).
  - antisym: from `L1 x y`, `L1 y x`: the `lay` strict cases give `lia` contradictions; equal-`lay` reduces to the `comp`-lex antisym (as in `disjoint_chains_dim_le2`) ⟹ `poset_antisym`.
  - trans: case-split both on `lay` (`<`/`=`) then `comp`; `lia` for the strict-`lay` compositions, `poset_trans` for the all-equal branch.
  - total_comparable: `destruct (lt_eq_lt_dec (lay x) (lay y))`; `<`→`left;left`; `>`→`right;left`; `=`→ inner `destruct (lt_eq_lt_dec (comp x) (comp y))` then `Hchain` for the comp-equal case (as in `disjoint_chains_dim_le2`).
  - linear_extends: `R x y` ⟹ `Hresp`: `lay x <= lay y`; if `lay x < lay y` → `left`; if `=` → `Hrcomp` gives `comp x = comp y` → right;right.
- **`L2`**: symmetric (swap `comp x < comp y` ↔ `comp y < comp x`; `lay` stays forward).
- **`Hcap`** (`R x y <-> L1 x y /\ L2 x y`): `→` via `Hresp`/`Hrcomp`. `←`: `destruct (lt_eq_lt_dec (lay x) (lay y))`: `<` ⟹ `Hbar` gives `R x y`; `=` ⟹ the comp-lex conjunction ⟹ `comp x = comp y /\ R x y` ⟹ `R x y`; `>` ⟹ both `L1`,`L2` false (their disjuncts need `lay x <= lay y`), contradiction with the hypotheses — i.e. this case can't arise from `L1 x y /\ L2 x y`, discharge by `lia`/`exfalso`.
- **`HReal`/`Hcard`/`dimension_is_minimum`**: copy verbatim from `disjoint_chains_dim_le2` (same `{L1,L2}` realizer, same `Ensembles.Add` cardinal-≤2 plumbing).
- [ ] **Build** `bash .claude/scripts/timed-build.sh 360 execution/BarrierExecDim.vo 2` → EXIT=0; zero admits.
- [ ] **Commit** `git add execution/BarrierExecDim.v && git commit -m "feat(execution): layered_chains_dim_le2 (barriers between layers + disjoint chains within => dim<=2)"`.

---

## Task BE2: the barrier order `blo` + arbitrary-N theorem (`BarrierExecDim.v`)
Append. Reuses finding 2 (`hb_same_index_msg`, `fb_comp`) for the within-layer hypotheses.

```coq
(* hb respects the index, via the rank 2*idx + c *)
Lemma hb_idx_le :
  forall s (x y : ep_carrier (exec_of_schedule s)),
    ep_order (exec_of_schedule s) x y ->
    snd (proj1_sig x) <= snd (proj1_sig y).
Proof.
  (* rank_hb_le : rp_rank (desugar s) (proj1_sig x) <= rp_rank … y ;
     desugar_rank_form gives rank = 2*idx + c, c<=1, for x and y; lia. *)
Admitted_REPLACE.

(* the fully-synchronized (true-barrier) order: every index a full barrier,
   real intra-layer message order as the tiebreak *)
Definition blo (s : Schedule)
  : ep_carrier (exec_of_schedule s) -> ep_carrier (exec_of_schedule s) -> Prop :=
  fun x y => snd (proj1_sig x) < snd (proj1_sig y)
          \/ (snd (proj1_sig x) = snd (proj1_sig y) /\ ep_order (exec_of_schedule s) x y).

#[export] Instance blo_IsPoset : forall s, IsPoset (ep_carrier (exec_of_schedule s)) (blo s).
Proof.
  intro s. constructor.
  - (* refl *) intro x. right. split; [reflexivity | apply poset_refl].
  - (* antisym *) intros x y Hxy Hyx. unfold blo in Hxy, Hyx.
    destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyx as [Hlt2|[He2 Hr2]];
      try lia. apply (poset_antisym _ _ Hr1 Hr2).
  - (* trans *) intros x y z Hxy Hyz. unfold blo in *.
    pose proof (hb_idx_le s) as Hle.
    destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyz as [Hlt2|[He2 Hr2]].
    + left; lia.
    + left; lia.
    + left; lia.
    + right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
Qed.

Theorem barrier_execution_dim_le2 :
  forall s, wf_schedule s -> forall d, PosetDimension (blo s) d -> d <= 2.
Proof.
  intros s Hwf d Hdim.
  apply (layered_chains_dim_le2 (blo s)
           (fun x => snd (proj1_sig x))
           (fun x => fb_comp s (proj1_sig x))
           _ _ _ _ d Hdim).
  - (* full barrier: lay x < lay y -> blo x y *) intros x y Hlt. left. exact Hlt.
  - (* respects layers: blo x y -> lay x <= lay y *)
    intros x y [Hlt|[He _]]; lia.
  - (* respects comp within layer: blo x y -> lay x = lay y -> comp x = comp y *)
    intros x y Hblo Heq. unfold blo in Hblo.
    destruct Hblo as [Hlt|[_ Hhb]]; [lia|].
    (* same index, ep_order x y : x=y (=> equal fb_comp) or hb_same_index_msg => fb_comp equal *)
    Admitted_REPLACE.
  - (* within-layer chain: lay x = lay y -> comp x = comp y -> blo x y \/ blo y x *)
    intros x y Heq Hcomp.
    (* finding 2's H2: same index + same fb_comp => ep_order x y \/ ep_order y x => blo .. *)
    Admitted_REPLACE.
Qed.
```
**Replace the three `Admitted_REPLACE` (NO admit in the final file):**
- `hb_idx_le`: `ep_order (exec_of_schedule s) = hb (desugar s)`. `rank_hb_le (desugar s) x y Hhb : rp_rank (desugar s) (proj1_sig x) <= rp_rank … y`. `rp_rank (desugar s) = desugar_rank s`. `destruct (desugar_rank_form s (proj1_sig x)) as [cx [Hcx Ex]]` and same for `y`; rewrite, `lia` (with `cx,cy <= 1` and `rank = 2*idx + c`, `rank x <= rank y` forces `idx x <= idx y`). Use `change`/`unfold` to align `rp_rank (desugar s)` with `desugar_rank s` if needed.
- respects-comp (3rd goal): reuse the EXACT H1 reasoning from `frontier_block_dim_le2` in `DisjointChainsDim.v` — `destruct (classic (proj1_sig x = proj1_sig y))`: if equal, `fb_comp` equal (rewrite); else `hb_same_index_msg s Hwf x y Heq Hhb Hneq` gives `In (px,py) (nth k …)`, and `fb_comp` of a receiver = its sender = `px` = `fb_comp` of the sender `x` (which is a `Send`/`Local` ⟹ maps to `px`). Lift the block-level H1 proof; it may be cleanest to factor a shared lemma `fb_comp_eq_of_hb_same_index : wf_schedule s -> snd(proj1 x)=snd(proj1 y) -> ep_order .. x y -> fb_comp s (proj1 x) = fb_comp s (proj1 y)` (prove once, reuse here and — optionally — refactor `frontier_block_dim_le2` to use it; do NOT break the existing file).
- within-layer chain (4th goal): reuse `frontier_block_dim_le2`'s H2 reasoning (same `fb_comp` ⟹ same matched pair/event ⟹ `ep_order`-comparable via the message edge / `ConnSync.msg_step`); conclude `blo x y \/ blo y x` by the `right;split;[exact Heq|…]` tiebreak form. If reusing is awkward, factor a shared lemma `hb_comparable_of_fb_comp_eq : wf_schedule s -> snd(proj1 x)=snd(proj1 y) -> fb_comp s (proj1 x)=fb_comp s (proj1 y) -> ep_order .. x y \/ ep_order .. y x`.

To enable reuse, it is acceptable to FIRST extract `fb_comp_eq_of_hb_same_index` and `hb_comparable_of_fb_comp_eq` as standalone lemmas in `DisjointChainsDim.v` (append; keep everything) and re-prove `frontier_block_dim_le2`'s H1/H2 via them — but ONLY if that refactor stays green; otherwise just prove them fresh here in `BarrierExecDim.v`.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 360 execution/BarrierExecDim.vo 2` (rebuild `DisjointChainsDim.vo` first if you touched it) → EXIT=0; zero admits.
- [ ] **Commit** `git add execution/BarrierExecDim.v [execution/DisjointChainsDim.v] && git commit -m "feat(execution): blo true-barrier order; barrier_execution_dim_le2 (dim<=2 for any N)"`.

---

## Task BE3: N=5 example + wiring + audit
**Files:** `execution/BarrierExecDimExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.
- [ ] **Step 1: N=5 punchline** — a 5-process barrier execution with dim ≤ 2 (beyond the pairwise ≤4 reach).
```coq
Definition s_bar5 : Schedule := {| sch_nprocs := 5; sch_frontiers := [ [] ; [] ] |}.
Lemma wf_s_bar5 : wf_schedule s_bar5.   (* both frontiers empty: wf_frontier n [] trivial *)
Example bar5_dim_le2 :
  forall d, PosetDimension (blo s_bar5) d -> d <= 2.
Proof. apply (barrier_execution_dim_le2 s_bar5 wf_s_bar5). Qed.
```
(Two barrier layers; each layer is a 5-event antichain — width 5 — so the cross-layer ordering is a genuine 5-way barrier, impossible to realize via pairwise `hb` for the `FullySynchronizing` notion. `bar5_dim_le2` shows dim ≤ 2 nonetheless.)
- [ ] **Step 2: build** `bash .claude/scripts/timed-build.sh 180 execution/BarrierExecDimExamples.vo 2` → EXIT=0.
- [ ] **Step 3: export** append `BarrierExecDim` to `execution/Execution.v`'s `Require Export` list.
- [ ] **Step 4: whole-project** `bash .claude/scripts/timed-build.sh 1800 @all 4` → EXIT=0.
- [ ] **Step 5: audit** scratch `execution/BEAudit.v` (`From Execution Require Import BarrierExecDim. Print Assumptions layered_chains_dim_le2. Print Assumptions barrier_execution_dim_le2.`), register, build, capture (expect standard classical/proof-irrelevance/choice only; NO `small_complement_le_2`), then REMOVE + revert registration.
- [ ] **Step 6: INDEX** add a `#### execution/BarrierExecDim.v` subsection: `layered_chains_dim_le2`, `blo`, `hb_idx_le`, `blo_IsPoset`, `barrier_execution_dim_le2`; note "addresses critical-review finding 1: true N-way barriers (the order `blo`) give dim ≤ 2 for ANY process count — the synchronized regime the pairwise `hb` model could only realize for N≤4. `blo` strengthens `hb` with barrier edges (synchronization reduces dimension)."
- [ ] **Step 7: commit** `git add execution/BarrierExecDimExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): N=5 barrier-exec example + export + INDEX (addresses finding 1)"`.

---

## Self-Review (vs the spec)
- **Coverage:** generic `layered_chains_dim_le2` (BE1); `blo`/`hb_idx_le`/`blo_IsPoset`/`barrier_execution_dim_le2` (BE2); N=5 example + wiring (BE3). Mapped.
- **Reuse:** `disjoint_chains_dim_le2` structure (BE1); `hb_same_index_msg`/`fb_comp` from finding 2 (BE2); `rank_hb_le`/`desugar_rank_form` (Rank/Schedule).
- **Name consistency:** `layered_chains_dim_le2`/`blo`/`hb_idx_le`/`blo_IsPoset`/`barrier_execution_dim_le2` across BE1–BE3.
- **Honest scope:** `blo` = `hb` strengthened by barrier edges (the true-barrier primitive); does NOT claim arbitrary message executions are dim ≤ 2; finding 1's pairwise limitation stays on record. The N=5 example is the concrete punchline.
- **No placeholders in final code:** the three `Admitted_REPLACE` MUST be replaced; build steps assert zero admits.

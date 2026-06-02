# Disjoint-chains dim ≤ 2 (closes review finding 2) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development.

**Goal:** Prove (1) a disjoint union of chains has dim ≤ 2 (generic), and (2) every frontier block of a well-formed schedule is such — discharging `fully_sync_dim_le2`'s per-block hypothesis.

**Architecture:** `execution/DisjointChainsDim.v` — `disjoint_chains_dim_le2` (explicit 2-realizer, no width/finiteness), the rank-based `hb_same_index_msg`, `fb_comp`, `frontier_block_dim_le2`, and the `fully_sync_frontier_dim_le2` corollary. `execution/DisjointChainsDimExamples.v` — a width>2 frontier-block example. Reuses the realizer/cardinal idiom from `DimTwoGeneric.dim2_record`.

**Tech Stack:** Rocq 9.1; `DimDefs`, `Schedule`/`Rank` (rank), `ScheduleWf`, `SyncShape`, `Ordinal`, `FullySyncDim2`, `Operators_Properties` (`clos_rt_rt1n`). Builds via the wrapper.

---

## Task DC0: Scaffold
**Files:** create `execution/DisjointChainsDim.v`, `execution/DisjointChainsDimExamples.v`; modify `execution/dune`, `_CoqProject`.
- [ ] **Step 1: `execution/DisjointChainsDim.v`**
```coq
(* A disjoint union of chains has dimension <= 2; hence every frontier block of a
   well-formed schedule has dim <= 2 (closes critical-review finding 2). *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                           ProofIrrelevance Relation_Operators Operators_Properties.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape.
Import ListNotations.
#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.
```
- [ ] **Step 2: `execution/DisjointChainsDimExamples.v`**
```coq
(* frontier block of width > 2 still has dim <= 2 (test-only). *)
From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Poset Schedule ScheduleWf SyncShape
                              Ordinal DisjointChainsDim.
Import ListNotations.
```
- [ ] **Step 3/4:** add `DisjointChainsDim`, `DisjointChainsDimExamples` to `execution/dune` + `_CoqProject` (after `TransformBExamples`).
- [ ] **Step 5: build** `bash .claude/scripts/timed-build.sh 120 execution/DisjointChainsDimExamples.vo 2` → EXIT=0.
- [ ] **Step 6: commit** `git add -A && git commit -m "chore(execution): scaffold DisjointChainsDim modules"`.

---

## Task DC1: generic `disjoint_chains_dim_le2` (`DisjointChainsDim.v`)
Append. Model the realizer/cardinal plumbing on `DimTwoGeneric.dim2_record` (read it).

```coq
Lemma disjoint_chains_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (comp : A -> nat),
    (forall x y, R x y -> comp x = comp y) ->
    (forall x y, comp x = comp y -> R x y \/ R y x) ->
    forall d, PosetDimension R d -> d <= 2.
Proof.
  intros A R HR comp Hrel Hchain d Hdim.
  set (L1 := fun x y : A => comp x < comp y \/ (comp x = comp y /\ R x y)).
  set (L2 := fun x y : A => comp y < comp x \/ (comp x = comp y /\ R x y)).
  (* both are linear extensions of R *)
  assert (HL1 : IsLinearExtension R L1).
  { constructor.
    - constructor.
      + constructor.
        * intro x. right. split; [reflexivity | apply poset_refl].
        * intros x y z Hxy Hyz. unfold L1 in *.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyz as [Hlt2|[He2 Hr2]].
          -- left; lia.
          -- left; lia.
          -- left; lia.
          -- right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
        * intros x y Hxy Hyx. unfold L1 in *.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyx as [Hlt2|[He2 Hr2]];
            try lia. apply (poset_antisym _ _ Hr1 Hr2).
      + intros x y. unfold L1. destruct (lt_eq_lt_dec (comp x) (comp y)) as [[Hlt|Heq]|Hgt].
        * left; left; exact Hlt.
        * destruct (Hchain x y Heq) as [Hr|Hr];
            [ left; right; split; [exact Heq | exact Hr]
            | right; right; split; [symmetry; exact Heq | exact Hr] ].
        * right; left; exact Hgt.
    - intros x y Hr. unfold L1. right. split; [apply Hrel; exact Hr | exact Hr]. }
  assert (HL2 : IsLinearExtension R L2).
  { constructor.
    - constructor.
      + constructor.
        * intro x. right. split; [reflexivity | apply poset_refl].
        * intros x y z Hxy Hyz. unfold L2 in *.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyz as [Hlt2|[He2 Hr2]].
          -- left; lia.
          -- left; lia.
          -- left; lia.
          -- right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
        * intros x y Hxy Hyx. unfold L2 in *.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyx as [Hlt2|[He2 Hr2]];
            try lia. apply (poset_antisym _ _ Hr1 Hr2).
      + intros x y. unfold L2. destruct (lt_eq_lt_dec (comp x) (comp y)) as [[Hlt|Heq]|Hgt].
        * right; left; exact Hlt.
        * destruct (Hchain x y Heq) as [Hr|Hr];
            [ left; right; split; [exact Heq | exact Hr]
            | right; right; split; [symmetry; exact Heq | exact Hr] ].
        * left; left; exact Hgt.
    - intros x y Hr. unfold L2. right. split; [apply Hrel; exact Hr | exact Hr]. }
  assert (Hcap : forall x y, R x y <-> (L1 x y /\ L2 x y)).
  { intros x y. split.
    - intro Hr. assert (Hc : comp x = comp y) by (apply Hrel; exact Hr).
      split; [right; split; assumption | right; split; assumption].
    - intros [H1 H2]. unfold L1, L2 in H1, H2.
      destruct H1 as [Hlt1|[He1 Hr1]].
      + destruct H2 as [Hlt2|[He2 Hr2]]; [ lia | lia ].
      + exact Hr1. }
  assert (HReal : IsRealizer R (fun L => L = L1 \/ L = L2)).
  { constructor.
    - intros L [-> | ->]; assumption.
    - intros x y. split.
      + intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HA HB].
        intros L [-> | ->]; assumption.
      + intro Hall. apply (proj2 (Hcap x y)). split;
          [ apply (Hall L1); left; reflexivity | apply (Hall L2); right; reflexivity ]. }
  assert (Hcard : exists nc, cardinal (A -> A -> Prop) (fun L => L = L1 \/ L = L2) nc /\ nc <= 2).
  { destruct (classic (L1 = L2)) as [Heq | Hne].
    - exists 1. split; [|lia].
      replace (fun L => L = L1 \/ L = L2)
        with (Add (A -> A -> Prop) (Empty_set _) L1).
      + apply card_add; [apply card_empty | intro Hb; destruct Hb].
      + apply Extensionality_Ensembles; split; intros L HL.
        * destruct HL as [L' HL'|L' HL']; [destruct HL' | apply Singleton_inv in HL'; left; symmetry; exact HL'].
        * destruct HL as [-> | ->]; [right; constructor | rewrite <- Heq; right; constructor].
    - exists 2. split; [|lia].
      replace (fun L => L = L1 \/ L = L2)
        with (Add (A -> A -> Prop) (Add (A -> A -> Prop) (Empty_set _) L1) L2).
      + apply card_add; [ apply card_add; [apply card_empty | intro Hb; destruct Hb]
                        | intro Hb; destruct Hb as [L' Hb|L' Hb]; [destruct Hb | apply Singleton_inv in Hb; apply Hne; symmetry; exact Hb] ].
      + apply Extensionality_Ensembles; split; intros L HL.
        * destruct HL as [-> | ->]; [left; right; constructor | right; constructor].
        * destruct HL as [L' [L'' HL''|L'' HL'']|L' HL'];
            [ destruct HL'' | apply Singleton_inv in HL''; left; symmetry; exact HL''
            | apply Singleton_inv in HL'; right; symmetry; exact HL' ]. }
  destruct Hcard as [nc [Hnc Hnc2]].
  pose proof (dimension_is_minimum Hdim (fun L => L = L1 \/ L = L2) nc HReal Hnc) as Hle. lia.
Qed.
```
NOTES: `Print IsLinearExtension. Print IsTotalOrder.` to confirm the nested `constructor` order (`linear_is_total :> IsTotalOrder` then `linear_extends`; `IsTotalOrder` = `IsPoset` fields refl/antisym/trans wrapped + `total_comparable`). If `IsTotalOrder` is `{ total_is_poset :> IsPoset ; total_comparable }` then the inner `constructor` builds `IsPoset L1` (3 fields) then totality — match it (the script above assumes refl/trans/antisym ordering of `IsPoset`; reorder to the real `PosetClasses.IsPoset` field order: `poset_refl`, `poset_antisym`, `poset_trans` — adjust the three bullets accordingly). `lt_eq_lt_dec : forall n m, {n<m}+{n=m}+{m<n}`. `dimension_is_minimum` args per `DimDefs` (`Arguments dimension_is_minimum {A R d} _ _ _ _ _`). The cardinal plumbing mirrors `DimTwoGeneric.dim2_record` exactly — copy its `Add`/`card_add`/`Singleton_inv` shape if a bullet mismatches.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 300 execution/DisjointChainsDim.vo 2` → EXIT=0; zero admits.
- [ ] **Commit** `git add execution/DisjointChainsDim.v && git commit -m "feat(execution): disjoint_chains_dim_le2 (generic, no width/finiteness)"`.

---

## Task DC2: frontier blocks are disjoint chains (`DisjointChainsDim.v`)
Append. This is the gap-closer; the crux is `hb_same_index_msg` via the rank.

Helpers to establish first (read `Rank.v` and `Schedule.v` for exact names/types):
- `desugar_rank_form : forall s pi, exists c, c <= 1 /\ desugar_rank s pi = 2 * snd pi + c` (Schedule.v).
- `hb_neq_rank_lt : forall (R:RankedProgram) a b, hb R a b -> a <> b -> rp_rank R (proj1_sig a) < rp_rank R (proj1_sig b)` (Rank.v). For `desugar s`, `rp_rank (desugar s) = desugar_rank s` and `rp_prog (desugar s) = desugar_prog s`; `ep_order (exec_of_schedule s) = hb (desugar s)` definitionally.
- `rp_rank_mono : forall (R:RankedProgram) a b, edge R a b -> rp_rank R (proj1_sig a) < rp_rank R (proj1_sig b)`.
- `clos_rt_rt1n : clos_refl_trans A Rel x y -> clos_refl_trans_1n A Rel x y` (Operators_Properties) — for left-decomposition `x = y \/ exists z, edge x z /\ hb z y`.

```coq
(* within one frontier, hb between two distinct events is a direct sender->receiver message *)
Lemma hb_same_index_msg :
  forall s, wf_schedule s ->
  forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) = snd (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y -> x <> y ->
    List.In (fst (proj1_sig x), fst (proj1_sig y))
            (nth (snd (proj1_sig x)) (sch_frontiers s) []).
Proof.
  (* 1. ranks: rank x = 2k+cx, rank y = 2k+cy, cx,cy<=1; hb_neq_rank_lt => rank x < rank y
        => cx=0, cy=1, rank y = rank x + 1.
     2. clos_rt_rt1n on the hb: x = y (excluded) or exists z, edge x z /\ hb z y.
        edge x z => rank x < rank z (rp_rank_mono); hb z y => rank z <= rank y = rank x + 1
        => rank z = rank x + 1 = rank y; with hb z y and rank z = rank y, the strict-along-edge
        structure forces z = y (else rank z < rank y). So x -> y is a single edge.
     3. a single edge with equal indices is a message (program edge raises index/rank by 2):
        edge (desugar s) x y, snd x = snd y => the message disjunct => op_at p k = Send q _,
        op_at q k = Recv p _ ; op_at_desugar + op_for_send_iff => In (p,q) (nth k …). *)
Admitted_REPLACE.
Qed.

(* component label: a receiver maps to its sender; senders/locals map to themselves *)
Definition fb_comp (s : Schedule) (pi : nat * nat) : nat :=
  match op_at (desugar_prog s) (fst pi) (snd pi) with
  | Some (Recv src _) => src
  | _ => fst pi
  end.

Lemma frontier_block_dim_le2 :
  forall s, wf_schedule s -> forall k d,
    PosetDimension (sub_order (exec_of_schedule s) (frontier_block s k)) d -> d <= 2.
Proof.
  intros s Hwf k d Hdim.
  apply (disjoint_chains_dim_le2
           (sub_order (exec_of_schedule s) (frontier_block s k))
           (fun z => fb_comp s (proj1_sig (proj1_sig z)))).
  - (* H1: sub_order z w -> fb_comp = fb_comp.  z,w in block => same index k;
       sub_order = hb on proj; if z=w trivial; else hb_same_index_msg => proj z sends to proj w
       => w is Recv from (fst proj z) => fb_comp w = fst proj z = fb_comp z (z is a sender). *)
    Admitted_REPLACE.
  - (* H2: same fb_comp -> comparable.  Case on whether each is a sender/local or receiver
       (op_for under wf): same comp => same matched pair or same event => hb via msg_step-style
       message edge or reflexivity. *)
    Admitted_REPLACE.
  - exact Hdim.
Qed.

Corollary fully_sync_frontier_dim_le2 :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
    IsFullySync (exec_of_schedule s) (frontier_blocks s) ->
    exists d, exec_has_dimension (exec_of_schedule s) d /\ d <= 2.
Proof.
  intros s Hwf Hnp Hfs.
  apply (fully_sync_dim_le2 (exec_of_schedule s) (frontier_blocks s) Hfs).
  intros blk Hblk.
  apply in_map_iff in Hblk. destruct Hblk as [k [Hbeq _]]. subst blk.
  (* dimension of the block exists (finite carrier) then bound by frontier_block_dim_le2 *)
  destruct (fin_dim_exists (sub_order (exec_of_schedule s) (frontier_block s k)) _) as [d [Hd]].
  (* Hfin for the block subtype: from the execution's finiteness restricted *)
  exists d. split; [exact (inhabits Hd) | exact (frontier_block_dim_le2 s Hwf k d Hd)].
Qed.
```
**The three `Admitted_REPLACE` are placeholders — REPLACE with real proofs (NO admit in the final file).** Detailed guidance:
- `hb_same_index_msg`: follow the 3-step comment. For step 2's "single edge," `clos_rt_rt1n` gives `clos_refl_trans_1n`; do `inversion`/`destruct` on it: the `rt1n_refl` case contradicts `x<>y`; the `rt1n_trans` case gives `z` with `edge x z` and `clos_refl_trans_1n … z y` (re-`clos_rt1n_rt` to `hb z y`). Use `rp_rank_mono`/`rank_hb_le` for the rank squeeze `rank z = rank y`, then `hb z y` with equal rank ⟹ `z = y` (by `hb_neq_rank_lt` contrapositive: if `z<>y` then `rank z < rank y`). Then `edge x y` same-index ⟹ message (the program disjunct `pa=pb /\ ib = S ia` contradicts `snd x = snd y` since `ib = S ia ≠ ia`). Extract the `Send`/`Recv` and convert via `op_at_desugar` (you'll need `x`'s/`y`'s validity for indices) + `op_for_send_iff`.
- `frontier_block_dim_le2` H1/H2: `z`,`w` are block elements (`In (frontier_block s k) (proj1_sig z)`, i.e. `snd (proj1_sig (proj1_sig z)) = k`). `sub_order … z w = ep_order … (proj1_sig z) (proj1_sig w)`. Use `hb_same_index_msg` for H1 and `op_for_send_iff`/`op_for_recv_iff` (ScheduleWf) for H2. Unfold `fb_comp` and case on `op_at … = Send/Recv/Local`. Under `wf_schedule`, a sender `p` with `(p,q)∈frontier k` has `op_at p k = Send q k` and `op_at q k = Recv p k`.
- `fully_sync_frontier_dim_le2`: `fin_dim_exists` needs the block subtype's finiteness `Finite {z | In (frontier_block s k) z} (Full_set _)`; obtain via `cardinal_subtype_full` from the execution carrier's finiteness restricted to the block, OR via the existing `sub_order` finiteness used in `FullySyncDim2.v` (read how `fully_sync_dim_le2`'s callers get block dimensions — e.g. `BarrierDim2Examples`/`FinFullySyncExamples` derive `inhabited (PosetDimension (sub_order …) d)`; mirror that). If `fin_dim_exists` is awkward here, use `subposet_dimension_le`/`dushnik_miller`-style existence already used for blocks elsewhere.

If `hb_same_index_msg` or the H1/H2 discharge proves too heavy, FALL BACK: keep `disjoint_chains_dim_le2` (DC1, the main mathematical deliverable) and prove `frontier_block_dim_le2` only for a CONCRETE schedule in DC3 (instantiating `disjoint_chains_dim_le2` directly on a specific block), recording the general frontier characterization as remaining work. Report which path you took.
- [ ] **Build** `bash .claude/scripts/timed-build.sh 360 execution/DisjointChainsDim.vo 2` → EXIT=0; zero admits.
- [ ] **Commit** `git add execution/DisjointChainsDim.v && git commit -m "feat(execution): frontier blocks are disjoint chains => dim <= 2 (closes finding 2)"`.

---

## Task DC3: example + wiring + audit
**Files:** `execution/DisjointChainsDimExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.
- [ ] **Step 1: example** — a width-3 frontier block (3 procs, no messages at the frontier ⟹ antichain of 3, width 3, dim 2) discharged by `frontier_block_dim_le2` (or, if DC2 fell back, by a direct `disjoint_chains_dim_le2` instantiation). Use schedule `{ nprocs := 3; frontiers := [[]] }` (all Local at index 0) and show the index-0 block has dim ≤ 2. Prove `wf_schedule` (empty frontier is trivially `wf_frontier`).
```coq
Definition s_anti3 : Schedule := {| sch_nprocs := 3; sch_frontiers := [ [] ] |}.
Lemma wf_s_anti3 : wf_schedule s_anti3.
  (* the only frontier is [] : wf_frontier n [] is (no pairs) /\ NoDup [] *)
Example anti3_block_dim_le2 :
  forall d, PosetDimension (sub_order (exec_of_schedule s_anti3) (frontier_block s_anti3 0)) d -> d <= 2.
Proof. apply (frontier_block_dim_le2 s_anti3 wf_s_anti3 0). Qed.
```
- [ ] **Step 2: build** `bash .claude/scripts/timed-build.sh 180 execution/DisjointChainsDimExamples.vo 2` → EXIT=0.
- [ ] **Step 3: export** append `DisjointChainsDim` to `execution/Execution.v`'s `Require Export` list.
- [ ] **Step 4: whole-project** `bash .claude/scripts/timed-build.sh 1800 @all 4` → EXIT=0.
- [ ] **Step 5: audit** scratch `execution/DCDimAudit.v` (`From Execution Require Import DisjointChainsDim. Print Assumptions disjoint_chains_dim_le2. Print Assumptions frontier_block_dim_le2.`), register, build, capture (expect standard axioms; `disjoint_chains_dim_le2` should be axiom-light — note if it pulls only `classic`/proof-irrelevance), then REMOVE + revert registration.
- [ ] **Step 6: INDEX** add a `#### execution/DisjointChainsDim.v` subsection: `disjoint_chains_dim_le2`, `hb_same_index_msg`, `fb_comp`, `frontier_block_dim_le2`, `fully_sync_frontier_dim_le2`; note "closes critical-review finding 2 (per-block dim ≤ 2 discharged for frontier blocks); finding 1 (IsFullySync/barrier for N>4) remains."
- [ ] **Step 7: commit** `git add execution/DisjointChainsDimExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): disjoint-chains example + export + INDEX (closes finding 2)"`.

---

## Self-Review (vs the spec)
- **Coverage:** generic lemma (DC1); frontier-block discharge via rank + comp (DC2); corollary + example + wiring (DC2/DC3). Mapped.
- **Reuse:** realizer/cardinal idiom from `dim2_record`; `desugar_rank_form`/`hb_neq_rank_lt`/`rp_rank_mono` (Rank/Schedule); `op_for_send_iff`/`op_for_recv_iff` (ScheduleWf); `fully_sync_dim_le2` (existing).
- **Name consistency:** `disjoint_chains_dim_le2`/`hb_same_index_msg`/`fb_comp`/`frontier_block_dim_le2`/`fully_sync_frontier_dim_le2` across DC1–DC3.
- **Honest scope:** closes finding 2 only; finding 1 explicitly still open. Fallback (concrete frontier block) recorded if the general H1/H2 overruns.
- **No placeholders in final code:** the three `Admitted_REPLACE` MUST be replaced; build steps assert zero admits.

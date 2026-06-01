# E_min `{b,c,d}` block exact dimension (#66) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development.

**Goal:** Close deferred #66 — prove the `{b,c,d}` block of `E_min` has dimension exactly 2, and assemble the `E_min` exact-dimension cross-check `dim E_min = max(1, max(dim Lmin, dim Umin)) = max(1,max(0,2)) = 2` via `fin_barrier_dimension_full` (cross-checking the existing `E_min_dim_2`). X4 took the cheap fallback (`bool` chain); this does the real thing.

**Architecture:** A small generic dim-2 toolkit (`execution/DimTwoGeneric.v`, generalizing the two `DimBridge` lemmas off `ExecPoset`), a bare 3-element poset proven dim-2, transported onto the `Umin` subtype by `dimension_iso`, and the barrier assembly — all test-driven in `execution/EminBlockDimExamples.v`.

**Tech Stack:** Rocq 9.1; Dimension theory (`PosetDimension`, `IsRealizer`, `IsLinearExtension`, `dimension_iso`, `dimension_is_minimum`, `fin_dim_exists`), `FinPosetDimSurgery` (`fin_sub_order`), `FinPosetDim` (`fin_is_barrier`), `FinExtremumDim` (`fin_barrier_dimension_full`, `fin_singleton_dim0`). Builds via the wrapper.

---

## Task EB1: generic dim-2 toolkit (`execution/DimTwoGeneric.v`)

Generalize `DimBridge.exec_dim_ge_2` and `exec_dim_eq_2_of_realizer` off `ExecPoset` to any poset (the proofs are already generic in disguise — only `ep_order E` needs to become an abstract `R`, and `exec_dimension_exists` becomes `fin_dim_exists`).

**Files:** Create `execution/DimTwoGeneric.v`; modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1: file**
```coq
(* Generic dim-2 toolkit: incomparable pair => dim >= 2, and a 2-linear-extension
   realizer => dim = 2. Off-ExecPoset generalization of DimBridge's two lemmas. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import FinPosetDimSurgery.

(* incomparable pair forces dimension >= 2 (no finiteness needed) *)
Lemma dim_ge_2_of_incomparable :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (x y : A),
    Incomparable R x y ->
    forall d, PosetDimension R d -> 2 <= d.
Proof.
  intros A R HR x y Hinc d Hdim.
  assert (Hne : x <> y).
  { intro Heq. apply Hinc. left. subst y. apply poset_refl. }
  destruct d as [| [| d']]; [ exfalso | exfalso | lia ].
  - pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    assert (Hre : dimension_realizer Hdim = Empty_set _)
      by (apply cardinalO_empty; exact Hcard).
    assert (Hempty : forall L, ~ In _ (dimension_realizer Hdim) L).
    { intros L HL. rewrite Hre in HL. destruct HL. }
    assert (HRxy : R x y).
    { apply (proj2 (realizer_intersection Hreal x y)).
      intros L HL. exfalso. exact (Hempty L HL). }
    apply Hinc. left. exact HRxy.
  - pose proof (dimension_is_realizer Hdim) as Hreal.
    pose proof (dimension_cardinality Hdim) as Hcard.
    destruct (cardinal_invert _ _ _ Hcard) as [A' [L [Heq [Hnin Hcard0]]]].
    assert (HA' : A' = Empty_set _) by (apply cardinalO_empty; exact Hcard0).
    subst A'.
    assert (HinL : In _ (dimension_realizer Hdim) L).
    { rewrite Heq. apply Add_intro2. }
    assert (Hmem : forall L', In _ (dimension_realizer Hdim) L' -> L' = L).
    { intros L' HL'. rewrite Heq in HL'.
      destruct HL' as [L' Hbad | L' Hsing].
      - destruct Hbad.
      - apply Singleton_inv in Hsing. symmetry. exact Hsing. }
    pose proof (realizer_linear Hreal L HinL) as HLlin.
    pose proof (linear_is_total HLlin) as HLtot.
    pose proof (total_comparable (IsTotalOrder := HLtot) x y) as Hcomp.
    assert (Hback : forall u v, L u v -> R u v).
    { intros u v Huv. apply (proj2 (realizer_intersection Hreal u v)).
      intros L' HL'. rewrite (Hmem L' HL'). exact Huv. }
    destruct Hcomp as [HLxy | HLyx].
    + apply Hinc. left. apply Hback. exact HLxy.
    + apply Hinc. right. apply Hback. exact HLyx.
Qed.

(* two distinct linear extensions whose intersection is R, on a finite poset,
   build a dimension-2 witness *)
Lemma dim_eq_2_of_realizer :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)),
    (exists L1 L2,
       IsLinearExtension R L1 /\ IsLinearExtension R L2 /\
       (forall x y, R x y <-> (L1 x y /\ L2 x y))) ->
    (exists x y, Incomparable R x y) ->
    PosetDimension R 2.
Proof.
  intros A R HR Hfin [L1 [L2 [Hlin1 [Hlin2 Hcap]]]] [x0 [y0 Hinc]].
  set (realizer := fun L : A -> A -> Prop => L = L1 \/ L = L2).
  assert (HrealizerIsRealizer : IsRealizer R realizer).
  { constructor.
    - intros L [-> | ->]; assumption.
    - intros x y. split.
      + intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HL1 HL2].
        intros L [-> | ->]; assumption.
      + intro Hall. apply (proj2 (Hcap x y)). split.
        * apply (Hall L1). left. reflexivity.
        * apply (Hall L2). right. reflexivity. }
  assert (HL12 : L1 <> L2).
  { intro HeqL.
    pose proof (linear_is_total Hlin1) as Htot1.
    pose proof (total_comparable (IsTotalOrder := Htot1) x0 y0) as Hc1.
    destruct Hc1 as [H1xy | H1yx].
    - apply Hinc. left. apply (proj2 (Hcap x0 y0)).
      split; [ exact H1xy | rewrite <- HeqL; exact H1xy ].
    - apply Hinc. right. apply (proj2 (Hcap y0 x0)).
      split; [ exact H1yx | rewrite <- HeqL; exact H1yx ]. }
  assert (Hreq : realizer = Add _ (Add _ (Empty_set _) L1) L2).
  { apply Extensionality_Ensembles. split.
    - intros L HL. destruct HL as [-> | ->].
      + left. right. constructor.
      + right. constructor.
    - intros L HL. destruct HL as [L HL | L HL].
      + destruct HL as [L HL | L HL].
        * destruct HL.
        * apply Singleton_inv in HL. left. symmetry. exact HL.
      + apply Singleton_inv in HL. right. symmetry. exact HL. }
  assert (Hcard2 : cardinal _ realizer 2).
  { rewrite Hreq. apply card_add.
    - apply card_add.
      + apply card_empty.
      + intro Hbad. destruct Hbad.
    - intro Hbad. destruct Hbad as [L Hbad | L Hbad].
      + destruct Hbad.
      + apply Singleton_inv in Hbad. apply HL12. exact Hbad. }
  destruct (fin_dim_exists R Hfin) as [d [Hd]].
  pose proof (dimension_is_minimum Hd realizer 2 HrealizerIsRealizer Hcard2) as Hle.
  pose proof (dim_ge_2_of_incomparable R x0 y0 Hinc d Hd) as Hge.
  assert (Hd2 : d = 2) by lia. subst d. exact Hd.
Qed.
```
NOTE: `fin_dim_exists` lives in `FinPosetDimSurgery` — confirm its exact statement with `About fin_dim_exists` (it should give `Finite A (Full_set A) -> exists d, inhabited (PosetDimension R d)`; if it returns the bare `PosetDimension` or a different shape, adapt the `destruct`). All other lemmas (`cardinalO_empty`, `cardinal_invert`, `realizer_*`, `total_comparable`, `dimension_*`) are exactly as used in `DimBridge.v` — mirror that file if a name/arg differs.

- [ ] **Step 2:** register `DimTwoGeneric` in `execution/dune` + `_CoqProject`.
- [ ] **Step 3: build** — `bash .claude/scripts/timed-build.sh 240 execution/DimTwoGeneric.vo 2`. EXIT=0.
- [ ] **Step 4: commit** — `git add -A && git commit -m "feat(execution): generic dim>=2 / dim=2-of-realizer toolkit"`.

---

## Task EB2: bare 3-element block + transport to Umin (`execution/EminBlockDimExamples.v`)

**Files:** Create `execution/EminBlockDimExamples.v`; modify `execution/dune`, `_CoqProject`.

The `{b,c,d}` block (events `b=(0,1)`, `c=(1,0)`, `d=(1,1)`; only `c<d`, `b` isolated) is order-isomorphic to the bare poset `T3` below. Prove `T3` dim-2 (everything computes on a 3-value inductive), then transport via `dimension_iso`.

- [ ] **Step 1: header + bare poset**
```coq
(* #66: the E_min {b,c,d} block has dimension exactly 2, and the E_min exact-dim
   cross-check via fin_barrier_dimension_full. Test-only. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset Schedule
                              FinPosetDimSurgery FinPosetDim FinExtremumDim
                              DimIso DimBridge DimTwoGeneric
                              DimExamples FrontierExamples.

(* bare 3-element poset: C3 < D3, B3 isolated *)
Inductive T3 : Set := B3 | C3 | D3.

Definition bcd_R (x y : T3) : Prop := x = y \/ (x = C3 /\ y = D3).

#[export] Instance bcd_poset : IsPoset T3 bcd_R.
Proof.
  constructor.
  - intro x. left. reflexivity.
  - intros x y [Hxy|[Hx Hy]] [Hyx|[Hy' Hx']]; subst; try reflexivity; try discriminate.
  - intros x y z [Hxy|[Hx Hy]] [Hyz|[Hy' Hz]]; subst; try (left; reflexivity);
      try (right; split; reflexivity); try discriminate.
Qed.

Lemma bcd_Hfin : Finite T3 (Full_set T3).
Proof.
  apply (cardinal_finite T3 (Full_set T3) 3).
  replace (Full_set T3)
    with (Add T3 (Add T3 (Add T3 (Empty_set T3) B3) C3) D3).
  - apply card_add; [apply card_add; [apply card_add; [apply card_empty | ] | ] | ];
      (let H := fresh in intro H;
       repeat (match goal with
               | [ H : In _ (Add _ _ _) _ |- _ ] => apply Add_inv in H; destruct H as [H|H]
               end); try (destruct H); try discriminate).
  - apply Extensionality_Ensembles; split; intros x _.
    + constructor.
    + destruct x; [ left;left;right;constructor | left;right;constructor | right;constructor ].
Qed.
```
NOTE: the `card_add` distinctness side-goals (`~ In D3 (Add (Add (Add ∅ B3) C3))`, etc.) require showing the new element differs from all prior — the `Add_inv`/`discriminate` chain handles it but may need tuning per how `Add_inv` nests; if it fights, prove each `~In` by `intro H; repeat (destruct H as [H|H]); [discriminate.. | inversion H]`. Mirror `chain2_Hfin` in `FinExtremumDimExamples.v` for the exact idiom.

- [ ] **Step 2: two linear extensions + dim 2 of the bare poset**
```coq
Definition kB (x : T3) : nat := match x with B3 => 0 | C3 => 1 | D3 => 2 end.
Definition kC (x : T3) : nat := match x with C3 => 0 | D3 => 1 | B3 => 2 end.
Definition M1 (x y : T3) : Prop := kB x <= kB y.
Definition M2 (x y : T3) : Prop := kC x <= kC y.

Lemma M1_linext : IsLinearExtension bcd_R M1.
Proof.
  constructor.
  - constructor.
    + constructor; unfold M1.
      * intro x; lia.
      * intros x y z; lia.
      * intros x y Hxy Hyx. destruct x, y; simpl in *; try reflexivity; lia.
    + intros x y. unfold M1. destruct x, y; simpl; (left + right); lia.
  - intros x y [Hxy|[Hx Hy]]; subst; unfold M1; simpl; lia.
Qed.

Lemma M2_linext : IsLinearExtension bcd_R M2.
Proof.
  constructor.
  - constructor.
    + constructor; unfold M2.
      * intro x; lia.
      * intros x y z; lia.
      * intros x y Hxy Hyx. destruct x, y; simpl in *; try reflexivity; lia.
    + intros x y. unfold M2. destruct x, y; simpl; (left + right); lia.
  - intros x y [Hxy|[Hx Hy]]; subst; unfold M2; simpl; lia.
Qed.

Lemma bcd_cap : forall x y, bcd_R x y <-> (M1 x y /\ M2 x y).
Proof.
  intros x y. unfold bcd_R, M1, M2. destruct x, y; simpl;
    split; intros; repeat split; try (left; reflexivity);
    try (right; split; reflexivity); try lia;
    repeat match goal with [H : _ /\ _ |- _] => destruct H end;
    try lia; try discriminate;
    repeat match goal with [H : _ \/ _ |- _] => destruct H end;
    try lia; try discriminate; try (exfalso; lia).
Qed.

Lemma bcd_incomp : Incomparable bcd_R B3 C3.
Proof.
  intros [H|[Hb Hc]]; [ destruct H as [H|[H _]]; discriminate | discriminate ].
Qed.

Lemma bcd_dim2 : PosetDimension bcd_R 2.
Proof.
  apply (dim_eq_2_of_realizer bcd_R bcd_Hfin).
  - exists M1, M2. split; [exact M1_linext| split; [exact M2_linext| exact bcd_cap]].
  - exists B3, C3. exact bcd_incomp.
Qed.
```
NOTE: the `IsTotalOrder`/`IsLinearExtension` field structure: confirm with `Print IsLinearExtension` / `Print IsTotalOrder` (from `DimDefs`). `IsLinearExtension R L := { linear_is_total :> IsTotalOrder L; linear_extends : forall x y, R x y -> L x y }`. `IsTotalOrder` likely bundles `IsPoset L` (refl/antisym/trans) + totality `forall x y, L x y \/ L y x`. Adjust the inner `constructor`s to match its exact fields (use `Print IsTotalOrder` first). The `bcd_cap` blast may need manual case work if the combined `split;intros;...` is too coarse — fall back to `destruct x, y; simpl; intuition (try lia; try discriminate)` or an explicit 9-case proof.

- [ ] **Step 3: transport to the Umin subtype**

`Umin := fun x : ep_carrier E_min => proj1_sig x <> (0,0)` (from `FrontierExamples`). The block poset is `fin_sub_order (ep_order E_min) Umin` on `{z : ep_carrier E_min | In Umin z}`. Build the iso `T3 -> {z | In Umin z}` sending `B3↦b, C3↦c, D3↦d` (events from `DimExamples`: `ev_b=(0,1)`, `ev_c=(1,0)`, `ev_d=(1,1)`), and transport `bcd_dim2` via `dimension_iso`.

```coq
(* membership proofs: ev_b, ev_c, ev_d are all <> (0,0) *)
Lemma inU_b : Ensembles.In _ Umin ev_b. Proof. unfold Umin, Ensembles.In, ev_b; simpl; discriminate. Qed.
Lemma inU_c : Ensembles.In _ Umin ev_c. Proof. unfold Umin, Ensembles.In, ev_c; simpl; discriminate. Qed.
Lemma inU_d : Ensembles.In _ Umin ev_d. Proof. unfold Umin, Ensembles.In, ev_d; simpl; discriminate. Qed.

Definition UU := {z : ep_carrier E_min | Ensembles.In _ Umin z}.
Definition f3 (t : T3) : UU :=
  match t with
  | B3 => exist _ ev_b inU_b
  | C3 => exist _ ev_c inU_c
  | D3 => exist _ ev_d inU_d
  end.
Definition g3 (u : UU) : T3 :=
  match proj1_sig (proj1_sig u) with
  | (0,1) => B3 | (1,0) => C3 | _ => D3
  end.

Lemma g3_f3 : forall t, g3 (f3 t) = t.
Proof. intro t; destruct t; vm_compute; reflexivity. Qed.

Lemma f3_g3 : forall u, f3 (g3 u) = u.
Proof.
  intros [z Hz]. unfold g3, f3. simpl.
  (* z is one of ev_b/ev_c/ev_d; use valid_event_min_cases + that z <> (0,0) *)
  pose proof (valid_event_min_cases z) as Hc. simpl in Hc.
  destruct Hc as [H0|[Hb|[Hc|Hd]]].
  - exfalso. unfold Umin, Ensembles.In in Hz. rewrite H0 in Hz. exact (Hz eq_refl).
  - rewrite (eq_ev_b z Hb). rewrite Hb. apply f_equal. (* subtype eq via proof irrelevance *)
    f_equal. apply proof_irrelevance.
  - rewrite (eq_ev_c z Hc). rewrite Hc. f_equal. apply proof_irrelevance.
  - rewrite (eq_ev_d z Hd). rewrite Hd. f_equal. apply proof_irrelevance.
Qed.

Lemma f3_iso : forall t t', bcd_R t t' <-> fin_sub_order (ep_order E_min) Umin (f3 t) (f3 t').
Proof.
  intros t t'. unfold fin_sub_order. destruct t, t'; simpl; split; intro H.
  (* 9 cases. Forward: bcd_R gives reflexive or C3->D3 (=> ep_order ev_c ev_d = hb_c_d).
     Backward: use the existing E_min order facts. Reuse: poset_refl, hb_c_d (c<d),
     incomp_b_c, and hb_min_realizer to refute non-edges. *)
Admitted.  (* REPLACE: see note *)

Lemma dim_block_bcd_2 : PosetDimension (fin_sub_order (ep_order E_min) Umin) 2.
Proof.
  apply (dimension_iso T3 UU bcd_R (fin_sub_order (ep_order E_min) Umin) f3 g3
           g3_f3 f3_g3 f3_iso 2 bcd_dim2).
Qed.
```
**CRITICAL — `f3_iso` must be PROVED, not `Admitted` (the `Admitted` above is a placeholder to delete).** Prove the 9 cases. The order facts you need are all available:
- reflexive cases (t=t'): `bcd_R t t` holds (`left`); `fin_sub_order … (f3 t)(f3 t)` is `ep_order E_min ev_? ev_?` = `poset_refl`.
- `C3,D3`: `bcd_R C3 D3` holds; RHS is `ep_order E_min ev_c ev_d` = `hb_c_d` (from `DimExamples`).
- all other off-diagonal pairs: `bcd_R` is FALSE (`discriminate` the disjunction), so forward is vacuous; backward must REFUTE `ep_order E_min ev_? ev_?`. Refutations: `b` vs `c` both ways via `incomp_b_c`; the remaining non-edges (`b`↔`d`, `d`→`c`, `d`→`b`, `c`→`b`) via `hb_min_realizer` (rewrite into the key inequalities and `vm_compute`/`lia`), exactly as `incomp_b_c` is proved in `DimExamples.v`. If a needed refutation lemma (e.g. `incomp_b_d`) is not already in `DimExamples`, prove it inline with the `hb_min_realizer` + `vm_compute` pattern.

- [ ] **Step 4:** register `EminBlockDimExamples` in `dune` + `_CoqProject`.
- [ ] **Step 5: build** — `bash .claude/scripts/timed-build.sh 360 execution/EminBlockDimExamples.vo 2`. EXIT=0; `grep -nE "Admitted|admit|Axiom" execution/EminBlockDimExamples.v` MUST be empty (delete the placeholder `Admitted`).
- [ ] **Step 6: commit** — `git add -A && git commit -m "feat(execution): E_min {b,c,d} block has dimension exactly 2 (via bare poset + dimension_iso)"`.

---

## Task EB3: barrier assembly + wiring + audit

**Files:** modify `execution/EminBlockDimExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.

- [ ] **Step 1: dim Lmin = 0 + the cross-check**
```coq
(* Lmin = {a} singleton -> dim 0 *)
Lemma dim_block_a_0 : PosetDimension (fin_sub_order (ep_order E_min) Lmin) 0.
Proof.
  apply (fin_singleton_dim0 (fin_sub_order (ep_order E_min) Lmin)).
  intros [x Hx] [y Hy].
  (* Lmin x means proj1_sig x = (0,0); so x = y = ev_a, equal up to proof irrelevance *)
  unfold Lmin, Ensembles.In in Hx, Hy.
  assert (Hxy : x = y).
  { rewrite (eq_ev_a x Hx). rewrite (eq_ev_a y Hy). reflexivity. }
  subst y. f_equal. apply proof_irrelevance.
Qed.

(* E_min finiteness *)
Lemma E_min_Hfin : Finite (ep_carrier E_min) (Full_set (ep_carrier E_min)).
Proof. (* from the ExecPoset / hb_IsFinitePoset instance; see note *) Admitted. (* REPLACE *)

(* E_min_barrier : IsBarrier E_min Lmin Umin has the SAME shape as
   fin_is_barrier (ep_order E_min) Lmin Umin -- reuse it. *)
Example E_min_exact_dim_via_barrier :
  exists dW, inhabited (PosetDimension (ep_order E_min) dW) /\ dW = 2.
Proof.
  destruct E_min_dim_2 as [HdW].
  pose proof (fin_barrier_dimension_full (ep_order E_min) E_min_Hfin Lmin Umin
                E_min_barrier 0 2 2 dim_block_a_0 dim_block_bcd_2 HdW) as Heq.
  exists 2. split; [ exact (inhabits HdW) | reflexivity ].
Qed.
```
NOTES:
- `fin_singleton_dim0`'s signature (from `FinExtremumDim`, a sectioned lemma): `About fin_singleton_dim0` to get its explicit args (it takes the poset's `R` then the `forall x y, x = y` proof — see how `chain2_exact_dim` calls `@fin_singleton_dim0` in `FinExtremumDimExamples.v`). Match that calling convention.
- `E_min_Hfin`: every `ExecPoset` carrier is finite. Find the lemma — try `About hb_IsFinitePoset` / `Search Finite ep_carrier` / look at how `FinFullySyncExamples.v` or `BarrierDim2Examples.v` obtain finiteness for `E_min` (e.g. `ep_size_ok`, or `fp_finite (hb_IsFinitePoset …)`). Replace the `Admitted` with the real witness. If genuinely unavailable, build it from `valid_event_min_cases` (the 4 events `ev_a..ev_d`) like `chain2_Hfin` (cardinal 4). DO NOT leave it `Admitted`.
- `E_min_barrier` may need a `change`/`unfold` to retype `IsBarrier E_min Lmin Umin` as `fin_is_barrier (ep_order E_min) Lmin Umin` if they are not definitionally interchangeable; both are: cover ∧ disjoint ∧ (∃L) ∧ (∃U) ∧ (L≤U in ep_order). If `exact E_min_barrier` fails where `fin_is_barrier …` is expected, insert `unfold fin_is_barrier; unfold IsBarrier in E_min_barrier; exact E_min_barrier` or a `change`.
- `fin_barrier_dimension_full` arg order (from its statement): `R`, `{HR}`, `Hfin`, `L`, `U`, `(barrier : fin_is_barrier R L U)`, `dL`, `dU`, `dW`, `(HdL)`, `(HdU)`, `(HdW)` → `dW = max 1 (max dL dU)`. Here `max 1 (max 0 2) = 2`, so `Heq : 2 = 2` (or it rewrites `dW`); the `exists 2` is justified because `HdW : PosetDimension … 2` already. (We supply `dW := 2`; if `E_min_dim_2` gives some abstract `d`, instead `exists d` and use `Heq : d = 2` to `subst`.)

- [ ] **Step 2: build** — `bash .claude/scripts/timed-build.sh 360 execution/EminBlockDimExamples.vo 2`. EXIT=0; zero admits.
- [ ] **Step 3: export** — append `DimTwoGeneric` to `execution/Execution.v`'s `Require Export` list (NOT the examples).
- [ ] **Step 4: whole-project build** — `bash .claude/scripts/timed-build.sh 1800 @all 4`. EXIT=0.
- [ ] **Step 5: audit** — scratch `execution/EminBlockAudit.v` (`From Execution Require Import EminBlockDimExamples. Print Assumptions dim_block_bcd_2. Print Assumptions E_min_exact_dim_via_barrier.`), build via wrapper, capture (expected: the standard classical/proof-irrelevance axioms already pervasive in the dimension examples — `classic`, `proof_irrelevance`, `constructive_definite_description`, `Extensionality_Ensembles`; NOT any `admit`/`False`), then REMOVE it and revert its `dune`/`_CoqProject` registration.
- [ ] **Step 6: INDEX** — add `dim_block_bcd_2`, `E_min_exact_dim_via_barrier`, and the `DimTwoGeneric` lemmas to `docs/INDEX.md` (extend the exact-barrier-dimension subsection); note #66 is closed.
- [ ] **Step 7: commit** — `git add execution/EminBlockDimExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): E_min exact-dim cross-check via barrier (closes #66)"`.

---

## Self-Review (checked against the exact-barrier-dim spec, Component 3)

- **Spec coverage:** `dim (Umin block) = 2` → EB2 (`dim_block_bcd_2`); `dim (Lmin) = 0` → EB3 (`dim_block_a_0`); `fin_barrier_dimension_full` assembly giving `dim E_min = max(1,max(0,2)) = 2` cross-checking `E_min_dim_2` → EB3 (`E_min_exact_dim_via_barrier`). Generic toolkit (EB1) is the reusable substrate.
- **No `Admitted` in deliverables:** the two `Admitted` in the plan (`f3_iso`, `E_min_Hfin`) are explicit placeholders the implementer MUST replace; EB2/EB3 build steps assert `grep` finds none.
- **Name consistency:** `bcd_R`/`M1`/`M2`/`bcd_dim2`/`f3`/`g3`/`dim_block_bcd_2`/`dim_block_a_0`/`E_min_exact_dim_via_barrier`; reuses `dimension_iso`, `fin_barrier_dimension_full`, `fin_singleton_dim0`, `E_min_barrier`, `Lmin`/`Umin`, `ev_b`/`ev_c`/`ev_d`/`eq_ev_*`/`hb_c_d`/`incomp_b_c`/`hb_min_realizer`/`valid_event_min_cases` verbatim from existing files.
- **Reuse over re-proof:** EB1 generalizes `DimBridge`'s proven lemmas rather than re-deriving; EB2 reuses existing E_min order facts via `dimension_iso` instead of re-bashing the subtype realizer.

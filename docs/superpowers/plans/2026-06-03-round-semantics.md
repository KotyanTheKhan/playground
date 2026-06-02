# Barrier-round operational semantics + local clock Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** An operational, primitive-state barrier-round model (`RSys`, programs per process) whose happened-before `rhb` is characterized by a schedule-free local clock `rclock` — closing the W-2 gap, reusing the generic `stamp_iff`.

**Architecture:** One new leaf file `execution/RoundSem.v`: round system + well-formedness, `rhb` (barrier order) + its `IsPoset`, the `rlay`/`rcomp`/`rstep` fields with structural lemmas (the `stamp_iff` hypotheses, read straight off `rwf`), then `rhb_iff_stamp` by instantiating `stamp_iff` and `rhb_iff_rclock` via the schedule-free `rclock`. Plus a test-only examples file.

**Tech Stack:** Coq/Rocq 9.1, Stdlib `List`/`Arith`/`Lia`/`ProofIrrelevance`, the `Execution` library (`Op`, `OnlineClock`, `OnlineClockLocal`), `Posets.PosetClasses`. All builds via `bash .claude/scripts/timed-build.sh <secs> <target> 2`.

**Spec:** `docs/superpowers/specs/2026-06-03-round-semantics-design.md`.
**Branch:** `async-sem` (already checked out; the work pivoted to barrier-round).

**Key reused facts:**
- `Op` (execution/Op.v): `Local | Send (tgt:nat) (tag:nat) | Recv (src:nat) (tag:nat)`.
- `IsPoset` (Posets/PosetClasses.v): constructor takes refl/antisym/trans; projections `poset_refl`/`poset_antisym`/`poset_trans`.
- `local_stamp N p i o = let comp := match o with Recv src _ => src | _ => p end in let step := match o with Recv _ _ => 1 | _ => 0 end in ((i,comp,step),(i,(N-1)-comp,step))` (execution/OnlineClock.v).
- `le_prod B lx cx sx ly cy sy := le_lex3 lx cx sx ly cy sy /\ le_lex3 lx (B-cx) sx ly (B-cy) sy` (OnlineClock.v).
- `stamp_iff {A} (R) {HR:IsPoset A R} (lay comp step : A->nat) (B) : (barrier)->(resp-lay)->(resp-comp)->(rank)->(bound)-> forall x y, R x y <-> le_prod B (lay x)(comp x)(step x)(lay y)(comp y)(step y)` (OnlineClock.v).
- `stamp_le st1 st2 := let '((a1,a2,a3),(b1,b2,b3)):=st1 in let '((c1,c2,c3),(d1,d2,d3)):=st2 in le_lex3 a1 a2 a3 c1 c2 c3 /\ le_lex3 b1 b2 b3 d1 d2 d3` (execution/OnlineClockLocal.v).

---

### Task 1: round system, `rhb`, and `rhb_IsPoset`

**Files:**
- Create: `execution/RoundSem.v`
- Modify: `execution/dune` (add `RoundSem` to `(modules …)` after `OnlineClockLocalExamples`)
- Modify: `_CoqProject` (add `execution/RoundSem.v` after `execution/OnlineClockLocalExamples.v`)

- [ ] **Step 1: Create `execution/RoundSem.v` with the model + poset**

```coq
(* Barrier-round operational semantics with primitive per-process programs.
   The happened-before rhb is a barrier order; the clock (Task 3) is computed from
   nth r (prog p) -- p's own program -- with no Schedule projection (closes W-2). *)
From Stdlib Require Import List Arith Lia ProofIrrelevance.
From Posets Require Import PosetClasses.
From Execution Require Import Op OnlineClock OnlineClockLocal.
Import ListNotations.

Record RSys := { rs_nprocs : nat ; rs_nrounds : nat ; rs_prog : nat -> list Op }.

Definition rop (S : RSys) (p r : nat) : Op := nth r (rs_prog S p) Local.

Definition rvalid (S : RSys) (e : nat * nat) : Prop :=
  fst e < rs_nprocs S /\ snd e < rs_nrounds S.

Definition rwf (S : RSys) : Prop :=
  (forall p, p < rs_nprocs S -> length (rs_prog S p) = rs_nrounds S) /\
  (forall p r d t, p < rs_nprocs S -> r < rs_nrounds S -> rop S p r = Send d t ->
      d < rs_nprocs S /\ rop S d r = Recv p t) /\
  (forall p r s t, p < rs_nprocs S -> r < rs_nrounds S -> rop S p r = Recv s t ->
      s < rs_nprocs S /\ rop S s r = Send p t).

(* realized rendezvous edge: p sends to d AND d receives from p, in round r *)
Definition redge (S : RSys) (p d r : nat) : Prop :=
  (exists t, rop S p r = Send d t) /\ (exists t, rop S d r = Recv p t).

Definition rhb_same (S : RSys) (e e' : nat * nat) : Prop :=
  e = e' \/ (snd e = snd e' /\ redge S (fst e) (fst e') (snd e)).

Definition rhb (S : RSys) (e e' : nat * nat) : Prop :=
  snd e < snd e' \/ (snd e = snd e' /\ rhb_same S e e').

Definition REvent (S : RSys) : Type := { e : nat * nat | rvalid S e }.
Definition rhb_sub (S : RSys) (x y : REvent S) : Prop := rhb S (proj1_sig x) (proj1_sig y).

#[export] Instance rhb_IsPoset : forall S, IsPoset (REvent S) (rhb_sub S).
Proof.
  intro S. constructor.
  - (* refl *) intro x. unfold rhb_sub, rhb. right. split; [reflexivity | left; reflexivity].
  - (* antisym *) intros x y Hxy Hyx.
    assert (Hpe : proj1_sig x = proj1_sig y).
    { unfold rhb_sub, rhb in Hxy, Hyx.
      destruct Hxy as [Hlt1 | [He1 Hs1]]; destruct Hyx as [Hlt2 | [He2 Hs2]]; try lia.
      destruct Hs1 as [Hxy0 | [_ Hed1]]; [exact Hxy0|].
      destruct Hs2 as [Hyx0 | [_ Hed2]]; [symmetry; exact Hyx0|].
      exfalso. destruct Hed1 as [[t1 Hsend1] _]. destruct Hed2 as [_ [t2 Hrecv2]].
      rewrite <- He1 in Hrecv2. rewrite Hsend1 in Hrecv2. discriminate. }
    destruct x as [ex Hx]; destruct y as [ey Hy]; simpl in Hpe; subst ey.
    f_equal. apply proof_irrelevance.
  - (* trans *) intros x y z Hxy Hyz. unfold rhb_sub, rhb in *.
    destruct Hxy as [Hlt1 | [He1 Hs1]]; destruct Hyz as [Hlt2 | [He2 Hs2]];
      try (left; lia).
    right. split; [lia|].
    destruct Hs1 as [Hxy0 | [Hr1 Hed1]].
    + rewrite Hxy0. exact Hs2.
    + destruct Hs2 as [Hyz0 | [Hr2 Hed2]].
      * rewrite <- Hyz0. right. split; [exact Hr1 | exact Hed1].
      * exfalso. destruct Hed1 as [_ [t1 Hrecv1]]. destruct Hed2 as [[t2 Hsend2] _].
        rewrite He1 in Hrecv1. rewrite Hsend2 in Hrecv1. discriminate.
Qed.
```

- [ ] **Step 2: Register the module**

`execution/dune`: add `  RoundSem` after `  OnlineClockLocalExamples` inside `(modules …)`.
`_CoqProject`: add `execution/RoundSem.v` after `execution/OnlineClockLocalExamples.v`.

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/RoundSem.vo 2`
Expected: exit 0, `✅ Build successful`.

Likely fixes: if `IsPoset`'s constructor needs a different bullet count/order, read `posets/PosetClasses.v` and match (refl/antisym/trans). If `rewrite Hsend1 in Hrecv2` fails on a tag mismatch, `injection`/`discriminate` after aligning the round index with `He1`. Do NOT change definitions.

- [ ] **Step 4: Commit**

```bash
git add execution/RoundSem.v execution/dune _CoqProject
git commit -m "feat(round-sem): RSys/rwf, rhb barrier order, rhb_IsPoset (unconditional)"
```

---

### Task 2: clock fields + structural lemmas (the `stamp_iff` hypotheses)

**Files:**
- Modify: `execution/RoundSem.v` (append)

- [ ] **Step 1: Append fields and op-characterization helpers**

```coq
Definition rlay  (S : RSys) (x : REvent S) : nat := snd (proj1_sig x).
Definition rcomp (S : RSys) (x : REvent S) : nat :=
  match rop S (fst (proj1_sig x)) (snd (proj1_sig x)) with Recv s _ => s | _ => fst (proj1_sig x) end.
Definition rstep (S : RSys) (x : REvent S) : nat :=
  match rop S (fst (proj1_sig x)) (snd (proj1_sig x)) with Recv _ _ => 1 | _ => 0 end.

(* event pid in range *)
Lemma revent_fst_lt : forall S (x : REvent S), fst (proj1_sig x) < rs_nprocs S.
Proof. intros S x. exact (proj1 (proj2_sig x)). Qed.
Lemma revent_snd_lt : forall S (x : REvent S), snd (proj1_sig x) < rs_nrounds S.
Proof. intros S x. exact (proj2 (proj2_sig x)). Qed.
```

- [ ] **Step 2: Append the five structural lemmas**

```coq
(* hyp 1: barrier *)
Lemma rhb_barrier : forall S (x y : REvent S), rlay S x < rlay S y -> rhb_sub S x y.
Proof. intros S x y H. unfold rhb_sub, rhb, rlay in *. left. exact H. Qed.

(* hyp 2: resp-lay *)
Lemma rhb_resp_lay : forall S (x y : REvent S), rhb_sub S x y -> rlay S x <= rlay S y.
Proof. intros S x y [Hlt | [He _]]; unfold rlay; lia. Qed.

(* hyp 5: bound -- rcomp is a valid pid *)
Lemma rcomp_lt_nprocs :
  forall S, rwf S -> forall x : REvent S, rcomp S x < rs_nprocs S.
Proof.
  intros S Hwf x. unfold rcomp.
  destruct (rop S (fst (proj1_sig x)) (snd (proj1_sig x))) as [|d t|s t] eqn:E.
  - apply revent_fst_lt.                              (* Local *)
  - apply revent_fst_lt.                              (* Send  *)
  - (* Recv s t : s < nprocs by rwf clause 3 *)
    destruct Hwf as [_ [_ Hrecv]].
    apply (Hrecv (fst (proj1_sig x)) (snd (proj1_sig x)) s t
                 (revent_fst_lt S x) (revent_snd_lt S x) E).
Qed.

(* hyp 3: resp-comp -- within a round an edge forces equal comp (the sender) *)
Lemma rcomp_eq_of_rhb :
  forall S (x y : REvent S), rhb_sub S x y -> rlay S x = rlay S y -> rcomp S x = rcomp S y.
(* Proof outline: unfold rhb_sub/rhb; rlay-equal kills the snd< disjunct, leaving rhb_same.
   Case x=y: trivial. Case redge (fst x)(fst y)(snd x): the edge gives
   rop (fst x)(snd x) = Send (fst y) _  and  rop (fst y)(snd x) = Recv (fst x) _.
   So rcomp x = fst x (Send branch) and rcomp y = fst x (Recv-source branch, after
   rewriting snd y = snd x). Both equal fst x. unfold rcomp; rewrite the two rop eqns;
   reflexivity. *)

(* within a round, same comp => the two events are rhb-comparable (a chain) -- analogue of
   hb_or_of_fb_comp_eq, but read straight off rwf. *)
Lemma rhb_comparable_of_comp :
  forall S, rwf S -> forall x y : REvent S,
    rlay S x = rlay S y -> rcomp S x = rcomp S y ->
    rhb_sub S x y \/ rhb_sub S y x.
(* Proof outline: let r := snd(proj1 x)=snd(proj1 y), c := rcomp x = rcomp y.
   Case-split rop(fst x, r) and rop(fst y, r) into Local/Send/Recv (9 cases).
   Using rcomp definitions and rwf:
   - both non-Recv => fst x = c = fst y => x = y (proof_irrelevance) => rhb refl.
   - x non-Recv (so fst x = c), y = Recv c => rwf clause: rop(c,r)=Send(fst y) => redge c->fst y
       => rhb_sub x y (right disjunct).
   - x = Recv c, y non-Recv (fst y = c) => symmetric => rhb_sub y x.
   - both Recv c => rwf clause 3 gives rop(c,r)=Send(fst x) and =Send(fst y) => fst x=fst y => x=y.
   Mirror the structure of hb_or_of_fb_comp_eq in DisjointChainsDim.v. *)

(* hyp 4: rank -- within a round, same comp: rhb <-> rstep <= rstep *)
Lemma rhb_rank :
  forall S, rwf S -> forall x y : REvent S,
    rlay S x = rlay S y -> rcomp S x = rcomp S y ->
    (rhb_sub S x y <-> rstep S x <= rstep S y).
(* Proof outline (mirror blo_rank):
   (->) rhb x y, same round => rhb_same: x=y (steps equal) or redge fst x->fst y, where
        x is the sender (rstep 0) and y the receiver (rstep 1): 0<=1.
   (<-) rstep x <= rstep y: get comparability from rhb_comparable_of_comp.
        If rhb x y: done. If rhb y x (and x<>y): then by the (->) direction on y,x we'd get
        rstep y <= rstep x; combined with rstep x <= rstep y and x<>y (distinct steps 0/1)
        gives a contradiction unless equal; conclude rhb x y. Use rstep characterization:
        rstep = 1 iff the op is Recv. *)
```

Implementer notes: `rcomp_eq_of_rhb`, `rhb_comparable_of_comp`, `rhb_rank` are the
three substantive proofs — they mirror `fb_comp_eq_of_hb` / `hb_or_of_fb_comp_eq` /
`blo_rank` in `execution/DisjointChainsDim.v` and `execution/OnlineClockLocal.v`,
but are SHORTER (matching is read directly from `rwf`, no `desugar`/rank/`op_for`).
Read those analogues. Replace each outline with a real proof; do NOT leave `admit`.
Keep the lemma STATEMENTS exactly as given.

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 300 execution/RoundSem.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/RoundSem.v
git commit -m "feat(round-sem): rlay/rcomp/rstep + structural lemmas (stamp_iff hypotheses)"
```

---

### Task 3: `rhb_iff_stamp`, `rclock`, `rhb_iff_rclock`

**Files:**
- Modify: `execution/RoundSem.v` (append) and `execution/Execution.v` (export)

- [ ] **Step 1: Append the characterization + the schedule-free clock**

```coq
(* instantiate the generic dim-2 rule on the round model *)
Theorem rhb_iff_stamp :
  forall S, rwf S -> 0 < rs_nprocs S -> forall x y : REvent S,
    rhb_sub S x y <->
    le_prod (rs_nprocs S - 1)
      (rlay S x)(rcomp S x)(rstep S x)(rlay S y)(rcomp S y)(rstep S y).
Proof.
  intros S Hwf Hnp x y.
  apply (stamp_iff (rhb_sub S) (rlay S) (rcomp S) (rstep S) (rs_nprocs S - 1)).
  - intros a b H. exact (rhb_barrier S a b H).
  - intros a b H. exact (rhb_resp_lay S a b H).
  - intros a b H He. exact (rcomp_eq_of_rhb S a b H He).
  - intros a b He Hc. exact (rhb_rank S Hwf a b He Hc).
  - intro e. pose proof (rcomp_lt_nprocs S Hwf e). lia.
Qed.

(* the clock from PRIMITIVE local state: process p's own program at its counter r *)
Definition rclock (S : RSys) (p r : nat) : (nat*nat*nat) * (nat*nat*nat) :=
  local_stamp (rs_nprocs S) p r (rop S p r).

(* rclock's coordinates are exactly (rlay, rcomp, rstep) of the event *)
Lemma rclock_is_stamp :
  forall S (x : REvent S),
    rclock S (fst (proj1_sig x)) (snd (proj1_sig x))
    = ((rlay S x, rcomp S x, rstep S x),
       (rlay S x, (rs_nprocs S - 1) - rcomp S x, rstep S x)).
Proof.
  intros S x. unfold rclock, local_stamp, rlay, rcomp, rstep.
  destruct (rop S (fst (proj1_sig x)) (snd (proj1_sig x))); reflexivity.
Qed.

(* headline: causality via the schedule-free local clock *)
Theorem rhb_iff_rclock :
  forall S, rwf S -> 0 < rs_nprocs S -> forall x y : REvent S,
    rhb_sub S x y <->
    stamp_le (rclock S (fst (proj1_sig x)) (snd (proj1_sig x)))
             (rclock S (fst (proj1_sig y)) (snd (proj1_sig y))).
Proof.
  intros S Hwf Hnp x y.
  rewrite (rclock_is_stamp S x), (rclock_is_stamp S y).
  unfold stamp_le.
  exact (rhb_iff_stamp S Hwf Hnp x y).
Qed.
```

Likely fixes:
- `rhb_iff_rclock`: after `rewrite` + `unfold stamp_le`, the goal should be exactly the
  `le_prod` of `rhb_iff_stamp` (since `le_prod B lx cx sx … = le_lex3 lx cx sx … /\
  le_lex3 lx (B-cx) sx …` and `stamp_le` of the two triples is the same conjunction).
  If `exact` fails on a fold/`cbn` mismatch, insert `unfold le_prod` and/or `cbn` then
  `exact (rhb_iff_stamp …)`, or `split; apply (rhb_iff_stamp S Hwf Hnp x y)`.
- If `stamp_iff` cannot find the `IsPoset` instance, pass it: `apply (stamp_iff (rhb_sub S) (HR := rhb_IsPoset S) …)`.

- [ ] **Step 2: Build**

Run: `bash .claude/scripts/timed-build.sh 300 execution/RoundSem.vo 2`
Expected: exit 0.

- [ ] **Step 3: Print Assumptions check (no admits)**

Append temporarily, build, read output, then remove:
```coq
Print Assumptions rhb_iff_rclock.
```
Run: `bash .claude/scripts/timed-build.sh 300 execution/RoundSem.vo 2`
Expected: only standard axioms (`classic`, `proof_irrelevance`,
`constructive_definite_description`, `Extensionality_Ensembles`) — NO `admit`/`Admitted`.
Remove the line and rebuild green.

- [ ] **Step 4: Export from `execution/Execution.v`**

Append ` RoundSem` to the end of the `From Execution Require Export … OnlineClockLocal.` line, making it end `… OnlineClock OnlineClockLocal RoundSem.`

- [ ] **Step 5: Build the public surface**

Run: `bash .claude/scripts/timed-build.sh 300 execution/Execution.vo 2`
Expected: exit 0.

- [ ] **Step 6: Commit**

```bash
git add execution/RoundSem.v execution/Execution.v
git commit -m "feat(round-sem): rhb_iff_stamp + rclock + rhb_iff_rclock (schedule-free clock; W-2 closed) + export"
```

---

### Task 4: examples `RoundSemExamples.v`

**Files:**
- Create: `execution/RoundSemExamples.v`
- Modify: `execution/dune` (add `RoundSemExamples`), `_CoqProject` (add the file)

- [ ] **Step 1: Create the examples file**

```coq
(* Barrier-round model: worked instance (test-only). *)
From Stdlib Require Import List Arith Lia.
From Posets Require Import PosetClasses.
From Execution Require Import Op OnlineClock OnlineClockLocal RoundSem.
Import ListNotations.

(* 3 processes, 1 round: proc0 -> proc1 (msg), proc2 idle *)
Definition Sdemo : RSys :=
  {| rs_nprocs := 3 ; rs_nrounds := 1 ;
     rs_prog := fun p => match p with
                         | 0 => [Send 1 0]
                         | 1 => [Recv 0 0]
                         | _ => [Local]
                         end |}.

Lemma wf_Sdemo : rwf Sdemo.
Proof.
  unfold rwf, Sdemo, rop. simpl. repeat split.
  - intros p Hp. destruct p as [|[|[|p']]]; simpl; lia.
  - intros p r d t Hp Hr Hsend.
    destruct p as [|[|[|p']]]; destruct r as [|r']; simpl in *; try discriminate;
      try lia; injection Hsend as <- <-; split; [lia | reflexivity].
  - intros p r s t Hp Hr Hrecv.
    destruct p as [|[|[|p']]]; destruct r as [|r']; simpl in *; try discriminate;
      try lia; injection Hrecv as <- <-; split; [lia | reflexivity].
Qed.

(* the three events as REvents *)
Lemma v0 : rvalid Sdemo (0,0). Proof. unfold rvalid, Sdemo; simpl; lia. Qed.
Lemma v1 : rvalid Sdemo (1,0). Proof. unfold rvalid, Sdemo; simpl; lia. Qed.
Lemma v2 : rvalid Sdemo (2,0). Proof. unfold rvalid, Sdemo; simpl; lia. Qed.
Definition x0 : REvent Sdemo := exist _ (0,0) v0.
Definition x1 : REvent Sdemo := exist _ (1,0) v1.
Definition x2 : REvent Sdemo := exist _ (2,0) v2.

(* the schedule-free clock literals (N=3 => B=2) *)
Example rclock_x0 : rclock Sdemo 0 0 = ((0,0,0),(0,2,0)). Proof. vm_compute. reflexivity. Qed.
Example rclock_x1 : rclock Sdemo 1 0 = ((0,0,1),(0,2,1)). Proof. vm_compute. reflexivity. Qed.
Example rclock_x2 : rclock Sdemo 2 0 = ((0,2,0),(0,0,0)). Proof. vm_compute. reflexivity. Qed.

(* the sender->receiver pair is rhb-ordered *)
Example rhb_x0_x1 : rhb_sub Sdemo x0 x1.
Proof.
  unfold rhb_sub, rhb, x0, x1. simpl. right. split; [reflexivity|].
  unfold rhb_same. right. split; [reflexivity|].
  unfold redge, rop, Sdemo. simpl. split; [exists 0; reflexivity | exists 0; reflexivity].
Qed.

(* the idle event x2 is rhb-incomparable to the sender x0, via the clock *)
Example rhb_x0_x2_incomp :
  ~ rhb_sub Sdemo x0 x2 /\ ~ rhb_sub Sdemo x2 x0.
Proof.
  split; intro H;
  [ apply (proj1 (rhb_iff_rclock Sdemo wf_Sdemo ltac:(vm_compute; lia) x0 x2)) in H
  | apply (proj1 (rhb_iff_rclock Sdemo wf_Sdemo ltac:(vm_compute; lia) x2 x0)) in H ];
  unfold stamp_le in H; vm_compute in H; (now destruct H) || (intuition lia).
Qed.
```

Implementer notes: if any `vm_compute` literal or `wf_Sdemo` case-split differs,
read the actual computed value / `rop` result and adjust (the deliverable is that
`rclock`/`rhb` compute, not the specific constant). If the `ltac:(vm_compute; lia)`
inline positivity proof is awkward, add `Lemma sdemo_pos : 0 < rs_nprocs Sdemo. Proof.
vm_compute; lia. Qed.` and pass it. Keep each example's intent.

- [ ] **Step 2: Register the examples file**

`execution/dune`: add `  RoundSemExamples` after `  RoundSem`. `_CoqProject`: add
`execution/RoundSemExamples.v` after `execution/RoundSem.v`.

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 300 execution/RoundSemExamples.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/RoundSemExamples.v execution/dune _CoqProject
git commit -m "test(round-sem): Sdemo round system; rclock literals; rhb edge + incomparable pair"
```

---

### Task 5: docs + whole-project green

**Files:**
- Modify: `docs/INDEX.md`, `execution/DIM2_CLOCK.md`

- [ ] **Step 1: Add an INDEX.md subsection**

After the `#### `execution/OnlineClockLocal.v` …` subsection (and its `OnlineClockLocalExamples` paragraph), insert:

```markdown
#### `execution/RoundSem.v` — barrier-round operational model + schedule-free clock (exported)

An operational, primitive-state model: an `RSys` is `nprocs`, `nrounds`, and a
per-process program `rs_prog p : list Op`; `rop S p r = nth r (rs_prog S p)` is
process `p`'s round-`r` action. `rwf` is rendezvous compatibility (sends/recvs
matched per round). `rhb` is the barrier order on valid events (`rhb_IsPoset`,
unconditional, via the realized send∧recv edge). The clock `rclock S p r =
local_stamp (nprocs) p r (rop S p r)` reads **only** `p`'s own program and counter
— no `Schedule`/`op_at` projection — and `rhb_iff_rclock` proves causality through
it (via `stamp_iff`). This closes the proof-skeptic W-2 gap operationally for the
barrier-synchronized regime. Admit-free.

| Name | Meaning |
|------|---------|
| `RSys` / `rop` / `rvalid` / `rwf` | round system; per-process op; valid event; rendezvous well-formedness |
| `redge` / `rhb_same` / `rhb` / `rhb_sub` / `rhb_IsPoset` | realized edge; within-round order; barrier order; on the valid-event carrier; partial order |
| `rlay` / `rcomp` / `rstep` | round; sender (or own pid); `Recv?1:0` |
| `rcomp_eq_of_rhb` / `rhb_comparable_of_comp` / `rhb_rank` / `rcomp_lt_nprocs` | the `stamp_iff` structural hypotheses |
| `rhb_iff_stamp` | `rwf` ⟹ `rhb x y ↔ le_prod (nprocs-1) …` |
| `rclock` / `rclock_is_stamp` / `rhb_iff_rclock` | schedule-free clock; its coordinates; causality via it |

`RoundSemExamples.v` (test): a 3-proc/1-round system, `rclock` literals, an `rhb`
edge and an incomparable pair.
```

- [ ] **Step 2: Update `execution/DIM2_CLOCK.md` §6**

In the closing paragraph, record that an **operational primitive-state model** now
carries the clock: `RoundSem.v`'s `rhb_iff_rclock`, where `rclock S p r` depends only
on `nth r (rs_prog S p)` (the process's own program), so `local_obs` is no longer a
projection of a shared `Schedule` — the W-2 gap is closed for the barrier-round
regime. Add a lemma-map row:
`| operational primitive-state model: causality via a schedule-free local clock | rhb_iff_rclock (RoundSem.v) |`.

- [ ] **Step 3: Whole-project build**

Run: `bash .claude/scripts/timed-build.sh 1800 @all 4`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add docs/INDEX.md execution/DIM2_CLOCK.md
git commit -m "docs(round-sem): INDEX subsection + DIM2_CLOCK W-2 closed operationally (round model)"
```

---

## Self-Review

**Spec coverage:**
- Component 1 (RSys/rop/rvalid/rwf) → Task 1. ✓
- Component 2 (redge/rhb/rhb_sub/rhb_IsPoset) → Task 1. ✓
- Component 3 (rlay/rcomp/rstep + 5 structural lemmas) → Task 2. ✓
- Component 4 (rclock/rclock_is_stamp/rhb_iff_stamp/rhb_iff_rclock) → Task 3. ✓
- Component 5 (examples) → Task 4. ✓
- Wiring (dune/_CoqProject/Execution.v), INDEX, DIM2_CLOCK, whole-project green,
  Print Assumptions, zero admits → Tasks 1, 3, 4, 5. ✓

**Placeholder scan:** the three structural lemmas in Task 2 (`rcomp_eq_of_rhb`,
`rhb_comparable_of_comp`, `rhb_rank`) are given as STATEMENTS + detailed proof
OUTLINES rather than full scripts, with explicit analogues to cite
(`fb_comp_eq_of_hb`/`hb_or_of_fb_comp_eq`/`blo_rank`). This is intentional (the
proofs are case-analytic and mirror existing code); the implementer writes the
scripts and must NOT `admit`. All other steps have complete code.

**Type consistency:** `rhb`/`rhb_sub`/`rlay`/`rcomp`/`rstep`/`rclock`/`rhb_iff_stamp`/
`rhb_iff_rclock` names and signatures match across tasks; `rclock`'s `(N,p,r,op)`
shape matches `local_stamp`; `stamp_le`/`le_prod` field order matches `rclock_is_stamp`.

**Risk notes:** the fiddliest proofs are the three Task-2 structural lemmas; all
three have direct analogues already in the repo (`DisjointChainsDim.v`,
`OnlineClockLocal.v`). `rhb_IsPoset` (Task 1) is given in full and is the most
error-prone definitional proof — if a tactic fails, the math (a sender op ≠ a recv
op) is robust; adjust the `rewrite`/`discriminate` plumbing. If an example constant
differs, use the prover's value.

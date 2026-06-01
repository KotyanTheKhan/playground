# `desugar_wf` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task.

**Goal:** Prove `desugar_wf : forall s, wf_schedule s -> wf_program (desugar s)` (closes deferred task #12), with a correctly-strengthened `wf_schedule` (per-frontier partial matching).

**Architecture:** New `execution/ScheduleWf.v` holds `wf_frontier`/`wf_schedule`, the `find`/`op_for` characterization engine, and `desugar_wf`. A test file gives concrete `wf_schedule` witnesses. `Schedule.v` is untouched.

**Tech Stack:** Rocq 9.1, Stdlib `List`/`Arith`/`Lia`. Builds via `bash .claude/scripts/timed-build.sh`.

---

## Task ZW0: Scaffold

**Files:** Create `execution/ScheduleWf.v`, `execution/ScheduleWfExamples.v`; modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1: stub `execution/ScheduleWf.v`**
```coq
(* Well-formed schedules: per-frontier partial matching; desugar preserves wf. *)
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Event Edges Rank Poset Schedule.
Import ListNotations.
```
- [ ] **Step 2: stub `execution/ScheduleWfExamples.v`**
```coq
(* Concrete well-formed schedule witnesses (test-only). *)
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Schedule ScheduleWf Examples SyncShapeExamples.
Import ListNotations.
```
- [ ] **Step 3:** add `ScheduleWf` and `ScheduleWfExamples` to `execution/dune` `(modules …)` (after `YamlParseExamples`).
- [ ] **Step 4:** add `execution/ScheduleWf.v` and `execution/ScheduleWfExamples.v` to `_CoqProject` (after the Yaml entries).
- [ ] **Step 5: build** — `bash .claude/scripts/timed-build.sh 120 execution/ScheduleWfExamples.vo 2`. EXIT=0.
  - NOTE: `ScheduleWfExamples` imports `Examples` (`sched_n3`, `sched_m45`) and `SyncShapeExamples` (`s_demo`). Confirm those modules export those names; if `Examples`/`SyncShapeExamples` are not the right module names, run `grep -rn "Definition sched_n3\|Definition s_demo\|Definition sched_m45" execution/` and import the files that actually define them.
- [ ] **Step 6: commit** — `git add -A && git commit -m "chore(execution): scaffold ScheduleWf modules"`.

---

## Task ZW1: defs + `find`/`op_for` characterization engine (`ScheduleWf.v`)

**Files:** Modify `execution/ScheduleWf.v` (append after header).

- [ ] **Step 1: definitions + helpers**

```coq
Definition endpoints (pq : Pid * Pid) : list Pid := [fst pq; snd pq].

Definition wf_frontier (n : nat) (fr : Frontier) : Prop :=
  (forall a b, In (a, b) fr -> a < n /\ b < n /\ a <> b) /\
  NoDup (flat_map endpoints fr).

Definition wf_schedule (s : Schedule) : Prop :=
  forall fr, In fr (sch_frontiers s) -> wf_frontier (sch_nprocs s) fr.

(* membership of an endpoint in the flattened list *)
Lemma in_flat_fst : forall (fr : Frontier) p q, In (p, q) fr -> In p (flat_map endpoints fr).
Proof.
  intros fr p q Hin. apply in_flat_map. exists (p, q). split; [exact Hin| left; reflexivity].
Qed.
Lemma in_flat_snd : forall (fr : Frontier) p q, In (p, q) fr -> In q (flat_map endpoints fr).
Proof.
  intros fr p q Hin. apply in_flat_map. exists (p, q). split; [exact Hin| right; left; reflexivity].
Qed.

(* find on fst is canonical when endpoints are NoDup *)
Lemma find_fst_unique :
  forall (fr : Frontier) p q, NoDup (flat_map endpoints fr) -> In (p, q) fr ->
    find (fun pq => Nat.eqb (fst pq) p) fr = Some (p, q).
Proof.
  induction fr as [|[a b] fr' IH]; intros p q Hnd Hin; [destruct Hin|].
  simpl in Hin. simpl flat_map in Hnd. simpl.
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. rewrite Nat.eqb_refl. reflexivity.
  - (* (p,q) in tail; head (a,b) has fst a; a <> p because p occurs in tail flat *)
    destruct (Nat.eqb a p) eqn:Hap.
    + (* a = p, but then p appears as head fst AND in tail flat -> NoDup contradiction *)
      apply Nat.eqb_eq in Hap. subst a.
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      apply Hnotin. (* p in (b :: flat tail); p is in tail flat via Hin' *)
      simpl. right. apply (in_flat_fst fr' p q Hin').
    + apply IH.
      * inversion Hnd as [|x l Hnotin Hnd']. subst.
        inversion Hnd' as [|y m Hnotin2 Hnd'']. subst. exact Hnd''.
      * exact Hin'.
Qed.

Lemma find_snd_unique :
  forall (fr : Frontier) p q, NoDup (flat_map endpoints fr) -> In (p, q) fr ->
    find (fun pq => Nat.eqb (snd pq) q) fr = Some (p, q).
Proof.
  induction fr as [|[a b] fr' IH]; intros p q Hnd Hin; [destruct Hin|].
  simpl in Hin. simpl flat_map in Hnd. simpl.
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb b q) eqn:Hbq.
    + apply Nat.eqb_eq in Hbq. subst b.
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      (* q in (a :: flat tail): head occurrence is at the 'b' slot = second element.
         q appears in tail flat via Hin'; and the head list is [a; q]. NoDup of
         (a :: q :: flat tail) means q (the 2nd) not in flat tail. *)
      inversion Hnd' as [|y m Hnotin2 Hnd'']. subst.
      apply Hnotin2. apply (in_flat_snd fr' p q Hin').
    + apply IH.
      * inversion Hnd as [|x l Hnotin Hnd']. subst.
        inversion Hnd' as [|y m Hnotin2 Hnd'']. subst. exact Hnd''.
      * exact Hin'.
Qed.

(* a receiver's pid is never a fst -> find on fst gives None *)
Lemma no_fst_of_recv :
  forall (fr : Frontier) s p, NoDup (flat_map endpoints fr) -> In (s, p) fr ->
    find (fun pq => Nat.eqb (fst pq) p) fr = None.
Proof.
  induction fr as [|[a b] fr' IH]; intros s p Hnd Hin; [destruct Hin|].
  simpl in Hin. simpl flat_map in Hnd. simpl.
  destruct Hin as [Heq | Hin'].
  - injection Heq as <- <-. (* head is (s,p); fst = s. Need s <> p? No: need find fst=p.
       head fst = s; is s = p? if so [s;p]=[p;p] not NoDup. *)
    destruct (Nat.eqb a p) eqn:Hap.
    + apply Nat.eqb_eq in Hap. (* a = s here (head is (a,b)=(s,p)) so a=s, b=p; Hap: s=p *)
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      apply Hnotin. simpl. left. exact Hap.
    + (* a <> p; recurse: p still a snd in tail? No—(s,p) was the head. p might not be in tail.
         We must show find fst=p fr' = None. p occurs in head flat as snd (b=p). NoDup says
         p not in tail flat, so p is not any fst in tail. *)
      inversion Hnd as [|x l Hnotin Hnd']. subst.
      (* Hnotin : ~ In a (p :: flat fr'); Hnd' : NoDup (p :: flat fr') *)
      inversion Hnd' as [|y m Hnotin2 Hnd'']. subst.
      (* Hnotin2 : ~ In p (flat fr'). So p is no fst in fr'. *)
      clear IH. (* prove find = None directly: no pair in fr' has fst p *)
      apply find_none_aux. intros [c d] Hcd. simpl.
      destruct (Nat.eqb c p) eqn:Hcp; [|reflexivity].
      apply Nat.eqb_eq in Hcp. subst c. exfalso. apply Hnotin2.
      apply (in_flat_fst fr' p d Hcd).
  - (* (s,p) in tail *)
    destruct (Nat.eqb a p) eqn:Hap.
    + apply Nat.eqb_eq in Hap. subst a.
      exfalso. inversion Hnd as [|x l Hnotin Hnd']. subst.
      apply Hnotin. simpl. right. apply (in_flat_snd fr' s p Hin').
    + apply IH with (s := s).
      * inversion Hnd as [|x l Hnotin Hnd']. subst.
        inversion Hnd' as [|y m Hnotin2 Hnd'']. subst. exact Hnd''.
      * exact Hin'.
Qed.
```

NOTE on `find_none_aux`: Stdlib has `find_none : find f l = None -> forall x, In x l -> f x = false`; the reverse direction (build `find = None` from "all false") is needed. If a named reverse lemma is unavailable, prove a tiny local one:
```coq
Lemma find_none_aux {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> find f l = None.
Proof.
  induction l as [|a l' IH]; intro Hall; simpl; [reflexivity|].
  rewrite (Hall a (or_introl eq_refl)). apply IH. intros x Hx. apply Hall. right. exact Hx.
Qed.
```
Place `find_none_aux` BEFORE `no_fst_of_recv`. The `inversion Hnd` NoDup-peeling steps above are written for `NoDup (a :: b :: rest)`; adjust the `as`-patterns if Coq names the pieces differently, but the structure (head-not-in-tail twice) is correct.

- [ ] **Step 2: the `op_for` characterization**

```coq
Lemma op_for_send_iff :
  forall n fr p q k, wf_frontier n fr ->
    (op_for fr p k = Send q k <-> In (p, q) fr).
Proof.
  intros n fr p q k [Hrange Hnd]. unfold op_for. split.
  - intro H. destruct (find (fun pq => Nat.eqb (fst pq) p) fr) as [[a b]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hfst]. apply Nat.eqb_eq in Hfst. simpl in Hfst. subst a.
      injection H as <-. exact Hin.
    + (* falls to recv/local branch — can't be a Send *)
      destruct (find (fun pq => Nat.eqb (snd pq) p) fr) as [[a b]|]; discriminate H.
  - intro Hin. rewrite (find_fst_unique fr p q Hnd Hin). reflexivity.
Qed.

Lemma op_for_recv_iff :
  forall n fr s p k, wf_frontier n fr ->
    (op_for fr p k = Recv s k <-> In (s, p) fr).
Proof.
  intros n fr s p k [Hrange Hnd]. unfold op_for. split.
  - intro H. destruct (find (fun pq => Nat.eqb (fst pq) p) fr) as [[a b]|] eqn:Hf.
    + discriminate H.
    + destruct (find (fun pq => Nat.eqb (snd pq) p) fr) as [[a b]|] eqn:Hg.
      * apply find_some in Hg as [Hin Hsnd]. apply Nat.eqb_eq in Hsnd. simpl in Hsnd. subst b.
        injection H as <-. exact Hin.
      * discriminate H.
  - intro Hin. rewrite (no_fst_of_recv fr s p Hnd Hin).
    rewrite (find_snd_unique fr s p Hnd Hin). reflexivity.
Qed.
```

- [ ] **Step 3: inverse range lemma**

```coq
Lemma op_at_desugar_inv :
  forall s p i o, op_at (desugar_prog s) p i = Some o ->
    p < sch_nprocs s /\ i < length (sch_frontiers s) /\
    o = op_for (nth i (sch_frontiers s) []) p i.
Proof.
  intros s p i o H.
  destruct (Nat.ltb p (sch_nprocs s)) eqn:Hp.
  - apply Nat.ltb_lt in Hp.
    destruct (Nat.ltb i (length (sch_frontiers s))) eqn:Hi.
    + apply Nat.ltb_lt in Hi.
      rewrite (op_at_desugar s p i Hp Hi) in H. injection H as <-.
      repeat split; [exact Hp | exact Hi | reflexivity].
    + (* i out of range -> op_at None, contradiction *)
      exfalso. apply Nat.ltb_ge in Hi.
      unfold op_at in H. rewrite proc_ops_desugar in H by exact Hp.
      rewrite nth_error_None in H. rewrite length_map, length_seq in H. lia.
  - (* p out of range -> proc_ops = [] -> op_at None *)
    exfalso. apply Nat.ltb_ge in Hp.
    unfold op_at, proc_ops, desugar_prog in H. simpl in H.
    rewrite nth_overflow in H by (rewrite length_map, length_seq; exact Hp).
    simpl in H. destruct i; discriminate H.
Qed.
```
NOTE: if `nth_error_None`/`nth_overflow`/`length_map`/`length_seq` names differ, find them with `Search nth_error None`, `Search nth (length _)`. The two out-of-range branches just need to show `op_at = None`, contradicting `Some o`.

- [ ] **Step 4: build** — `bash .claude/scripts/timed-build.sh 240 execution/ScheduleWf.vo 2`. EXIT=0.
- [ ] **Step 5: commit** — `git add execution/ScheduleWf.v && git commit -m "feat(execution): wf_schedule + op_for characterization engine"`.

---

## Task ZW2: `desugar_wf` (`ScheduleWf.v`)

**Files:** Modify `execution/ScheduleWf.v` (append).

- [ ] **Step 1: the theorem**

```coq
Theorem desugar_wf : forall s, wf_schedule s -> wf_program (desugar s).
Proof.
  intros s Hwf.
  (* desugar's prog is desugar_prog s; nprocs (desugar s) = sch_nprocs s *)
  assert (Hnp : nprocs (desugar s) = sch_nprocs s) by apply nprocs_desugar.
  constructor.
  - (* wf_send_targets *)
    intros p i q t Hsend.
    apply op_at_desugar_inv in Hsend as [Hp [Hi Ho]].
    pose proof (op_for_tag (nth i (sch_frontiers s) []) p i q t) as [Htag _].
    assert (Hofeq : op_for (nth i (sch_frontiers s) []) p i = Send q t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth i (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hi. }
    pose proof (proj1 (op_for_send_iff (sch_nprocs s) _ p q i Hfr) Hofeq) as Hin.
    destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [_ [Hq _]].
    rewrite Hnp. exact Hq.
  - (* wf_recv_sources *)
    intros q j p t Hrecv.
    apply op_at_desugar_inv in Hrecv as [Hq [Hj Ho]].
    pose proof (op_for_tag (nth j (sch_frontiers s) []) q j p t) as [_ Htag].
    assert (Hofeq : op_for (nth j (sch_frontiers s) []) q j = Recv p t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth j (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hj. }
    pose proof (proj1 (op_for_recv_iff (sch_nprocs s) _ p q j Hfr) Hofeq) as Hin.
    destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [Hp _].
    rewrite Hnp. exact Hp.
  - (* wf_recv_matched *)
    intros q j p t Hrecv.
    apply op_at_desugar_inv in Hrecv as [Hq [Hj Ho]].
    pose proof (op_for_tag (nth j (sch_frontiers s) []) q j p t) as [_ Htag].
    assert (Hofeq : op_for (nth j (sch_frontiers s) []) q j = Recv p t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth j (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hj. }
    pose proof (proj1 (op_for_recv_iff (sch_nprocs s) _ p q j Hfr) Hofeq) as Hin.
    assert (Hp : p < sch_nprocs s).
    { destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [Hp _]. exact Hp. }
    exists j. split.
    + (* op_at (desugar) p j = Some (Send q j) *)
      pose proof (proj2 (op_for_send_iff (sch_nprocs s) _ p q j Hfr) Hin) as Hsend.
      rewrite (op_at_desugar s p j Hp Hj). rewrite Hsend. reflexivity.
    + (* uniqueness *)
      intros i' Hi'. apply op_at_desugar_inv in Hi' as [Hp' [Hi'' Ho']].
      pose proof (op_for_tag (nth i' (sch_frontiers s) []) p i' q j) as [Htag' _].
      symmetry in Ho'. specialize (Htag' Ho'). lia.
  - (* wf_send_matched *)
    intros p i q t Hsend.
    apply op_at_desugar_inv in Hsend as [Hp [Hi Ho]].
    pose proof (op_for_tag (nth i (sch_frontiers s) []) p i q t) as [Htag _].
    assert (Hofeq : op_for (nth i (sch_frontiers s) []) p i = Send q t) by (symmetry; exact Ho).
    specialize (Htag Hofeq). subst t.
    assert (Hfr : wf_frontier (sch_nprocs s) (nth i (sch_frontiers s) [])).
    { apply Hwf. apply nth_In. exact Hi. }
    pose proof (proj1 (op_for_send_iff (sch_nprocs s) _ p q i Hfr) Hofeq) as Hin.
    assert (Hq : q < sch_nprocs s).
    { destruct Hfr as [Hrange _]. destruct (Hrange p q Hin) as [_ [Hq _]]. exact Hq. }
    exists i. split.
    + pose proof (proj2 (op_for_recv_iff (sch_nprocs s) _ p q i Hfr) Hin) as Hrecv.
      rewrite (op_at_desugar s q i Hq Hi). rewrite Hrecv. reflexivity.
    + intros j' Hj'. apply op_at_desugar_inv in Hj' as [Hq' [Hj'' Ho']].
      pose proof (op_for_tag (nth j' (sch_frontiers s) []) q j' p i) as [_ Htag'].
      symmetry in Ho'. specialize (Htag' Ho'). lia.
Qed.
```

NOTE: the `op_for_send_iff`/`op_for_recv_iff` applications pass the frontier as `_` (inferred). If unification needs it explicit, supply `(nth i (sch_frontiers s) [])`. The uniqueness sub-proofs hinge on `op_for_tag`: any `Send q j` at index `i'` forces `j = i'`. If `constructor` does not produce the four `wf_program` fields in this order, reorder the bullets to match `Op.v` (`wf_send_targets`, `wf_recv_sources`, `wf_recv_matched`, `wf_send_matched`).

- [ ] **Step 2: build** — `bash .claude/scripts/timed-build.sh 300 execution/ScheduleWf.vo 2`. EXIT=0.
- [ ] **Step 3: commit** — `git add execution/ScheduleWf.v && git commit -m "feat(execution): desugar_wf — desugaring a wf schedule yields a wf program"`.

---

## Task ZW3: witnesses + export + INDEX + audit

**Files:** Modify `execution/ScheduleWfExamples.v`, `execution/Execution.v`, `docs/INDEX.md`.

- [ ] **Step 1: concrete witnesses** (`ScheduleWfExamples.v`)

```coq
(* helper: a single-pair frontier with a<b<n is well-formed *)
Lemma wf_frontier_one : forall n a b, a < n -> b < n -> a <> b ->
  wf_frontier n [(a, b)].
Proof.
  intros n a b Ha Hb Hab. split.
  - intros x y Hin. simpl in Hin. destruct Hin as [Heq|[]].
    injection Heq as <- <-. repeat split; assumption.
  - simpl. repeat constructor.
    + simpl. intros [H|[]]. exact (Hab H).
    + simpl. tauto.
Qed.

Example wf_sched_n3 : wf_schedule sched_n3.
Proof.
  intros fr Hin. unfold sched_n3 in Hin. simpl in Hin.
  destruct Hin as [<- | [<- | []]];
    [ apply wf_frontier_one; lia | apply wf_frontier_one; lia ].
Qed.

Example wf_s_demo : wf_schedule s_demo.
Proof.
  intros fr Hin. unfold s_demo in Hin. simpl in Hin.
  destruct Hin as [<- | [<- | []]];
    [ apply wf_frontier_one; lia | apply wf_frontier_one; lia ].
Qed.

Example wf_program_desugar_n3 : wf_program (desugar sched_n3).
Proof. apply desugar_wf. exact wf_sched_n3. Qed.
```
NOTE: `sched_n3`/`s_demo` frontier lists are `[[(0,1)];[(1,2)]]` and `[[(0,1)];[(1,0)]]`. If the `destruct Hin` shape differs (e.g. more/fewer frontiers), adjust the number of `[<- | …]` branches. `wf_frontier_one`'s `NoDup [a;b]` proof: `repeat constructor` builds `NoDup (a :: b :: nil)`; the side goals are `~ In a [b]` (i.e. `a <> b`) and `~ In b []` (trivial) and `NoDup []`. Adjust the tactic if the goal shape needs `apply NoDup_cons`. Optionally add `wf_sched_m45` for `sched_m45` (5 single-pair frontiers) the same way.

- [ ] **Step 2: build examples** — `bash .claude/scripts/timed-build.sh 180 execution/ScheduleWfExamples.vo 2`. EXIT=0.
- [ ] **Step 3: export** — in `execution/Execution.v`, append `ScheduleWf` to the `Require Export` list (NOT the examples).
- [ ] **Step 4: whole-project build** — `bash .claude/scripts/timed-build.sh 1800 @all 4`. EXIT=0.
- [ ] **Step 5: audit** — temporarily register a scratch `execution/DesugarWfAudit.v` (`From Execution Require Import ScheduleWf. Print Assumptions desugar_wf.`), build via wrapper, capture output (expected `Closed under the global context`), then REMOVE it and revert its `dune`/`_CoqProject` registration.
- [ ] **Step 6: INDEX** — add a `#### execution/ScheduleWf.v — well-formed schedules + desugar_wf` subsection to `docs/INDEX.md` (after the Schedule entry or near the execution core), with a name/meaning table for `wf_frontier`, `wf_schedule`, `op_for_send_iff`/`op_for_recv_iff`, `desugar_wf`. Note the strengthening (partial-matching frontiers) vs. the original in-range-only sketch.
- [ ] **Step 7: commit** — `git add execution/ScheduleWfExamples.v execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): wf_schedule witnesses + export desugar_wf + INDEX"`.

---

## Self-Review (checked against the spec)

- **Spec coverage:** `wf_frontier`/`wf_schedule` + `find`/`op_for` engine → ZW1; `op_at_desugar_inv` → ZW1 Step 3; `desugar_wf` four fields → ZW2; witnesses + export + INDEX + audit → ZW0+ZW3. All mapped.
- **Strengthening recorded:** the design note + INDEX both state `wf_schedule` is the partial-matching strengthening (original in-range-only is unsound — counterexample `[(0,1);(0,2)]`).
- **Name consistency:** `wf_frontier`/`wf_schedule`/`endpoints`/`find_fst_unique`/`find_snd_unique`/`no_fst_of_recv`/`op_for_send_iff`/`op_for_recv_iff`/`op_at_desugar_inv`/`desugar_wf` consistent across ZW1–ZW3. Reuses Schedule.v's `op_for_tag`, `op_at_desugar`, `proc_ops_desugar`, `nprocs_desugar` and Op.v's `wf_program` field names verbatim.
- **No placeholders:** every proof is given in full; named-lemma fallbacks (`find_none_aux`, `nth_error_None`) flagged with `Search` instructions.

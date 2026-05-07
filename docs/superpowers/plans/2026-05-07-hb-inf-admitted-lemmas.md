# hb_inf Admitted Lemmas Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace four `Admitted` lemmas in `ExtendedHistory.v` with real Coq proofs by introducing a colimit relation `hb_inf`.

**Architecture:** Define `hb_inf e1 e2 := exists n, happened_before (pp_history_ext n) e1 e2` as the causal relation over unbounded execution. Restate the four `ax_*` lemmas in terms of `hb_inf` (dropping the false `forall n` quantifier) and prove each by choosing the minimal `n` that puts the relevant message in the history, then applying the existing in-range causality lemma. Update `ex_is_ping_pong` to use `hb_inf` and drop its `n` parameter.

**Tech Stack:** Coq/Rocq (Stdlib), `mise run build-posets` to build.

---

### Task 1: Add `hb_inf` definition

**Files:**
- Modify: `happenedBefore/examples/pingpong/ExtendedHistory.v`

The build should pass both before and after this task.

- [ ] **Step 1: Insert the definition**

In `happenedBefore/examples/pingpong/ExtendedHistory.v`, find the line:

```coq
  (* ── IsPairAlternatingSymPingPong instance ───────────────────────────────  *)
```

Insert the following block immediately before it (after the last `Qed.` of the causality lemmas section):

```coq
  (* ── Colimit relation ────────────────────────────────────────────────────  *)

  Definition hb_inf (e1 e2 : Event) : Prop :=
    exists n, happened_before (pp_history_ext n) e1 e2.

```

- [ ] **Step 2: Build**

```
mise run build-posets
```

Expected: build completes with no errors.

- [ ] **Step 3: Commit**

```bash
git add happenedBefore/examples/pingpong/ExtendedHistory.v
git commit -m "feat: add hb_inf colimit definition to ExtendedHistory"
```

---

### Task 2: Replace the four admitted `ax_*` lemmas

**Files:**
- Modify: `happenedBefore/examples/pingpong/ExtendedHistory.v`

> **Note:** After this task the build will fail because the `ex_is_ping_pong` instance still
> passes `n` to the old `ax_*` signatures. Task 3 restores the build.

- [ ] **Step 1: Replace `ax_ping`**

Find and replace the entire block (comment + lemma):

```coq
  (** In-range case: [ping_causes_recv_ext].
      Out-of-range case: requires extending to an infinite history. *)
  Lemma ax_ping : forall n i,
    happened_before (pp_history_ext n)
      (map_ping_send GAP_0 GAP_1 i) (map_ping_recv GAP_0 GAP_1 i).
  Admitted.
```

with:

```coq
  Lemma ax_ping : forall i,
    hb_inf (map_ping_send GAP_0 GAP_1 i) (map_ping_recv GAP_0 GAP_1 i).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 1).
    apply ping_causes_recv_ext. lia.
  Qed.
```

- [ ] **Step 2: Replace `ax_turn`**

Find and replace:

```coq
  (** In-range case: [turn_causes_pong_ext].
      Out-of-range case: requires extending to an infinite history. *)
  Lemma ax_turn : forall n i,
    happened_before (pp_history_ext n)
      (map_ping_recv GAP_0 GAP_1 i) (map_pong_send GAP_0 GAP_1 i).
  Admitted.
```

with:

```coq
  Lemma ax_turn : forall i,
    hb_inf (map_ping_recv GAP_0 GAP_1 i) (map_pong_send GAP_0 GAP_1 i).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 2).
    apply turn_causes_pong_ext. lia.
  Qed.
```

- [ ] **Step 3: Replace `ax_pong`**

Find and replace:

```coq
  (** In-range case: [pong_causes_recv_ext].
      Out-of-range case: requires extending to an infinite history. *)
  Lemma ax_pong : forall n i,
    happened_before (pp_history_ext n)
      (map_pong_send GAP_0 GAP_1 i) (map_pong_recv GAP_0 GAP_1 i).
  Admitted.
```

with:

```coq
  Lemma ax_pong : forall i,
    hb_inf (map_pong_send GAP_0 GAP_1 i) (map_pong_recv GAP_0 GAP_1 i).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 3).
    apply pong_causes_recv_ext. lia.
  Qed.
```

- [ ] **Step 4: Replace `ax_next`**

Find and replace:

```coq
  (** In-range case: [inter_causes_next_ext].
      Out-of-range case: requires extending to an infinite history. *)
  Lemma ax_next : forall n i,
    happened_before (pp_history_ext n)
      (map_pong_recv GAP_0 GAP_1 i) (map_ping_send GAP_0 GAP_1 (S i)).
  Admitted.
```

with:

```coq
  Lemma ax_next : forall i,
    hb_inf (map_pong_recv GAP_0 GAP_1 i) (map_ping_send GAP_0 GAP_1 (S i)).
  Proof.
    intro i. unfold hb_inf.
    exists (i * msgs_per_cycle_ext + 4).
    apply inter_causes_next_ext. lia.
  Qed.
```

---

### Task 3: Update `ex_is_ping_pong` instance, build, and commit

**Files:**
- Modify: `happenedBefore/examples/pingpong/ExtendedHistory.v`

The instance currently takes an `n : nat` parameter and uses `happened_before (pp_history_ext n)` as the relation, passing `n` explicitly to each `ax_*` lemma. Replace it with an instance over `hb_inf` with no parameter.

- [ ] **Step 1: Replace the instance**

Find and replace the entire instance block:

```coq
  Instance ex_is_ping_pong (n : nat) :
    IsPairAlternatingSymPingPong (happened_before (pp_history_ext n)).
  Proof.
    exact {|
      map_cycle_ping_send := map_ping_send GAP_0 GAP_1;
      map_cycle_ping_recv := map_ping_recv GAP_0 GAP_1;
      map_cycle_pong_send := map_pong_send GAP_0 GAP_1;
      map_cycle_pong_recv := map_pong_recv GAP_0 GAP_1;
      ax_even_init := map_ping_send_even_process GAP_0 GAP_1;
      ax_even_resp := map_ping_recv_even_process GAP_0 GAP_1;
      ax_odd_init  := map_ping_send_odd_process  GAP_0 GAP_1;
      ax_odd_resp  := map_ping_recv_odd_process  GAP_0 GAP_1;
      ax_ping_rel  := ax_ping n;
      ax_turn_rel  := ax_turn n;
      ax_pong_rel  := ax_pong n;
      ax_next_rel  := ax_next n
    |}.
  Defined.
```

with:

```coq
  Instance ex_is_ping_pong : IsPairAlternatingSymPingPong hb_inf.
  Proof.
    exact {|
      map_cycle_ping_send := map_ping_send GAP_0 GAP_1;
      map_cycle_ping_recv := map_ping_recv GAP_0 GAP_1;
      map_cycle_pong_send := map_pong_send GAP_0 GAP_1;
      map_cycle_pong_recv := map_pong_recv GAP_0 GAP_1;
      ax_even_init := map_ping_send_even_process GAP_0 GAP_1;
      ax_even_resp := map_ping_recv_even_process GAP_0 GAP_1;
      ax_odd_init  := map_ping_send_odd_process  GAP_0 GAP_1;
      ax_odd_resp  := map_ping_recv_odd_process  GAP_0 GAP_1;
      ax_ping_rel  := ax_ping;
      ax_turn_rel  := ax_turn;
      ax_pong_rel  := ax_pong;
      ax_next_rel  := ax_next
    |}.
  Defined.
```

- [ ] **Step 2: Build**

```
mise run build-posets
```

Expected: build completes with no errors and zero `Admitted` warnings for `ExtendedHistory.v`.

- [ ] **Step 3: Commit**

```bash
git add happenedBefore/examples/pingpong/ExtendedHistory.v
git commit -m "feat: prove admitted ax_* lemmas via hb_inf colimit"
```

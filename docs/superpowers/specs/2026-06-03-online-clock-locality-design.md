# Online clock maintenance: the locality theorem — Design

**Date:** 2026-06-03
**Branch:** `online-maintenance`
**Goal:** Close the open "online" item of the dim-2 clock by exhibiting a
**schedule-blind** stamping function `local_stamp (N p i : nat) (o : Op)` and
proving it reproduces the proven global `stamp` for every valid event — so the
clock is computable from a process's local data (own pid, own op index, own op,
and for a `Recv` the sender id carried in the message) with **no global view and
no clock-value piggybacking**. The headline corollary restates the causality
characterization `blo s x y ↔ stamp ≤_prod` entirely in terms of `local_stamp`.
Serves the project [north star](../../../CLAUDE.md); the offline characterization
half is [`execution/OnlineClock.v`](../../../execution/OnlineClock.v) /
[`execution/DIM2_CLOCK.md`](../../../execution/DIM2_CLOCK.md) §6.
**Depends on:** `Execution.OnlineClock` (`stamp`, `clk_lay`/`clk_comp`/`clk_step`,
`le_lex3`, `le_prod`, `blo_iff_stamp`), `Execution.DisjointChainsDim`
(`fb_comp`, `block_op_for`), `Execution.Schedule`/`ScheduleWf` (`op_for`,
`op_at_desugar`), `Execution.Op` (`Op = Local | Send | Recv`),
`Execution.BarrierExecDim` (`blo`).

## What this is (and is not)

The locality is witnessed by the **type signature**: `local_stamp` takes only
`(N, p, i, o)` and *cannot* consult the global schedule `s`, because `s` is not
an argument. The theorem `local_stamp … = stamp s x` then shows this
schedule-blind function reproduces the global clock. This is deliberately **not
deep** — the analytical content already lives in `blo_iff_stamp` (proven). The
deliverable's value is to (a) close the open item with a machine-checked
locality statement, and (b) pin the **minimal interface**: per-process state is
`(pid, a local counter)`, and the only cross-process datum the clock consumes is
a `Recv`'s sender id (inherent message metadata). The asymptotic "beats vector
clocks" cost (O(1) state + O(1) piggyback vs Θ(N)) is argued in prose, backed
formally by the signature plus the interface lemmas (§ Component 4).

Scope unchanged from the offline result: `blo` (barrier-synchronized executions),
classical, admit-free. The fact that "each process's local op counter equals the
global layer" holds *by construction* of the `blo` model (every process performs
one op per frontier index); it is noted, not separately re-proven.

## Component 1 — `local_stamp` and `local_obs` (`execution/OnlineClockLocal.v`)

```coq
(* The clock computed from purely local data. s is deliberately NOT an argument:
   the locality of the clock is exactly this signature. *)
Definition local_stamp (N p i : nat) (o : Op) : (nat * nat * nat) * (nat * nat * nat) :=
  let comp := match o with Recv src _ => src | _ => p end in
  let step := match o with Recv _ _ => 1 | _ => 0 end in
  ((i, comp, step), (i, (N - 1) - comp, step)).

(* What process p observes at its index-i event: its own op (a Recv carries the sender). *)
Definition local_obs (s : Schedule) (p i : nat) : Op :=
  op_for (nth i (sch_frontiers s) []) p i.
```

## Component 2 — the locality theorem `local_stamp_correct` (`OnlineClockLocal.v`)

```coq
Theorem local_stamp_correct :
  forall s (x : ep_carrier (exec_of_schedule s)),
    local_stamp (sch_nprocs s) (fst (proj1_sig x)) (snd (proj1_sig x))
                (local_obs s (fst (proj1_sig x)) (snd (proj1_sig x)))
    = stamp s x.
```

Proof sketch: `unfold stamp, clk_lay, clk_comp, clk_step, local_stamp, local_obs`.
The global `stamp` reads the op only via `op_at (desugar_prog s) (fst …) (snd …)`;
`block_op_for s x` rewrites that to `Some (op_for (nth (snd …) (sch_frontiers s) [])
(fst …) (snd …))`, i.e. `Some (local_obs s (fst …) (snd …))`. Then `clk_comp`/
`clk_step`'s `match … with Recv … | _ …` and `local_stamp`'s matches coincide;
`destruct (local_obs …) as [|tgt tg|src tg]` closes all three op cases by
`reflexivity`. `clk_lay = snd (proj1_sig x) = i` definitionally. Near-definitional
once `block_op_for` is applied.

## Component 3 — the causality corollary `blo_iff_local_stamp` (`OnlineClockLocal.v`)

```coq
(* product of the two lex orders, on stamp pairs *)
Definition stamp_le (st1 st2 : (nat*nat*nat)*(nat*nat*nat)) : Prop :=
  let '((a1,a2,a3),(b1,b2,b3)) := st1 in
  let '((c1,c2,c3),(d1,d2,d3)) := st2 in
  le_lex3 a1 a2 a3 c1 c2 c3 /\ le_lex3 b1 b2 b3 d1 d2 d3.

Corollary blo_iff_local_stamp :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
  forall x y : ep_carrier (exec_of_schedule s),
    blo s x y <->
    stamp_le
      (local_stamp (sch_nprocs s) (fst (proj1_sig x)) (snd (proj1_sig x))
                   (local_obs s (fst (proj1_sig x)) (snd (proj1_sig x))))
      (local_stamp (sch_nprocs s) (fst (proj1_sig y)) (snd (proj1_sig y))
                   (local_obs s (fst (proj1_sig y)) (snd (proj1_sig y)))).
```

Proof sketch: rewrite both `local_stamp …` to `stamp s x` / `stamp s y` via
`local_stamp_correct`. Then `stamp_le (stamp s x) (stamp s y)` unfolds (the
`stamp` wrapper is `((l,c,st),(l,(N-1)-c,st))`) to exactly
`le_lex3 (clk_lay x)(clk_comp x)(clk_step x) … /\ le_lex3 (clk_lay x)((N-1)-clk_comp x) …`,
which is `le_prod (sch_nprocs s - 1) (clk_lay x)(clk_comp x)(clk_step x) …` by
definition. Conclude with `blo_iff_stamp s Hwf Hnp x y`. (Helper lemma
`stamp_le_stamp : stamp_le (stamp s x) (stamp s y) <-> le_prod (sch_nprocs s - 1)
(clk_lay s x)(clk_comp s x)(clk_step s x)(clk_lay s y)(clk_comp s y)(clk_step s y)`,
proved by `destruct`/`reflexivity`/`tauto`, bridges the tuple and scalar forms.)

## Component 4 — interface lemmas: the minimal cross-process datum (`OnlineClockLocal.v`)

Formalize that a `Send`/`Local` event contributes no cross-process clock data
(comp is the own pid), and that a `Recv` uses only its sender (not the tag):

```coq
Lemma local_stamp_send_eq_local :
  forall N p i t tg, local_stamp N p i (Send t tg) = local_stamp N p i Local.
Proof. reflexivity. Qed.

Lemma local_stamp_recv_tag_irrel :
  forall N p i src tg tg', local_stamp N p i (Recv src tg) = local_stamp N p i (Recv src tg').
Proof. reflexivity. Qed.
```

These two `reflexivity` facts are the formal backbone of the prose claim: the
clock reads, across processes, only a `Recv`'s sender id — **never** a piggybacked
clock value — so per-message overhead is O(1) (one pid), vs the vector clock's
Θ(N).

## Component 5 — examples (`execution/OnlineClockLocalExamples.v`, test-only)

Reuse `s_msg3`, `wf_s_msg3`, `e00`/`e10`/`e20`, `msg3_blo_e00_e10` from
`OnlineClockExamples.v`.

1. **Local stamps match the offline literals** (`vm_compute`):
   - `local_obs s_msg3 0 0 = Send 1 0` ⇒ `local_stamp 3 0 0 (Send 1 0) = ((0,0,0),(0,2,0))`.
   - `local_obs s_msg3 1 0 = Recv 0 0` ⇒ `local_stamp 3 1 0 (Recv 0 0) = ((0,0,1),(0,2,1))`.
   - `local_obs s_msg3 2 0 = Local` ⇒ `local_stamp 3 2 0 Local = ((0,2,0),(0,0,0))`.
   Each an `Example … = …. Proof. vm_compute. reflexivity. Qed.` (read the real
   `op_for` value if a literal differs; the point is `local_stamp = stamp`).
2. **`local_stamp_correct` instance:** `Example : local_stamp 3 0 0 (local_obs s_msg3 0 0) = stamp s_msg3 e00.` by `vm_compute; reflexivity` (or `apply local_stamp_correct`).
3. **Causality via the local clock:** from `msg3_blo_e00_e10`, derive the ordered
   local stamps through `blo_iff_local_stamp`; and the isolated `e20` is
   `stamp_le`-incomparable to `e00` (mirrors the offline incomparability).

## Files, wiring, testing

- New: `execution/OnlineClockLocal.v` (exported), `execution/OnlineClockLocalExamples.v` (test).
- `execution/dune` + `_CoqProject`: add both (after `OnlineClockExamples`).
- `execution/Execution.v`: add `OnlineClockLocal` to the `Require Export`.
- `docs/INDEX.md`: a subsection under the `OnlineClock.v` entry.
- `execution/DIM2_CLOCK.md` §6: mark the locality half proven (the open item is
  now narrowed to a full operational distributed-semantics model, if ever wanted).
- All builds via the wrapper; **zero `Admitted`**; files <500 lines; fast `Qed`s.
- `Print Assumptions local_stamp_correct blo_iff_local_stamp` recorded (expect only
  the standard classical axioms inherited from `blo_iff_stamp`).

## Acceptance criteria

1. `local_stamp` (schedule-blind, `s` not an argument), `local_obs`,
   `local_stamp_correct` — proven, zero admits.
2. `stamp_le`, `stamp_le_stamp` bridge, `blo_iff_local_stamp` — the causality
   characterization expressed purely via `local_stamp`. Zero admits.
3. `local_stamp_send_eq_local`, `local_stamp_recv_tag_irrel` — the minimal-interface
   lemmas.
4. Examples (local stamps = offline literals; a `local_stamp_correct` instance; a
   causality instance). Whole-project green; `INDEX.md` + `DIM2_CLOCK.md` updated.

## Out of scope / honestly noted

- **Still the characterization, now localized — not a full protocol model.** No
  small-step distributed operational semantics, no message channels, no global
  run relation. That (Level C from brainstorming) remains a possible future
  branch; this slice proves the clock is a function of local data only.
- **`lay` = local counter alignment is by construction.** The `blo` barrier model
  places one event per process per frontier index, so a process's local op count
  equals the global layer; we rely on this rather than re-deriving it.
- **`blo`-only.** Arbitrary pairwise-message executions are not dim-2 and get no
  local 2-coordinate clock (unchanged from `DIM2_CLOCK.md` §5).
- **No asymptotic cost theorem in Coq.** The O(1)-state / O(1)-piggyback claim is
  prose, evidenced by `local_stamp`'s signature and the Component 4 lemmas.

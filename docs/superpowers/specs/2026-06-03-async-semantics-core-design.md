# Async distributed semantics — Slice 1: the operational core — Design

**Date:** 2026-06-03
**Branch:** `async-sem`
**Arc:** This is **Slice 1 of 3** of the distributed-semantics work that closes the
last open item of the dim-2 clock (the proof-skeptic's W-2: make `local_obs` and
the layer counter *primitive local state*, not projections of a `Schedule`).
- **Slice 1 (this spec):** the asynchronous operational core — `Config`, a FIFO
  message-passing `step`, runs (relational + executable, proven equivalent), the
  operational happened-before `ohb`, and the metatheorem *`ohb` is a strict
  partial order on any valid run*.
- **Slice 2 (later):** a `Synchronized` (barrier-aligned) predicate on runs, an
  operationally-assigned timestamp, and `Synchronized run → (ohb e f ↔ ts ≤_prod)`.
- **Slice 3 (later, optional):** bridge a synchronized run to a `Schedule` with
  `ohb ≈ blo`, transporting `blo_iff_local_stamp`.

**Goal of Slice 1:** a self-contained, admit-free asynchronous message-passing
operational semantics with a proven-well-behaved causal order. No timestamps, no
synchronization predicate, no `blo` bridge here.
**Depends on:** `Execution.Op` (`Op = Local | Send (tgt) (tag) | Recv (src) (tag)`);
Stdlib `List`, `Arith`, `Lia`, `Relation_Operators` (`clos_trans`),
`RelationClasses` (`StrictOrder`).

## Honest scope

The dim-2 clock characterizes causality only on the **barrier-synchronized**
sub-runs (Slice 2); a general async run is not dim-2 (those need vector clocks).
Slice 1 deliberately builds the *general* async model as the honest container and
proves only model-level metatheory (`ohb` is a partial order). FIFO channels (one
queue per ordered process pair, head = oldest) make message matching
deterministic. Matching is **typed** (sender + tag), consistent with the rest of
the project, keeping Slice 3's bridge feasible.

## Component 1 — types and configuration (`execution/AsyncSem.v`)

```coq
Record Msg := { msg_tag : nat ; msg_src_event : nat }.   (* src_event = trace index of the Send *)

Record Config := {
  cfg_pc   : nat -> nat ;            (* per-process program counter *)
  cfg_chan : nat -> nat -> list Msg  (* cfg_chan s d = FIFO queue s->d; head = oldest *)
}.

Record Event := {
  ev_proc    : nat ;
  ev_idx     : nat ;          (* = pc of ev_proc just before this step (the local layer) *)
  ev_op      : Op ;
  ev_matched : option nat     (* Some j = trace index of the matched Send (Recv only); None otherwise *)
}.

Definition init_config : Config :=
  {| cfg_pc := fun _ => 0 ; cfg_chan := fun _ _ => [] |}.

(* functional updates (decidable nat keys) *)
Definition upd_pc (c : Config) (p v : nat) : Config :=
  {| cfg_pc := fun q => if Nat.eqb q p then v else cfg_pc c q ; cfg_chan := cfg_chan c |}.
Definition enqueue (c : Config) (s d : nat) (m : Msg) : Config :=   (* append (FIFO tail) *)
  {| cfg_pc := cfg_pc c ;
     cfg_chan := fun a b => if (Nat.eqb a s && Nat.eqb b d)%bool then cfg_chan c s d ++ [m] else cfg_chan c a b |}.
Definition dequeue (c : Config) (s d : nat) : Config :=            (* drop head *)
  {| cfg_pc := cfg_pc c ;
     cfg_chan := fun a b => if (Nat.eqb a s && Nat.eqb b d)%bool then tl (cfg_chan c s d) else cfg_chan c a b |}.
```

## Component 2 — the step relation (`AsyncSem.v`)

`n` is the trace index the new event will occupy (= number of prior events), so a
`Send` stamps its message with `msg_src_event := n`.

```coq
Inductive step (prog : nat -> list Op) (n : nat) : Config -> Event -> Config -> Prop :=
| step_local : forall c p,
    nth_error (prog p) (cfg_pc c p) = Some Local ->
    step prog n c {| ev_proc:=p; ev_idx:=cfg_pc c p; ev_op:=Local; ev_matched:=None |}
                  (upd_pc c p (S (cfg_pc c p)))
| step_send : forall c p d t,
    nth_error (prog p) (cfg_pc c p) = Some (Send d t) ->
    step prog n c {| ev_proc:=p; ev_idx:=cfg_pc c p; ev_op:=Send d t; ev_matched:=None |}
                  (upd_pc (enqueue c p d {| msg_tag:=t; msg_src_event:=n |}) p (S (cfg_pc c p)))
| step_recv : forall c p s t m rest,
    nth_error (prog p) (cfg_pc c p) = Some (Recv s t) ->
    cfg_chan c s p = m :: rest ->
    msg_tag m = t ->
    step prog n c {| ev_proc:=p; ev_idx:=cfg_pc c p; ev_op:=Recv s t; ev_matched:=Some (msg_src_event m) |}
                  (upd_pc (dequeue c s p) p (S (cfg_pc c p))).
```

## Component 3 — runs: relational + executable, proven equivalent (`AsyncSem.v`)

Relational:
```coq
Inductive run (prog : nat -> list Op) : list Event -> Config -> Prop :=
| run_nil  : run prog [] init_config
| run_step : forall tr c ev c',
    run prog tr c -> step prog (length tr) c ev c' -> run prog (tr ++ [ev]) c'.

Definition valid_run (prog : nat -> list Op) (tr : list Event) : Prop := exists c, run prog tr c.
```

Executable checker (replays a given trace, checking each event is the step its own
fields claim):
```coq
Definition check_event (prog : nat -> list Op) (n : nat) (c : Config) (ev : Event) : option Config :=
  let p := ev_proc ev in
  if Nat.eqb (cfg_pc c p) (ev_idx ev) then
    match nth_error (prog p) (cfg_pc c p), ev_op ev, ev_matched ev with
    | Some Local, Local, None => Some (upd_pc c p (S (cfg_pc c p)))
    | Some (Send d t), Send d' t', None =>
        if (Nat.eqb d d' && Nat.eqb t t')%bool
        then Some (upd_pc (enqueue c p d {| msg_tag:=t; msg_src_event:=n |}) p (S (cfg_pc c p))) else None
    | Some (Recv s t), Recv s' t', Some j =>
        match cfg_chan c s p with
        | m :: _ => if (Nat.eqb s s' && Nat.eqb t t' && Nat.eqb (msg_tag m) t && Nat.eqb (msg_src_event m) j)%bool
                    then Some (upd_pc (dequeue c s p) p (S (cfg_pc c p))) else None
        | [] => None
        end
    | _, _, _ => None
    end
  else None.

Fixpoint run_from (prog : nat -> list Op) (c : Config) (n : nat) (tr : list Event) : option Config :=
  match tr with
  | [] => Some c
  | ev :: tr' => match check_event prog n c ev with
                 | Some c' => run_from prog c' (S n) tr'
                 | None => None
                 end
  end.
Definition valid_run_b (prog : nat -> list Op) (tr : list Event) : bool :=
  match run_from prog init_config 0 tr with Some _ => true | None => false end.

Lemma run_iff :
  forall prog tr, valid_run prog tr <-> valid_run_b prog tr = true.
```
Proof sketch of `run_iff`: `→` by induction on `run` (each `run_step` matches one
`check_event = Some`; note `run` appends at the tail while `run_from` consumes from
the head — prove the generalized statement `run prog tr c → run_from prog
init_config 0 tr = Some c` and conversely via a `run_from`-from-`c`/append lemma).
A helper `run_from_app`/`run_snoc` relating tail-append to the head-fold is the
crux; both directions are structural inductions.

## Component 4 — operational happened-before + metatheorem (`AsyncSem.v`)

```coq
Definition oedge (tr : list Event) (i j : nat) : Prop :=
  (exists ei ej, nth_error tr i = Some ei /\ nth_error tr j = Some ej /\
                 ev_proc ei = ev_proc ej /\ S (ev_idx ei) = ev_idx ej)      (* program order *)
  \/ (exists ej, nth_error tr j = Some ej /\ ev_matched ej = Some i).       (* message order *)

Definition ohb (tr : list Event) : nat -> nat -> Prop := clos_trans nat (oedge tr).
```

Invariant lemmas (by induction on `run`):
```coq
Lemma run_chan_src_lt :                    (* every in-flight message predates the present *)
  forall prog tr c, run prog tr c ->
  forall s d m, In m (cfg_chan c s d) -> msg_src_event m < length tr.

Lemma run_proc_idx_pos_mono :              (* a process's events appear in idx order in the trace *)
  forall prog tr c, run prog tr c ->
  forall i j ei ej, nth_error tr i = Some ei -> nth_error tr j = Some ej ->
    ev_proc ei = ev_proc ej -> ev_idx ei < ev_idx ej -> i < j.
```

Payoff:
```coq
Lemma oedge_forward :
  forall prog tr, valid_run prog tr -> forall i j, oedge tr i j -> i < j.

Theorem ohb_strict_order :
  forall prog tr, valid_run prog tr -> StrictOrder (ohb tr).
```
Proof sketch: `oedge_forward` — program edges use `run_proc_idx_pos_mono`
(`idx i + 1 = idx j ⟹ idx i < idx j ⟹ i < j`); message edges use the fact that a
`Recv` at trace position `j` consumed a channel head whose `msg_src_event = i` was
set at the enqueueing `Send` (position `i`), and `run_chan_src_lt` gives `i < j`.
`ohb = clos_trans oedge ⊆ clos_trans (<) = (<)` (transitivity of `<`), so `ohb` is
irreflexive (no `i < i`) and transitive (`clos_trans`), i.e. a `StrictOrder`.

## Component 5 — examples (`execution/AsyncSemExamples.v`, test-only)

A concrete program/run, e.g. `prog 0 = [Send 1 0]`, `prog 1 = [Recv 0 0]`,
`prog 2 = [Local]`, and a trace `tr` interleaving them (send, then recv, then
local — or send, local, recv). Establish:
- `valid_run_b prog tr = true` by `vm_compute; reflexivity` (executable checker).
- `valid_run prog tr` via `run_iff`.
- `ohb tr 0 1` (the send→recv edge) holds; the `Local` event (proc 2) is
  `ohb`-incomparable to the send (neither `ohb tr · ·` direction), by
  `oedge_forward` (any `ohb` goes forward) + a small case analysis that no edge
  chain links them.

## Files, wiring, testing

- New: `execution/AsyncSem.v` (exported), `execution/AsyncSemExamples.v` (test).
- `execution/dune` + `_CoqProject`: add both (after the OnlineClockLocal entries).
- `execution/Execution.v`: add `AsyncSem` to the `Require Export`.
- `docs/INDEX.md`: a subsection (new "Async operational semantics" group).
- All builds via the wrapper; **zero `Admitted`**; each file < 500 lines; fast `Qed`s
  (the inductions are over `run`/lists; avoid heavy automation).
- `Print Assumptions ohb_strict_order run_iff` recorded (expect axiom-free or only
  standard Stdlib axioms; this slice should be largely constructive).

## Acceptance criteria

1. `Config`/`Event`/`Msg`, `step`, relational `run`/`valid_run`, executable
   `run_from`/`valid_run_b`, and `run_iff` (equivalence). Zero admits.
2. `oedge`/`ohb`, the two run-invariant lemmas, `oedge_forward`, and
   `ohb_strict_order`. Zero admits.
3. Examples: a concrete valid run (checker + relational via `run_iff`), one true
   `ohb` edge, one incomparable pair. Whole-project green; `INDEX.md` updated.

## Out of scope (later slices / not now)

- **No timestamps, no `Synchronized` predicate, no `blo` bridge** (Slices 2/3).
- **No liveness / progress / determinism-of-scheduling** theorems — only that a
  *given* valid run's `ohb` is a partial order. We do not prove runs exist or
  make progress, nor that the scheduler is fair.
- **No FIFO-specific ordering theorem** beyond what `oedge_forward` needs (we do
  not separately prove "messages on a channel are received in send order").
- General async runs are intentionally **not** claimed dim-2; that restriction is
  Slice 2's `Synchronized` predicate.

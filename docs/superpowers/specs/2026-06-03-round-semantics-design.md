# Barrier-round operational semantics + the local clock — Design

**Date:** 2026-06-03
**Branch:** `async-sem` (the work pivoted from fully-async to barrier-round; branch
name kept)
**Goal:** An operational, **primitive-state** model of barrier-synchronized
executions that closes the proof-skeptic's W-2 gap: each process has its own
program `prog p : list Op` and a round counter, and the dim-2 clock is computed
from `nth r (prog p)` — **no `Schedule` projection**. We define the round model,
its happened-before `rhb`, prove it's a partial order, and (reusing the generic
`stamp_iff`) prove `rhb e e' ↔ stamp ≤_prod` with a fully local clock.

**Why barrier-round, not async:** the dim-2 clock characterizes causality only on
barrier-synchronized executions; a general async model would be built and then
restricted back to barriers. Barrier-round bakes synchronization in (lockstep
rounds), so there is no separate `Synchronized` predicate, and the clock proof is
a direct re-instantiation of the proven generic rule. Key simplification: a
`Recv s t` op **names its source**, so the sender id the clock needs is in the
receiver's *own* op — `local_obs` becomes `nth r (prog p)`, needing only `p`'s
primitive program and counter.

**Depends on:** `Execution.Op` (`Op = Local | Send (tgt) (tag) | Recv (src) (tag)`);
`Execution.OnlineClock` (`local_stamp`, `le_lex3`, `le_prod`, `stamp_iff`);
`Execution.OnlineClockLocal` (`stamp_le`); `Posets.PosetClasses` (`IsPoset`);
Stdlib `List`, `Arith`, `Lia`.

## Implementation slices

Likely **two build cycles** (one spec, two plans, or split the plan):
- **A — the model:** `RSys`, `rwf`, valid events, `rhb`, `rhb_IsPoset`, and the
  within-round structural lemmas (resp-comp, rank, bound analogues).
- **B — the clock:** `rclock` from primitive local state, instantiate `stamp_iff`
  to get `rhb_iff_stamp` / `rhb_iff_rclock`, the W-2-closing locality remark,
  examples.

## Component 1 — the round system and well-formedness (`execution/RoundSem.v`)

```coq
Record RSys := { rs_nprocs : nat ; rs_nrounds : nat ; rs_prog : nat -> list Op }.

(* op of process p in round r (default Local out of range; real op for valid events) *)
Definition rop (S : RSys) (p r : nat) : Op := nth r (rs_prog S p) Local.

Definition rvalid (S : RSys) (e : nat * nat) : Prop :=
  fst e < rs_nprocs S /\ snd e < rs_nrounds S.

(* rendezvous compatibility: sends and recvs are mutually matched within a round *)
Definition rwf (S : RSys) : Prop :=
  (forall p, p < rs_nprocs S -> length (rs_prog S p) = rs_nrounds S) /\
  (forall p r d t, p < rs_nprocs S -> r < rs_nrounds S -> rop S p r = Send d t ->
      d < rs_nprocs S /\ rop S d r = Recv p t) /\
  (forall p r s t, p < rs_nprocs S -> r < rs_nrounds S -> rop S p r = Recv s t ->
      s < rs_nprocs S /\ rop S s r = Send p t).
```

Because `rop S p r` is a *single* op, each process sends to ≤1 partner and receives
from ≤1 partner per round — the unique-sender/receiver property is automatic (no
`NoDup` side condition needed, unlike the frontier model).

## Component 2 — happened-before `rhb` and its partial order (`RoundSem.v`)

```coq
(* within-round REALIZED rendezvous edge: p sends to d AND d receives from p, in round r.
   Both conjuncts (not just the Send) make rhb antisymmetric WITHOUT rwf -- an
   unmatched send is not an hb edge. Under rwf the second conjunct is implied. *)
Definition redge (S : RSys) (p d r : nat) : Prop :=
  (exists t, rop S p r = Send d t) /\ (exists t, rop S d r = Recv p t).

(* within-round order: equality or one sender->receiver realized edge *)
Definition rhb_same (S : RSys) (e e' : nat * nat) : Prop :=
  e = e' \/ (snd e = snd e' /\ redge S (fst e) (fst e') (snd e)).

(* the barrier order: lower round entirely below higher round; within a round, rhb_same *)
Definition rhb (S : RSys) (e e' : nat * nat) : Prop :=
  snd e < snd e' \/ (snd e = snd e' /\ rhb_same S e e').

(* carrier of valid events *)
Definition REvent (S : RSys) : Type := { e : nat * nat | rvalid S e }.
Definition rhb_sub (S : RSys) (x y : REvent S) : Prop := rhb S (proj1_sig x) (proj1_sig y).

#[export] Instance rhb_IsPoset : forall S, IsPoset (REvent S) (rhb_sub S).
```
`rhb_IsPoset` (refl/antisym/trans) is **unconditional** (no `rwf` needed), thanks to
the realized edge. Antisymmetry: mutual same-round edges `x→y` and `y→x` would force
`rop (fst x) r` to be both `Send (fst y) _` and `Recv (fst y) _` — impossible (a
`Send` op is not a `Recv` op). Transitivity within a round is near-vacuous: an edge
`x→y` makes `fst y` a receiver (`rop (fst y) r = Recv _ _`), so `fst y` cannot also be
the sender of an edge `y→z`; hence edges do not chain (only the `y=z` case applies).
Across rounds it is `snd e < snd e'` (transitivity of `<`). Event equality uses
`proof_irrelevance` on the validity proofs. Mirrors `blo_IsPoset`.

## Component 3 — clock fields and structural lemmas (`RoundSem.v`)

```coq
Definition rlay  (S : RSys) (x : REvent S) : nat := snd (proj1_sig x).
Definition rcomp (S : RSys) (x : REvent S) : nat :=
  match rop S (fst (proj1_sig x)) (snd (proj1_sig x)) with Recv s _ => s | _ => fst (proj1_sig x) end.
Definition rstep (S : RSys) (x : REvent S) : nat :=
  match rop S (fst (proj1_sig x)) (snd (proj1_sig x)) with Recv _ _ => 1 | _ => 0 end.
```

The five `stamp_iff` obligations for `R := rhb_sub S` under `rwf S`:
- **barrier** `rlay x < rlay y -> rhb_sub`: first disjunct of `rhb`. (lemma `rhb_barrier`)
- **resp-lay** `rhb_sub x y -> rlay x <= rlay y`: from `rhb`'s definition. (lemma `rhb_resp_lay`)
- **resp-comp** `rhb_sub x y -> rlay x = rlay y -> rcomp x = rcomp y`: within a round,
  `rhb_same` is `x=y` (trivial) or a message edge `p->d`; then `rcomp` of the sender
  `p` (op `Send d _`) is `p`, and `rcomp` of the receiver `d` (op `Recv p _` by `rwf`)
  is `p` — equal. (lemma `rcomp_eq_of_rhb`)
- **rank** `rlay x = rlay y -> rcomp x = rcomp y -> (rhb_sub x y <-> rstep x <= rstep y)`:
  same round, same comp `c`. `rstep` is `Recv?1:0`; cases mirror `blo_rank`
  (step 0/0 ⇒ both are the pid-`c` non-receiver ⇒ same process ⇒ equal; 0/1 ⇒ sender
  `c` → its receiver ⇒ message edge ⇒ `rhb`; 1/1 ⇒ both receive from `c` ⇒ unique
  sender ⇒ equal; 1/0 ⇒ `1<=0` false). (lemma `rhb_rank`)
- **bound** `rcomp x <= rs_nprocs S - 1`: `rcomp` is the own pid (`< nprocs` by
  validity) or a `Recv` source (`< nprocs` by `rwf`). (lemma `rcomp_lt_nprocs`)

These are the round-model analogues of `DisjointChainsDim`'s `fb_comp` lemmas, but
*shorter*: matching is read straight off `rwf` (no `desugar`/rank machinery).

## Component 4 — the local clock and the characterization (`RoundSem.v`)

```coq
(* the clock from PRIMITIVE local state: p's own program at counter r. Schedule-free. *)
Definition rclock (S : RSys) (p r : nat) : (nat*nat*nat) * (nat*nat*nat) :=
  local_stamp (rs_nprocs S) p r (rop S p r).   (* rop S p r = nth r (rs_prog S p) Local *)

(* instantiate the generic rule *)
Theorem rhb_iff_stamp :
  forall S, rwf S -> 0 < rs_nprocs S -> forall x y : REvent S,
    rhb_sub S x y <->
    le_prod (rs_nprocs S - 1)
      (rlay S x)(rcomp S x)(rstep S x)(rlay S y)(rcomp S y)(rstep S y).
(* via: apply (stamp_iff (rhb_sub S) (rlay S)(rcomp S)(rstep S)(rs_nprocs S -1)); discharge the 5 lemmas. *)

(* the headline: causality via the schedule-free local clock *)
Theorem rhb_iff_rclock :
  forall S, rwf S -> 0 < rs_nprocs S -> forall x y : REvent S,
    rhb_sub S x y <->
    stamp_le (rclock S (fst (proj1_sig x)) (snd (proj1_sig x)))
             (rclock S (fst (proj1_sig y)) (snd (proj1_sig y))).
```
`rhb_iff_rclock` proof: `rclock S p r = local_stamp (nprocs) p r (rop S p r)`, whose
three coordinates are exactly `rlay`/`rcomp`/`rstep` of the event `(p,r)` (by a
`rclock_components` lemma, `destruct (rop …)`); then `stamp_le (rclock x) (rclock y)`
unfolds to `le_prod …` (as in `stamp_le_stamp`), and `rhb_iff_stamp` closes it.

**W-2 closed:** `rclock S p r` reads only `rs_nprocs S`, `p`, `r`, and
`rop S p r = nth r (rs_prog S p) Local` — i.e. process `p`'s **own primitive
program** and its **own counter** `r`. No frontier list, no `op_at`/`desugar`, no
projection of a shared schedule. This is exactly the operational locality the
W-2 finding asked for.

## Component 5 — examples (`execution/RoundSemExamples.v`, test-only)

A concrete `RSys`: `nprocs := 3`, `nrounds := 1`, programs `prog 0 = [Send 1 0]`,
`prog 1 = [Recv 0 0]`, `prog 2 = [Local]` (proc 0 → proc 1; proc 2 idle).
- `rwf` for this system, by `vm_compute`/case analysis.
- `rclock` literals via `vm_compute` (sender `((0,0,0),(0,2,0))`, receiver
  `((0,0,1),(0,2,1))`, idle `((0,2,0),(0,0,0))` — matching the `OnlineClock` story).
- `rhb_sub` of the sender→receiver pair (a message edge), and incomparability of
  the idle event with the sender, both via `rhb_iff_rclock` / directly.

## Files, wiring, testing

- New: `execution/RoundSem.v` (exported), `execution/RoundSemExamples.v` (test).
- `execution/dune` + `_CoqProject`: add both (after the OnlineClockLocal entries).
- `execution/Execution.v`: add `RoundSem` to the `Require Export`.
- `docs/INDEX.md`: a subsection (new "Operational round model" group);
  `execution/DIM2_CLOCK.md` §6: record that an operational primitive-state model now
  carries the clock (W-2 closed for the round model), narrowing the open item.
- All builds via the wrapper; **zero `Admitted`**; each file < 500 lines; fast `Qed`s.
- `Print Assumptions rhb_iff_rclock` recorded (expect the four standard axioms via
  `stamp_iff`; the round model itself adds none).

## Acceptance criteria

1. `RSys`/`rop`/`rvalid`/`rwf`, `rhb`/`rhb_sub`/`rhb_IsPoset`. Zero admits.
2. `rlay`/`rcomp`/`rstep`, the five structural lemmas, `rhb_iff_stamp`. Zero admits.
3. `rclock`, `rclock_components`, `rhb_iff_rclock` (causality via the schedule-free
   local clock). Zero admits.
4. Examples (`rwf`, `rclock` literals, a message edge + an incomparable pair).
   Whole-project green; `INDEX.md` + `DIM2_CLOCK.md` updated.

## Out of scope / honestly noted

- **Barrier-round only.** This is lockstep synchronization (the regime where the
  dim-2 clock applies). Fully-asynchronous executions, and the proof that a clock
  fails / vector clocks are needed there, are NOT modeled (deliberately dropped in
  the pivot from async).
- **No explicit message channels / in-flight buffers.** Because a `Recv` op names
  its source and rounds are synchronous rendezvous, the sender id the clock needs is
  in the receiver's own op; persistent channels add nothing here. (If a future slice
  wants delayed delivery / channels, that is separate.)
- **No liveness/progress/scheduling.** We characterize the order of a well-formed
  round system; we do not model run construction, fairness, or termination.
- **Relationship to `blo`/`Schedule` not formalized.** A bridge `RSys ↔ Schedule`
  with `rhb ≈ blo` is possible but unneeded: `rhb_iff_rclock` is proven directly via
  `stamp_iff`, independently of the `Schedule` model.

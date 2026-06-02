# Online dim-2 clock: a computable 2-coordinate stamp characterizing `blo` — Design

**Date:** 2026-06-02
**Branch:** `online-clock`
**Goal:** turn the abstract `L1`/`L2` dim-2 realizer (`BarrierExecDim.v`) into a
**concrete, computable timestamp** — a function `stamp` assigning each event a
pair of integer triples — and prove it *characterizes* the barrier order:
`blo s x y ⟺ stamp x ≤_prod stamp y`. Two integers' worth of structure per
event for any N, with the causality test using **only the emitted integers**
(never `hb`). This is the soundness half of the project's
[north-star goal](../../../CLAUDE.md): a logical clock below vector clocks' Θ(N).
See the analysis in [`execution/DIM2_CLOCK.md`](../../../execution/DIM2_CLOCK.md).
**Depends on:** `Dimension.DimDefs`; `Execution.BarrierExecDim` (`blo`,
`blo_IsPoset`); `Execution.DisjointChainsDim` (`fb_comp`, `fb_comp_eq_of_hb`,
`hb_or_of_fb_comp_eq`, `hb_same_index_msg`, `fb_comp_send/recv/local`,
`event_pid_lt`); `Execution.ScheduleWf` (`wf_schedule`, `wf_frontier`,
`op_for_*_iff`); `Execution.Schedule`/`Op`; Stdlib `Arith`/`Lia`.

## What "characterization" means (and what it does not)

The Coq theorem proves `R x y ⟺ stamp x ≤_prod stamp y` — the order is exactly
the product of two lexicographic orders on integer triples. That is the
**soundness** of the clock. True distributed **online locality** (each field
derivable from a process's local history + received message payload) is argued in
prose (§5); it is not part of the machine-checked statement. No frontier
`Schedule` produces a within-layer chain longer than 2, so `step ≥ 2` is
exercised only by an abstract example (§4), not by any real barrier execution.

## Component 1 — generic `stamp_iff` (`execution/OnlineClock.v`)

Carrier-generic core, parameterized over any poset plus three integer fields and
a bound. No finiteness needed; the within-layer rank is *given*, not computed.

```coq
(* lexicographic order on nat triples *)
Definition le_lex3 (a b : nat * nat * nat) : Prop :=
  let '(a1,a2,a3) := a in let '(b1,b2,b3) := b in
  a1 < b1 \/ (a1 = b1 /\ (a2 < b2 \/ (a2 = b2 /\ a3 <= b3))).

Definition T1 (lay comp step : nat) : nat*nat*nat := (lay, comp, step).
Definition T2 (B lay comp step : nat) : nat*nat*nat := (lay, B - comp, step).

Definition le_prod (B : nat)
  (lx cx sx ly cy sy : nat) : Prop :=
  le_lex3 (T1 lx cx sx) (T1 ly cy sy) /\ le_lex3 (T2 B lx cx sx) (T2 B ly cy sy).

Theorem stamp_iff :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (lay comp step : A -> nat) (B : nat),
    (forall x y, lay x < lay y -> R x y) ->                                   (* 1 barrier   *)
    (forall x y, R x y -> lay x <= lay y) ->                                  (* 2 resp-lay  *)
    (forall x y, R x y -> lay x = lay y -> comp x = comp y) ->                (* 3 resp-comp *)
    (forall x y, lay x = lay y -> comp x = comp y ->
                 (R x y <-> step x <= step y)) ->                             (* 4 rank      *)
    (forall e, comp e <= B) ->                                               (* 5 bound     *)
    forall x y, R x y <-> le_prod B (lay x)(comp x)(step x)(lay y)(comp y)(step y).
```

Proof sketch (pure case analysis on `lay`/`comp`, `lia` throughout):
- **(→)** Assume `R x y`. By (2) `lay x ≤ lay y`.
  - `lay x < lay y`: both `T1`,`T2` decided by first coord — `le_lex3` holds on both. ✓
  - `lay x = lay y`: by (3) `comp x = comp y`, so `B - comp x = B - comp y` and by (4)
    `step x ≤ step y`. Both triples tie on coords 1–2 and satisfy coord 3. ✓
- **(←)** Assume `le_prod`. Trichotomy on `lay x` vs `lay y`:
  - `lay x < lay y`: (1) gives `R x y`. ✓
  - `lay x > lay y`: `T1` first coord `lay x > lay y` contradicts `le_lex3 (T1 x)(T1 y)`. ✗ (excluded)
  - `lay x = lay y`: then `le_lex3` on `T1` forces `comp x < comp y ∨ (comp x = comp y ∧ step x ≤ step y)`,
    and on `T2` forces `B-comp x < B-comp y ∨ (… )` i.e. `comp x > comp y ∨ (comp x = comp y ∧ …)`.
    The strict branches are mutually exclusive (`comp x < comp y` ∧ `comp x > comp y` impossible,
    using (5) so `B - ·` is order-reversing on `[0,B]`), leaving `comp x = comp y ∧ step x ≤ step y`,
    whence (4) gives `R x y`. ✓

Notes: axiom (4) subsumes the old "within-layer is a chain" condition of
`layered_chains_dim_le2` (nat totality on `step` ⟹ comparability) and yields
antisymmetry for free (`step x = step y ⟹ R x y ∧ R y x ⟹ x = y`). The `B - comp`
reversal is faithful only because of (5) (`comp ≤ B`); `lia` needs `comp x ≤ B`
and `comp y ≤ B` in the `lay x = lay y` branch.

## Component 2 — barrier instance `blo_iff_stamp` (`execution/OnlineClock.v`)

Instantiate the generic theorem on `blo`:

```coq
Definition clk_lay  (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  snd (proj1_sig x).
Definition clk_comp (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  fb_comp s (proj1_sig x).
Definition clk_step (s : Schedule) (x : ep_carrier (exec_of_schedule s)) : nat :=
  match op_at (desugar_prog s) (fst (proj1_sig x)) (snd (proj1_sig x)) with
  | Some (Recv _ _) => 1 | _ => 0 end.

(* the bound: fb_comp is always a valid pid, hence < sch_nprocs s *)
Lemma fb_comp_lt_nprocs :
  forall s, wf_schedule s -> forall x : ep_carrier (exec_of_schedule s),
    clk_comp s x < sch_nprocs s.

Theorem blo_iff_stamp :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
  forall x y,
    blo s x y <->
    le_prod (sch_nprocs s - 1)
      (clk_lay s x)(clk_comp s x)(clk_step s x)
      (clk_lay s y)(clk_comp s y)(clk_step s y).
```

Discharge of the five generic hypotheses for `R := blo s`:
- **1 barrier** `clk_lay x < clk_lay y → blo`: directly the first disjunct of `blo`.
- **2 resp-lay** `blo x y → clk_lay x ≤ clk_lay y`: from `blo`'s definition (`idx <` or `idx =`).
- **3 resp-comp** `blo x y → clk_lay x = clk_lay y → clk_comp x = clk_comp y`: within a layer
  `blo` reduces to `ep_order`; apply `fb_comp_eq_of_hb`.
- **4 rank** within `(lay,comp)`: `blo x y ↔ clk_step x ≤ clk_step y`. Within a layer +
  same `fb_comp`, `hb_or_of_fb_comp_eq` gives comparability; the comparable pair is a single
  `sender → receiver` message (`hb_same_index_msg`), so the `hb`-min is a `Send`/`Local`
  (`clk_step = 0`) and the `hb`-max is the `Recv` (`clk_step = 1`); `≤2`-length chains make
  `R ↔ step ≤` a finite case check (`0≤0,0≤1,1≤1` vs the unique-sender argument
  `find_fst_unique` for the `1,1` and `0,0` collapses to equality).
- **5 bound** `clk_comp ≤ sch_nprocs s - 1`: `fb_comp_lt_nprocs` + `0 < nprocs`.

`fb_comp_lt_nprocs`: `fb_comp` returns either `fst (proj1_sig x)` (`< nprocs` by
`event_pid_lt`) or a `Recv` source; the source is an in-range endpoint of a
`wf_frontier` pair (`op_for_recv_iff` + `wf_frontier` endpoint bound).

## Component 3 — the readable stamp wrapper (`execution/OnlineClock.v`)

A tuple-valued convenience so examples can `vm_compute` a literal timestamp and a
boolean compare; thin definitional layer over Component 2.

```coq
Definition stamp (s : Schedule) (x : ep_carrier (exec_of_schedule s))
  : (nat*nat*nat) * (nat*nat*nat) :=
  let l := clk_lay s x in let c := clk_comp s x in let st := clk_step s x in
  (T1 l c st, T2 (sch_nprocs s - 1) l c st).
(* blo_iff_stamp restated as: blo s x y <-> (le_lex3 (fst(stamp x))(fst(stamp y))
                                            /\ le_lex3 (snd(stamp x))(snd(stamp y))) *)
```

## Component 4 — examples (`execution/OnlineClockExamples.v`, test-only)

1. **`s_bar5`** (the N=5 barrier, from `BarrierExecDimExamples.v`): instantiate
   `blo_iff_stamp`; `vm_compute` the stamps of two layer-0 events and check they
   are `le_prod`-incomparable (mirrors `bar5_incomp`), and that a layer-0 event's
   stamp is `≤_prod` a layer-1 event's (the barrier).
2. **A messaged barrier schedule** (e.g. `{ nprocs:=3; frontiers:=[[(0,1)]] }`):
   show the message pair `(0,0)→(1,0)` has `clk_step 0 / 1` and stamps ordered,
   while `(2,0)` is incomparable — a `vm_compute` of real timestamp triples.
3. **Abstract length-3 chain** exercising the *generic* `stamp_iff` with
   `step ∈ {0,1,2}`: a 4-element `A` (one layer, one component, a 3-chain `u<v<w`
   plus an isolated `z` in a different component), `lay := fun _ => 0`,
   `comp u=comp v=comp w := 0`, `comp z := 1`, `step` the chain rank, `B := 1`.
   Prove the five hypotheses by `decide`/`lia` and conclude `R ↔ le_prod`,
   demonstrating the clock for chains beyond what any frontier model yields.

## Files, wiring, testing

- New: `execution/OnlineClock.v` (exported), `execution/OnlineClockExamples.v` (test).
- `execution/dune` + `_CoqProject`: add both. `execution/Execution.v`: export `OnlineClock`.
- `docs/INDEX.md`: a subsection under the execution dimension entries; link from
  `execution/DIM2_CLOCK.md` §6 (replace "open / offline only" with the new theorem).
- Whole-project green via the wrapper; **zero `Admitted`**; each file <500 lines;
  each `Qed` <5 min (the generic proof is `lia`-bound; the instance reuses
  existing lemmas — both should be fast).
- `Print Assumptions stamp_iff blo_iff_stamp` recorded (expect standard
  classical/proof-irrelevance only; the generic core should be axiom-light).

## Acceptance criteria

1. `stamp_iff` (generic, no finiteness; integer-only comparison). Zero admits.
2. `fb_comp_lt_nprocs` and `blo_iff_stamp` (`blo s x y ⟺ le_prod …`), for any N.
   Zero admits.
3. `stamp` wrapper + all three examples (`s_bar5`, messaged-3, abstract 3-chain),
   with at least one literal `vm_compute` of a timestamp pair. Whole-project
   green; `INDEX.md` + `DIM2_CLOCK.md` updated.

## Out of scope / honestly noted

- **Online locality is prose, not Coq.** The theorem is the characterization
  (soundness). A proved operational model where each process maintains
  `(barrier, comp, step)` from local state + message payloads — `barrier` a
  shared counter incremented at each full rendezvous (all processes agree because
  the barrier is total), `comp`/`step` carried in messages — is a *follow-up*
  branch. This spec deliberately stops at the computable stamp + iff.
- **`step ∈ {0,1}` for all real barrier executions.** General `step` rank only
  matters for the abstract example / future non-frontier layered models.
- **`blo` is the target order**, i.e. synchronization modeled as a barrier
  primitive (`blo ⊇ hb`). Arbitrary pairwise-message executions are *not* dim-2
  and get no 2-coordinate clock — unchanged from `DIM2_CLOCK.md` §5.
- No refactor of `BarrierExecDim.v` to expose its internal `L1`/`L2`; `stamp_iff`
  is proved directly rather than bridged to those `set`-local relations.

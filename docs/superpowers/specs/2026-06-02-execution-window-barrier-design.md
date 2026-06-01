# Thick (window) barrier — Design

**Date:** 2026-06-02
**Branch:** `execution_poset`
**Depends on:** `execution/ConnSync.v` (`mk_event`, `event_eq_of_proj`, `prog_step`, `msg_step`), `execution/SyncShape.v` (`event_index_lt`), `execution/ScheduleWf.v` (`wf_schedule`), `execution/Edges.v` (`hb_trans`).

## Goal & the proven limitation

A **window** of consecutive frontiers `[a,b)` acts as one logical synchronization barrier:
under window-connectivity, every event before index `a` precedes every event at/after index
`b`, **for arbitrary process count**. This lifts the per-transition reachability cap of
`ConnSync.StepConnected` (≈≤4 synchronized processes per single transition).

**Why a window, not a single cut (recorded fact):** a `hb`-path has non-decreasing index, so a
path from index `i` to `i+1` may use only frontiers `i`, `i+1`; each is a partial matching
(one directed hop per process), so the reachable set from `(p,i)` into level `i+1` is
`{p, σ_i(p), σ_{i+1}(p), σ_{i+1}(σ_i(p))}` — at most 4 processes. Hence the **consecutive**
barrier (`idx y = S (idx x)`, required by `FullySynchronizing`) is unattainable for `n>4` with
matching frontiers. A window of `b-a` frontiers provides `b-a` hops, removing the cap.

## Definitions (`execution/WindowSync.v`)

```coq
(* one forward window-step at frontier k: stay on p, or cross a sync pair p->q *)
Definition window_step (s : Schedule) (k p q : nat) : Prop :=
  p = q \/ List.In (p, q) (nth k (sch_frontiers s) []).

(* reach from (p, a) to (q, a + m) using m window-steps at levels a, a+1, …, a+m-1 *)
Fixpoint window_reach (s : Schedule) (a p m q : nat) : Prop :=
  match m with
  | 0 => p = q
  | S m' => exists r, window_reach s a p m' r /\ window_step s (a + m') r q
  end.

Definition WindowConnected (s : Schedule) (a b : nat) : Prop :=
  forall p q, p < sch_nprocs s -> q < sch_nprocs s -> window_reach s a p (b - a) q.
```

## Lemmas

```coq
(* program-order chain: same process, i <= k, both valid *)
Lemma prog_chain :
  forall s p i k (Hp : p < sch_nprocs s)
         (Hi : i < length (sch_frontiers s)) (Hk : k < length (sch_frontiers s)),
    i <= k ->
    ep_order (exec_of_schedule s) (mk_event s p i Hp Hi) (mk_event s p k Hp Hk).
(* induction on k; base i=k via poset_refl, step via prog_step + hb_trans *)

(* a window_reach lifts to hb between the endpoint events *)
Lemma window_reach_hb :
  forall s, wf_schedule s -> forall m a p q
    (Hp : p < sch_nprocs s) (Hq : q < sch_nprocs s)
    (Ha : a < length (sch_frontiers s)) (Hb : a + m < length (sch_frontiers s)),
    window_reach s a p m q ->
    ep_order (exec_of_schedule s) (mk_event s p a Hp Ha) (mk_event s q (a + m) Hq Hb).
(* induction on m: m=0 is p=q (event_eq_of_proj + refl); S m' decomposes the witness r,
   IH gives (p,a)->(r,a+m'), then window_step s (a+m') r q gives (r,a+m')->(q,a+S m')
   by case (stay => prog_step, cross => msg_step then prog_step) *)
```

### Main theorem
```coq
Definition idx {s} (x : ep_carrier (exec_of_schedule s)) : nat := snd (proj1_sig x).

Theorem window_connected_barrier :
  forall s, wf_schedule s -> 0 < sch_nprocs s ->
    forall a b, a < b -> b <= length (sch_frontiers s) ->
    WindowConnected s a b ->
    forall x y : ep_carrier (exec_of_schedule s),
      snd (proj1_sig x) < a -> b <= snd (proj1_sig y) ->
      ep_order (exec_of_schedule s) x y.
```
Proof: let `px = fst (proj1_sig x)`, `py = fst (proj1_sig y)`, `ix = snd (proj1_sig x)`,
`iy = snd (proj1_sig y)`; validity gives `px,py < nprocs`, `ix,iy < len`. Indices `a` and `b`
are `< len` (`a < b ≤ len` and `b ≤ iy < len`). Compose three `hb` legs:
`x = (px,ix) → (px,a)` (`prog_chain`, `ix < a`), `(px,a) → (py,b)` (`window_reach_hb` with
`WindowConnected px py`, `a + (b-a) = b`), `(py,b) → (py,iy)` (`prog_chain`, `b ≤ iy`); rewrite
`x`/`y` to `mk_event` via `event_eq_of_proj`; chain by `hb_trans`.

### Relating to ConnSync (the W=1 specialization)
`StepConnected s` (ConnSync) ⟹ `WindowConnected s k (S (S k))`-style barriers per transition is
the existing result; conversely a `window_step` at one frontier is the `p=q`/single-cross core
of `StepConnected`'s witness. Provide a short note/`Remark` connecting them (no heavy lemma
required); the value is `window_connected_barrier` for arbitrary `n`.

## Example (`execution/WindowSyncExamples.v`, test-only)

A concrete **gather/scatter** window over `n` processes is the natural arbitrary-`n` witness, but
a fully generic-in-`n` `WindowConnected` proof is heavy. Scope the example to a small concrete
schedule that genuinely exercises a `b-a ≥ 2` window with all-pairs mixing — a 3-process
gather-then-scatter (`coordinator 0`): frontiers `[(1,0)];[(2,0)];[(0,1)];[(0,2)]` (procs 1,2
send to 0, then 0 sends to 1,2). Prove `wf_schedule`, `WindowConnected s 0 4` (all 9 ordered
pairs via `window_reach` paths through coordinator 0), and instantiate
`window_connected_barrier` to get e.g. `(p,0) hb (q,3)` for all `p,q` — demonstrating
all-3-process synchronization across the window (which a single transition could NOT do beyond a
pair). If the generic 9-pair proof is fiddly, fall back to the 2-process `s_demo` window `[0,2)`.

## Files, wiring, testing
- New: `execution/WindowSync.v` (exported), `execution/WindowSyncExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add both. `execution/Execution.v`: export `WindowSync`.
- `docs/INDEX.md`: a `WindowSync.v` subsection, recording the consecutive-cut impossibility
  argument (≤4 reach) and the window lift.
- Whole-project green; **zero `Admitted`**; files <500 lines; each `Qed` <5 min.
- `Print Assumptions window_connected_barrier` recorded.

## Acceptance criteria
1. `WindowSync.v`: `window_step`, `window_reach`, `WindowConnected`, `prog_chain`,
   `window_reach_hb`, `window_connected_barrier`. Zero admits.
2. `WindowSyncExamples.v`: a concrete `WindowConnected` witness + an instantiated
   cross-window `hb` (3-process gather/scatter, or `s_demo` fallback). Zero admits.
3. Whole-project green; `Execution.v` exports `WindowSync`; INDEX updated (incl. the
   impossibility note); assumptions recorded.

## Out of scope
Transformation B; a fully generic-in-`n` `WindowConnected` schedule family proof; a Coq proof of
the universal consecutive-cut impossibility (documented in prose; the ≤4 reach bound is the
argument); any dimension payoff (the IsFullySync prefix-cut still hits the adjacent bottleneck —
deliberately not attempted here).

# Execution Poset Core Model (Sub-project A) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Coq-specific note:** This is research-grade Coq. **Definitions, record fields, and theorem statements in this plan are authoritative — implement them verbatim.** Proof *bodies* for the non-trivial lemmas give a strategy + named sub-lemmas, not a guaranteed tactic script; develop the exact tactics at execution time following the `coq-fast-compile` and `long-running-formalization` skills. "Test passes" = **the file builds** through the wrapper. Every build call:
> `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2`
> (exit 0 = pass; 124 = timeout → split the file; 137 = OOM → drop to `-j1`). Keep each `.v` < 500 lines and each `Qed` < 5 min.

**Goal:** A finite, dimension-ready Coq model of execution posets (N process-chains + message passing), describable both via high-level *rules* (synchronization schedule → operation sequence) and via an explicit *edge set*, with theorems that all three routes denote the same poset.

**Architecture:** New `execution/` Coq library (`-R execution Execution`). Carrier = a dependent-pair event type realized as a `nat*nat` subset `{ x | Valid x }` so the existing `cardinal_subtype_full` helper gives finiteness. The execution order is `clos_refl_trans` of a direct-causality edge relation (intra-process successor ∪ matched send→recv). Acyclicity is structural: every construction carries a `rank : Event → nat` strictly increasing along edges (supplied by the Schedule's global step order), so `IsPoset` antisymmetry needs no external `IsAcyclic` hypothesis.

**Tech Stack:** Coq/Rocq 9.1, Stdlib `Ensembles`/`Finite_sets`/`Relation_Operators` (`clos_refl_trans`), project libs `Posets.PosetClasses`, `Posets.FinitePoset`, `Posets.dimension`. Builds via `.claude/scripts/timed-build.sh`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/dune` | Coq theory `Execution`, deps `Posets Stdlib`, module list. |
| `execution/Op.v` | `Pid`, `Tag`, `Op`, `Program` record, `proc_len`, `wf_program`. |
| `execution/Event.v` | `Valid` predicate, `Event` carrier (`nat*nat` subset), decidable eq, `all_events` enumeration. |
| `execution/Finite.v` | `valid_cardinal` then `event_cardinal : cardinal Event (Full_set Event) (total prog)` via `cardinal_subtype_full`. |
| `execution/Edges.v` | `edge` relation (program order ∪ matched message), `hb := clos_refl_trans`, refl/trans facts. |
| `execution/Rank.v` | `RankedProgram` (Program + `rank` + `rank_edge_mono`); `hb`→`rank ≤`, `Strict`→`<`. |
| `execution/Poset.v` | `IsPoset Event hb`, `IsFinitePoset Event hb total`, the `ExecPoset` bundle record. |
| `execution/Schedule.v` | `Schedule`, `desugar : Schedule → RankedProgram`, `wf_schedule`, faithfulness + schedule≡program agreement. |
| `execution/FromEdges.v` | `from_edges` constructor (explicit events+edges+rank) + edge-set agreement theorem. |
| `execution/Examples.v` | N=3 and one mΨ(4,5) execution, built via schedule **and** edge set, equality lemma + sanity facts. |
| `execution/Execution.v` | Aggregator: `Require Export` all of the above. |
| `_CoqProject` | Add `-R execution Execution` block listing the files. |

`Event`, `edge`, `hb`, `rank`, `Program`, `RankedProgram`, `ExecPoset`, `desugar`, `from_edges` are the canonical names — use them exactly across all files.

---

## Task 0: Scaffold the `execution/` library

**Files:**
- Create: `execution/dune`, `execution/Execution.v`
- Modify: `_CoqProject`

- [ ] **Step 1: Create `execution/dune`**

```lisp
(coq.theory
 (name Execution)
 (package playground)
 (theories Posets Stdlib)
 (modules
  Op
  Event
  Finite
  Edges
  Rank
  Poset
  Schedule
  FromEdges
  Examples
  Execution))
```

- [ ] **Step 2: Create a minimal `execution/Execution.v`**

```coq
(* Execution poset framework — aggregator. *)
(* Submodule exports are added as each lands. *)
```

- [ ] **Step 3: Add the library to `_CoqProject`**

Append after the `happenedBefore/...` block:

```
-R execution Execution

execution/Op.v
execution/Event.v
execution/Finite.v
execution/Edges.v
execution/Rank.v
execution/Poset.v
execution/Schedule.v
execution/FromEdges.v
execution/Examples.v
execution/Execution.v
```

- [ ] **Step 4: Verify the empty theory builds**

Run: `bash .claude/scripts/timed-build.sh 120 execution/Execution.vo 2`
Expected: exit 0 (an empty `.v` compiles).

- [ ] **Step 5: Commit**

```bash
git add execution/dune execution/Execution.v _CoqProject
git commit -m "scaffold execution/ library"
```

---

## Task 1: Programs and well-formedness (`Op.v`)

**Files:** Create `execution/Op.v`

- [ ] **Step 1: Write the types and `wf_program` (the "spec under test")**

```coq
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition Pid := nat.
Definition Tag := nat.

(* One operation = one event in a process's local chain. *)
Inductive Op : Type :=
  | Local
  | Send (target : Pid) (tag : Tag)
  | Recv (from   : Pid) (tag : Tag).

(* A program: [procs] is per-process operation lists, process p = nth p procs. *)
Record Program := { procs : list (list Op) }.

Definition nprocs (P : Program) : nat := length (procs P).
Definition proc_ops (P : Program) (p : Pid) : list Op := nth p (procs P) [].
Definition proc_len (P : Program) (p : Pid) : nat := length (proc_ops P p).

(* op at (p,i), if present *)
Definition op_at (P : Program) (p i : Pid) : option Op := nth_error (proc_ops P p) i.

(* A send at (p,i) to q with tag t is *matched* by the recv at (q,j):
   op_at P p i = Some (Send q t) and op_at P q j = Some (Recv p t). *)
Definition matched (P : Program) (p i q j : nat) (t : Tag) : Prop :=
  op_at P p i = Some (Send q t) /\ op_at P q j = Some (Recv p t).

(* Well-formedness: every Recv has exactly one matching Send and vice versa,
   and targets are in range. Stated as a record so callers can use fields. *)
Record wf_program (P : Program) : Prop := {
  wf_send_targets :
    forall p i q t, op_at P p i = Some (Send q t) -> q < nprocs P;
  wf_recv_sources :
    forall q j p t, op_at P q j = Some (Recv p t) -> p < nprocs P;
  (* each recv matched by a unique send *)
  wf_recv_matched :
    forall q j p t, op_at P q j = Some (Recv p t) ->
      exists! i, op_at P p i = Some (Send q t);
  (* each send matched by a unique recv *)
  wf_send_matched :
    forall p i q t, op_at P p i = Some (Send q t) ->
      exists! j, op_at P q j = Some (Recv p t)
}.
```

- [ ] **Step 2: Build to verify it compiles**

Run: `bash .claude/scripts/timed-build.sh 120 execution/Op.vo 2`
Expected: exit 0.

- [ ] **Step 3: Commit**

```bash
git add execution/Op.v
git commit -m "feat(execution): Program syntax and well-formedness"
```

---

## Task 2: The finite event carrier (`Event.v`)

**Files:** Create `execution/Event.v`

- [ ] **Step 1: Define the carrier as a `nat*nat` subset + its enumeration**

```coq
From Stdlib Require Import List Arith Lia Ensembles Finite_sets.
From Execution Require Import Op.
Import ListNotations.

Section Carrier.
  Context (P : Program).

  (* (p,i) is a valid event iff p is a real process and i indexes one of its ops *)
  Definition Valid (pi : nat * nat) : Prop :=
    fst pi < nprocs P /\ snd pi < proc_len P (fst pi).

  Definition ValidSet : Ensemble (nat * nat) := fun pi => Valid pi.

  (* Carrier type: dependent pair (process, index) carrying its validity proof. *)
  Definition Event : Type := { pi : nat * nat | In (nat*nat) ValidSet pi }.

  Definition ev_pid (e : Event) : Pid := fst (proj1_sig e).
  Definition ev_idx (e : Event) : nat := snd (proj1_sig e).

  (* Total number of events. *)
  Definition total : nat := list_sum (map (proc_len P) (seq 0 (nprocs P))).

  (* Explicit enumeration of every valid (p,i) as raw pairs. *)
  Definition raw_events : list (nat * nat) :=
    flat_map (fun p => map (fun i => (p, i)) (seq 0 (proc_len P p)))
             (seq 0 (nprocs P)).
End Carrier.
```

- [ ] **Step 2: Prove decidable equality + the enumeration's basic facts (statements)**

Add inside / after the section (use `P` explicit):

```coq
Lemma raw_events_NoDup : forall P, NoDup (raw_events P).
(* strategy: flat_map of NoDup maps with disjoint p-blocks; induction on seq. *)

Lemma raw_events_spec : forall P pi, List.In pi (raw_events P) <-> Valid P pi.
(* strategy: in_flat_map + in_map_iff + in_seq, then unfold Valid. *)

Lemma raw_events_length : forall P, length (raw_events P) = total P.
(* strategy: flat_map_length / length_flat_map then map/seq lengths = proc_len. *)

Lemma event_eq_dec : forall P (a b : Event P), {a = b} + {a <> b}.
(* nat*nat has dec eq; lift through proj1_sig + proof_irrelevance. *)
```

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 180 execution/Event.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/Event.v
git commit -m "feat(execution): finite event carrier and enumeration"
```

---

## Task 3: Finiteness of the carrier (`Finite.v`) — risk-isolated

**Files:** Create `execution/Finite.v`

- [ ] **Step 1: State the two finiteness lemmas**

```coq
From Stdlib Require Import List Arith Lia Ensembles Finite_sets.
From Execution Require Import Op Event.
(* Reuse the existing helper that lifts a subset cardinal to the subtype's Full_set. *)
From Posets Require Import dimension.Theorems.   (* provides cardinal_subtype_full *)

(* The raw valid set has cardinality [total]. *)
Lemma valid_cardinal :
  forall P, cardinal (nat * nat) (ValidSet P) (total P).

(* Hence the carrier's Full_set is finite with that cardinality. *)
Lemma event_cardinal :
  forall P, cardinal (Event P) (Full_set (Event P)) (total P).
```

- [ ] **Step 2: Prove `valid_cardinal`**

Strategy (this is the residual finiteness work — keep it in this file):
- `ValidSet P` as an `Ensemble (nat*nat)` equals the "list-to-ensemble" of `raw_events P` (use `raw_events_spec`).
- A `NoDup` list of length `k` whose elements are exactly an ensemble `S` gives `cardinal _ S k`. If a `cardinal_of_list`/`list_to_ensemble` bridge already exists in `posets/dilworth/CardinalLemmas.v` or `CardinalArithmetic.v`, reuse it; otherwise add a local lemma:

```coq
Lemma cardinal_of_NoDup_list :
  forall (U : Type) (l : list U),
    NoDup l ->
    cardinal U (fun x => List.In x l) (length l).
(* induction on l; card_empty / card_add; In-cons. *)
```

  Then `valid_cardinal` = `cardinal_of_NoDup_list` on `raw_events P` (via `raw_events_NoDup`, `raw_events_length`) rewritten along `raw_events_spec` to land on `ValidSet P`.

- [ ] **Step 3: Prove `event_cardinal`**

```coq
Proof.
  intro P.
  exact (cardinal_subtype_full (nat*nat) (ValidSet P) (total P) (valid_cardinal P)).
Qed.
```

(Note: `Event P = { pi | In _ (ValidSet P) pi }` matches `cardinal_subtype_full`'s subtype shape exactly. If the `In`/`Valid` unfolding doesn't line up definitionally, insert an `Ensemble` equality rewrite first.)

- [ ] **Step 4: Build (allow more time; this is the heavy file)**

Run: `bash .claude/scripts/timed-build.sh 300 execution/Finite.vo 1`
Expected: exit 0. If 124, split `cardinal_of_NoDup_list` / `valid_cardinal` into a separate `FiniteAux.v` and add it to `dune` + `_CoqProject`.

- [ ] **Step 5: Commit**

```bash
git add execution/Finite.v
git commit -m "feat(execution): carrier finiteness via cardinal_subtype_full"
```

---

## Task 4: Direct-causality edges and the order (`Edges.v`)

**Files:** Create `execution/Edges.v`

- [ ] **Step 1: Define `edge` and `hb`**

```coq
From Stdlib Require Import List Arith Lia Relation_Operators.
From Execution Require Import Op Event.

Section Edges.
  Context (P : Program).

  (* Direct causal edge between two valid events. *)
  Definition edge (a b : Event P) : Prop :=
    let (pa, ia) := proj1_sig a in
    let (pb, ib) := proj1_sig b in
    (* program order: next op in the same process *)
    (pa = pb /\ ib = S ia)
    \/
    (* message: a is a Send matched by recv b *)
    (exists t, op_at P pa ia = Some (Send pb t)
            /\ op_at P pb ib = Some (Recv pa t)).

  (* Execution-poset order = reflexive-transitive closure of edge. *)
  Definition hb (a b : Event P) : Prop := clos_refl_trans (Event P) edge a b.
End Edges.
```

- [ ] **Step 2: State refl/trans facts (free from `clos_refl_trans`)**

```coq
Lemma hb_refl  : forall P (a : Event P), hb P a a.
Lemma hb_trans : forall P (a b c : Event P), hb P a b -> hb P b c -> hb P a c.
(* rt_refl / rt_trans. *)
```

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 120 execution/Edges.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/Edges.v
git commit -m "feat(execution): direct-causality edges and hb order"
```

---

## Task 5: Rank / structural acyclicity (`Rank.v`)

**Files:** Create `execution/Rank.v`

This is where acyclicity becomes structural: a `RankedProgram` bundles a `rank`
that strictly increases along every edge (the Schedule supplies it in Task 7).

- [ ] **Step 1: Define `RankedProgram` and derive monotonicity along `hb`**

```coq
From Stdlib Require Import List Arith Lia Relation_Operators.
From Execution Require Import Op Event Edges.

Record RankedProgram := {
  rp_prog :> Program;
  rp_rank : nat * nat -> nat;
  (* strictly increases across every direct edge *)
  rp_rank_mono :
    forall (a b : Event rp_prog), edge rp_prog a b ->
      rp_rank (proj1_sig a) < rp_rank (proj1_sig b)
}.

(* rank is monotone (non-strict) along hb *)
Lemma rank_hb_le :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> rp_rank R (proj1_sig a) <= rp_rank R (proj1_sig b).
(* clos_refl_trans induction; base = rp_rank_mono (strict ⇒ ≤), refl, trans by le_trans. *)
```

- [ ] **Step 2: State the acyclicity corollary used for antisymmetry**

```coq
Lemma hb_antisym :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> hb R b a -> a = b.
```

Strategy: from `rank_hb_le` both ways, `rp_rank (proj1_sig a) = rp_rank (proj1_sig b)`. That alone doesn't give `a = b`. Strengthen: prove that on a single edge the rank strictly increases, so any non-reflexive `hb` strictly increases rank. Concretely add:

```coq
(* hb that is not equality strictly increases rank *)
Lemma hb_neq_rank_lt :
  forall (R : RankedProgram) (a b : Event R),
    hb R a b -> a <> b -> rp_rank R (proj1_sig a) < rp_rank R (proj1_sig b).
```

then `hb_antisym`: if `a <> b`, `hb a b` and `hb b a` give `rank a < rank b < rank a`, contradiction; so `a = b`.

For `hb_neq_rank_lt`, induct on `clos_refl_trans`: the `rt_step` case is strict (`rp_rank_mono`); `rt_refl` contradicts `a <> b`; `rt_trans a m b`: if `a = m` use the right branch, if `m = b` use the left, else both strict — needs `event_eq_dec` (from Task 2) to split. Keep this lemma small; if the `rt_trans` bookkeeping balloons, factor a `clos_trans`-based variant.

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 180 execution/Rank.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/Rank.v
git commit -m "feat(execution): ranked programs give structural acyclicity"
```

---

## Task 6: Poset / finite-poset instances and the `ExecPoset` bundle (`Poset.v`)

**Files:** Create `execution/Poset.v`

- [ ] **Step 1: Prove the class instances**

```coq
From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Finite.

(* hb on a ranked program is a partial order. *)
Instance hb_IsPoset (R : RankedProgram) : IsPoset (Event R) (hb R).
Proof.
  constructor.
  - exact (hb_refl R).
  - exact (hb_antisym R).
  - exact (hb_trans R).
Qed.

(* and a finite poset of size [total]. *)
Instance hb_IsFinitePoset (R : RankedProgram) :
  IsFinitePoset (Event R) (hb R) (total R).
Proof.
  constructor.
  - exact (hb_IsPoset R).
  - exact (event_cardinal R).
Qed.
```

- [ ] **Step 2: Define the public bundle**

```coq
(* The canonical object the rest of the framework passes around. *)
Record ExecPoset := {
  ep_ranked : RankedProgram;
  ep_size   : nat;
  ep_size_ok : cardinal (Event ep_ranked) (Full_set (Event ep_ranked)) ep_size
}.

Definition ep_carrier (E : ExecPoset) := Event (ep_ranked E).
Definition ep_order   (E : ExecPoset) := hb (ep_ranked E).

(* Smart constructor from any ranked program. *)
Definition exec_of (R : RankedProgram) : ExecPoset :=
  {| ep_ranked := R; ep_size := total R; ep_size_ok := event_cardinal R |}.
```

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 180 execution/Poset.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/Poset.v
git commit -m "feat(execution): IsPoset/IsFinitePoset instances and ExecPoset bundle"
```

---

## Task 7: Schedule, desugaring, and agreement (`Schedule.v`)

**Files:** Create `execution/Schedule.v`

The Schedule is the paper-style "rules" form. Each step names a set of
point-to-point synchronizations happening at that global tick; desugaring emits
a `RankedProgram` whose `rank` is the global tick, making acyclicity automatic.

- [ ] **Step 1: Define `Schedule`, `desugar`, `wf_schedule`**

```coq
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Event Edges Rank Poset.
Import ListNotations.

(* One synchronization step: a list of directed syncs (from, to) firing at this tick.
   For the sync-shape target each is a send immediately followed by its receive;
   a Local step is a sync from p to p. *)
Record SyncStep := { syncs : list (Pid * Pid) }.

Record Schedule := {
  sch_nprocs : nat;
  sch_steps  : list SyncStep
}.

(* desugar: fold the steps, appending one op per participating process per tick,
   and recording each event's global tick as its rank. Produces a RankedProgram. *)
Definition desugar (s : Schedule) : RankedProgram.
(* Implementation: build [procs] by, for each step in order, appending
   Send/Recv (or Local) ops to the involved processes; build [rp_rank] from a
   parallel map (p,i) -> tick index; discharge [rp_rank_mono] because every edge
   (program order or matched send→recv) goes from an earlier tick to a strictly
   later one by construction. *)
Admitted.   (* replace with the real definition; see Step 2 for the obligation *)

Definition wf_schedule (s : Schedule) : Prop :=
  forall st, List.In st (sch_steps s) ->
    forall pq, List.In pq (syncs st) ->
      fst pq < sch_nprocs s /\ snd pq < sch_nprocs s.
```

NOTE: `desugar` must be a real `Definition`, not `Admitted` — the `Admitted` above is a placeholder marking the obligation. Build the `procs`/`rank` by a list fold; the only proof obligation is `rp_rank_mono`, proved by construction (ticks strictly increase along edges).

- [ ] **Step 2: State faithfulness + agreement theorems**

```coq
(* desugaring a wf schedule yields a wf program *)
Theorem desugar_wf :
  forall s, wf_schedule s -> wf_program (desugar s).

(* The execution poset is well-defined from the schedule and agrees with the
   program it desugars to — trivial once exec_of is defined on desugar, but we
   state it as the public agreement contract. *)
Definition exec_of_schedule (s : Schedule) : ExecPoset := exec_of (desugar s).

Theorem schedule_program_agree :
  forall s (a b : Event (desugar s)),
    ep_order (exec_of_schedule s) a b <-> hb (desugar s) a b.
Proof. reflexivity. Qed.   (* holds definitionally by construction *)
```

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/Schedule.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/Schedule.v
git commit -m "feat(execution): schedule, desugaring, and program agreement"
```

---

## Task 8: Edge-set representation and agreement (`FromEdges.v`)

**Files:** Create `execution/FromEdges.v`

- [ ] **Step 1: Define `from_edges` and the agreement theorem**

```coq
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Event Edges Rank Poset.
Import ListNotations.

(* Explicit edge-set description: process lengths, message edges as
   (p,i,q,j) quadruples, and a rank assignment with its monotonicity proof. *)
Record EdgeSpec := {
  es_lens  : list nat;                       (* proc_len for each process *)
  es_msgs  : list (nat * nat * nat * nat);   (* (sender p,i) -> (recv q,j) *)
  es_rank  : nat * nat -> nat
}.

(* Build the underlying Program from an EdgeSpec: each process p gets
   [es_lens!!p] ops; op (p,i) = Send/Recv if (p,i) appears in es_msgs, else Local. *)
Definition prog_of_edgespec (e : EdgeSpec) : Program.
(* list construction from es_lens / es_msgs *)
Admitted.   (* placeholder for the real definition *)

(* Require the supplied rank to be monotone along the induced edges. *)
Definition edgespec_ranked (e : EdgeSpec)
  (Hmono : forall a b : Event (prog_of_edgespec e),
             edge (prog_of_edgespec e) a b ->
             es_rank e (proj1_sig a) < es_rank e (proj1_sig b))
  : RankedProgram :=
  {| rp_prog := prog_of_edgespec e;
     rp_rank := es_rank e;
     rp_rank_mono := Hmono |}.

Definition from_edges (e : EdgeSpec) (Hmono : _) : ExecPoset :=
  exec_of (edgespec_ranked e Hmono).
```

- [ ] **Step 2: State the round-trip agreement (rules ≡ edge set)**

```coq
(* The edges *read back* from a program equal the program's own edge relation,
   i.e. building an EdgeSpec from a RankedProgram and back gives the same hb. *)
Definition edges_of (R : RankedProgram) : EdgeSpec :=
  {| es_lens := map (proc_len R) (seq 0 (nprocs R));
     es_msgs := (* enumerate matched (p,i,q,j) from procs R *) nil;  (* fill in *)
     es_rank := rp_rank R |}.

Theorem from_edges_agree :
  forall (R : RankedProgram) Hmono (a b : Event R) a' b',
    (* a,b and a',b' identify the same (p,i) pairs *)
    proj1_sig a = proj1_sig a' -> proj1_sig b = proj1_sig b' ->
    hb R a b <-> hb (edgespec_ranked (edges_of R) Hmono) a' b'.
```

Strategy: prove `prog_of_edgespec (edges_of R)` has the same `op_at` on every
`(p,i)` as `R` (a `proc`/`op_at` extensionality lemma), hence the same `edge`
relation, hence the same `clos_refl_trans`. The `Hmono` argument is discharged
by `rp_rank_mono R` transported across the `op_at` equality. Keep the `op_at`
extensionality as a named lemma `op_at_edgespec_of`.

- [ ] **Step 3: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/FromEdges.vo 2`
Expected: exit 0.

- [ ] **Step 4: Commit**

```bash
git add execution/FromEdges.v
git commit -m "feat(execution): edge-set representation and rules<->edges agreement"
```

---

## Task 9: Examples / compile-checked tests (`Examples.v`)

**Files:** Create `execution/Examples.v`

- [ ] **Step 1: Encode the N=3 execution two ways and prove they agree**

```coq
From Stdlib Require Import List Arith Lia.
From Execution Require Import Op Event Edges Rank Poset Schedule FromEdges.
Import ListNotations.

(* N=3, the paper's always-dimension-2 case: a minimal synchronized execution. *)
Definition sched_n3 : Schedule :=
  {| sch_nprocs := 3;
     sch_steps  := (* the mΨ(3,_) step list from the paper *) [] |}.   (* fill in *)

Definition edges_n3 : EdgeSpec :=
  {| es_lens := (* per-process lengths *) [];
     es_msgs := (* explicit message quadruples *) [];
     es_rank := (* explicit ranks *) (fun _ => 0) |}.   (* fill in *)

(* Both descriptions denote the same Program (hence same poset). *)
Example n3_same_program :
  desugar sched_n3 = prog_of_edgespec edges_n3 :> Program.
(* by computation / reflexivity once both are concrete *)
```

- [ ] **Step 2: Add sanity ordering/concurrency facts**

```coq
(* pick two events known to be causally ordered, and two known concurrent *)
Example n3_ordered    : exists a b : Event (desugar sched_n3), hb (desugar sched_n3) a b.
Example n3_concurrent : exists a b : Event (desugar sched_n3),
  ~ hb (desugar sched_n3) a b /\ ~ hb (desugar sched_n3) b a.
```

- [ ] **Step 3: Add one mΨ(4,5) configuration (schedule + edge set + equality)**

```coq
Definition sched_m45 : Schedule :=
  {| sch_nprocs := 4; sch_steps := (* one of the 10 mΨ(4,5) configs *) [] |}.  (* fill in *)

Definition edges_m45 : EdgeSpec := (* matching explicit edge set *)
  {| es_lens := []; es_msgs := []; es_rank := fun _ => 0 |}.   (* fill in *)

Example m45_same_program :
  desugar sched_m45 = prog_of_edgespec edges_m45 :> Program.
```

- [ ] **Step 4: Build**

Run: `bash .claude/scripts/timed-build.sh 240 execution/Examples.vo 2`
Expected: exit 0. (If the concrete `mΨ(4,5)` config is uncertain, encode any single valid 4-process synchronized execution and note it; the *structure* is what is being tested, not the specific paper enumeration.)

- [ ] **Step 5: Commit**

```bash
git add execution/Examples.v
git commit -m "test(execution): N=3 and m-Psi(4,5) examples, both representations agree"
```

---

## Task 10: Aggregator, whole-project build, INDEX update

**Files:** Modify `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1: Fill in the aggregator**

```coq
(* Execution poset framework — public surface. *)
From Execution Require Export Op Event Finite Edges Rank Poset Schedule FromEdges.
```

- [ ] **Step 2: Build the whole `execution/` library**

Run: `bash .claude/scripts/timed-build.sh 600 execution 2`
Expected: exit 0.

- [ ] **Step 3: Whole-project build (catch cross-module breakage)**

Run: `bash .claude/scripts/timed-build.sh 1800 @all 4`
Expected: exit 0.

- [ ] **Step 4: Update `docs/INDEX.md`**

Add an `Execution` section listing: `Op`/`Program`/`wf_program`, `Event`/`total`,
`event_cardinal`, `edge`/`hb`, `RankedProgram`/`hb_antisym`, `IsPoset`/`IsFinitePoset`
instances, `ExecPoset`/`exec_of`, `Schedule`/`desugar`/`desugar_wf`,
`from_edges`/`from_edges_agree`.

- [ ] **Step 5: Commit**

```bash
git add execution/Execution.v docs/INDEX.md
git commit -m "feat(execution): aggregate exports; index core model"
```

---

## Self-review notes (gaps to watch during execution)

- **`desugar` / `prog_of_edgespec` are real definitions**, shown as `Admitted`
  placeholders only to mark where the list-construction code goes. They must be
  total `Definition`s before their files build.
- **`from_edges` `Hmono` argument**: the underscore in `from_edges`/`from_edges_agree`
  signatures stands for the explicit monotonicity hypothesis type spelled out in
  `edgespec_ranked`; write it out in full when implementing.
- **`Finite.v` is the single highest-risk file** (cardinality of a `nat*nat`
  subset). It is deliberately isolated so a timeout there doesn't block Tasks 4–8,
  which only depend on `Event.v`, not `Finite.v`. If blocked, proceed with
  Edges/Rank/Poset (Poset's `IsFinitePoset` instance is the only consumer) and
  return to it.
- **Spec coverage:** A.0 module layout → Task 0; A.1 three layers → Tasks 1/7
  (schedule+program) and 4 (edge-set poset); A.2 finite carrier → Task 2; A.3
  edges/order → Task 4; A.4 IsPoset/IsFinitePoset + acyclicity-by-construction →
  Tasks 5–6; A.5 agreement theorems (faithfulness, schedule≡program, edge-set
  agreement) → Tasks 7–8; A.6 testing (N=3 + mΨ(4,5), both representations) →
  Task 9. All spec sections map to a task.

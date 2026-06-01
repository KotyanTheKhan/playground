# YAML I/O — Datatypes, Printer & Model Bridges (Sub-project C, slice 1)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** A (`Schedule` — `Schedule`/`sch_nprocs`/`sch_frontiers`/`exec_of_schedule`), `Dimension.Theorems` (`cardinal_subtype_full` for `Vert` finiteness), `PosetClasses` (`IsPoset`), Stdlib `Strings.String`/`Ascii`, `Relation_Operators` (`clos_refl_trans`).
**External format:** `~/code/research/playground_two/playground/nomadim` — the C++ `libnomadim` library and its YAML format (`include/nomadim/io.hpp`, `src/io.cpp`, `data/*.yaml`).

## Goal

Make the libnomadim YAML format readable/writable from our Coq model. This slice
(C slice 1) delivers the **datatypes**, the **`dump` printer** (Coq record → YAML
string matching libnomadim's emitter), and the **model bridges** (YAML execution →
`Schedule`; YAML poset → a bare finite poset via reachability). The string
**parser**, the **round-trip proof**, and **OCaml-extracted real file I/O** are later
C slices.

## The external format (verbatim from libnomadim)

Two top-level document kinds. From `data/*.yaml` (the C++ yaml-cpp emitter output —
the byte-fidelity ground truth):

```yaml
# data/exec_dim2.yaml — an execution
execution:
  n_procs: 2
  syncs:
    - [0, 1]
```
```yaml
# data/poset_s3.yaml — a poset
poset:
  n_vertices: 6
  edges:
    - [0, 4]
    - [0, 5]
    - [1, 3]
    - [1, 5]
    - [2, 3]
    - [2, 4]
```
- **execution**: `n_procs : int` + `syncs : list of [a,b]` (ordered; each a pair of
  distinct process indices). C++ `Execution { int n_procs; vector<pair<int,int>> syncs; }`;
  `validate()`: `n_procs > 0`, every endpoint in `[0, n_procs)`, no self-sync.
- **poset**: `n_vertices : int` + `edges : list of [u,v]` (cover/adjacency; the
  reflexive-transitive closure is the partial order). C++ `Poset { int n_vertices;
  adjacency_list edges; }`; `validate()`: endpoints in range, acyclic. The emitter
  flattens `edges[u]` as `for u in [0,n): for v in edges[u]: emit [u,v]`.
- Emitter style (`src/io.cpp`, yaml-cpp): block maps, 2-space nesting; sequence
  entries `    - [a, b]` (4-space indent, `- `, flow seq with `, ` separator).

## Component 1 — datatypes + well-formedness (`execution/Yaml.v`)

```coq
From Stdlib Require Import String Ascii List Arith Lia.
Import ListNotations.

Record YamlExecution := { ye_nprocs : nat; ye_syncs : list (nat * nat) }.
Record YamlPoset := { yp_nverts : nat; yp_edges : list (nat * nat) }.

Inductive Document :=
  | DocExecution (e : YamlExecution)
  | DocPoset (p : YamlPoset).

Definition wf_yaml_execution (e : YamlExecution) : Prop :=
  0 < ye_nprocs e /\
  (forall a b, List.In (a, b) (ye_syncs e) -> a < ye_nprocs e /\ b < ye_nprocs e /\ a <> b).

Definition wf_yaml_poset (p : YamlPoset) : Prop :=
  (forall u v, List.In (u, v) (yp_edges p) -> u < yp_nverts p /\ v < yp_nverts p) /\
  (* acyclic: no nonempty edge-path returns to its start.  Phrased via the closure: *)
  (forall x : { n : nat | n < yp_nverts p },
     ~ clos_trans _ (fun a b => List.In (proj1_sig a, proj1_sig b) (yp_edges p)) x x).
```
(`Document`/edges flattened to `list (nat*nat)`, matching the emitter's flattened
output order; the bridges/printer treat them as a flat edge list.)

## Component 2 — the `dump` printer (`Yaml.v`)

```coq
(* nat -> decimal string *)
Definition string_of_nat (n : nat) : string := …   (* digit recursion via Ascii *)

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition pair_line (indent : string) (xy : nat * nat) : string :=
  indent ++ "- [" ++ string_of_nat (fst xy) ++ ", " ++ string_of_nat (snd xy) ++ "]" ++ nl.

Definition dump_execution (e : YamlExecution) : string :=
  "execution:" ++ nl ++
  "  n_procs: " ++ string_of_nat (ye_nprocs e) ++ nl ++
  "  syncs:" ++ nl ++
  String.concat "" (map (pair_line "    ") (ye_syncs e)).

Definition dump_poset (p : YamlPoset) : string :=
  "poset:" ++ nl ++
  "  n_vertices: " ++ string_of_nat (yp_nverts p) ++ nl ++
  "  edges:" ++ nl ++
  String.concat "" (map (pair_line "    ") (yp_edges p)).

Definition dump (d : Document) : string :=
  match d with DocExecution e => dump_execution e | DocPoset p => dump_poset p end.
```
**Byte-fidelity target:** the three `data/*.yaml` files exactly (the observed emitter
output). `string_of_nat` produces plain decimals (no leading zeros). The trailing
newline / exact whitespace are pinned to match the example files (Component 5 tests
`dump … = "<file bytes>"`). Full yaml-cpp-emitter equivalence (beyond these examples)
is deferred to the round-trip slice.

## Component 3 — execution bridge (`Yaml.v`)

```coq
From Execution Require Import Schedule.

(* Each sync [a,b] becomes a singleton frontier [(a,b)]. *)
Definition schedule_of_yaml (e : YamlExecution) : Schedule :=
  {| sch_nprocs := ye_nprocs e;
     sch_frontiers := map (fun s => [s]) (ye_syncs e) |}.

Lemma schedule_of_yaml_nprocs : forall e, sch_nprocs (schedule_of_yaml e) = ye_nprocs e.
Lemma schedule_of_yaml_nfrontiers :
  forall e, length (sch_frontiers (schedule_of_yaml e)) = length (ye_syncs e).
```
(Both by `reflexivity`/`length_map`.) Payoff: `exec_of_schedule (schedule_of_yaml e)`
is a real `ExecPoset` — a loaded execution YAML is analyzable by the dimension
machinery.

## Component 4 — poset bridge: a bare finite poset (`Yaml.v` or `execution/YamlPoset.v`)

```coq
From Stdlib Require Import Ensembles Finite_sets Relation_Operators.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import Theorems.

Definition Vert (p : YamlPoset) : Type := { n : nat | n < yp_nverts p }.

Definition yaml_edge (p : YamlPoset) (x y : Vert p) : Prop :=
  List.In (proj1_sig x, proj1_sig y) (yp_edges p).

Definition yaml_order (p : YamlPoset) : Vert p -> Vert p -> Prop :=
  clos_refl_trans (Vert p) (yaml_edge p).

(* under acyclicity, the reachability closure is a partial order *)
Lemma yaml_order_IsPoset :
  forall p, wf_yaml_poset p -> IsPoset (Vert p) (yaml_order p).

(* the vertex carrier is finite *)
Lemma yaml_vert_finite :
  forall p, Finite (Vert p) (Full_set (Vert p)).
```
- `yaml_order_IsPoset`: reflexivity/transitivity from `clos_refl_trans` (`rt_refl`/`rt_trans`).
  Antisymmetry: `yaml_order x y` and `yaml_order y x` with `x <> y` ⟹ a nonempty
  cycle (`clos_trans` from `x` to `x`), contradicting `wf_yaml_poset`'s acyclicity.
  (Convert `clos_refl_trans` both ways + `x <> y` into a `clos_trans` cycle — a small
  lemma `crt_neq_ct`; reuse the `Edges.v`/`Rank.v` closure-reasoning patterns.)
- `yaml_vert_finite`: `Vert p = { n | n < yp_nverts p }`; `cardinal nat (fun n => n < yp_nverts p) (yp_nverts p)` (the `[0..n)` set, à la `TransformA.v`'s `B_square_Hfin`), then `cardinal_subtype_full` + `cardinal_finite`.

So `yaml_order p` is a finite poset (`IsPoset` + `Finite`) → `PosetDimension` applies.
(`IsFinitePoset (Vert p) (yaml_order p) (yp_nverts p)` can be bundled if convenient.)

If `Yaml.v` exceeds ~500 lines, put Component 4 in `execution/YamlPoset.v`
(`From Execution Require Import Yaml.`).

## Component 5 — concrete examples (`execution/YamlExamples.v`, test-only)

Match the three libnomadim data files:
```coq
Definition exec_dim2 : YamlExecution := {| ye_nprocs := 2; ye_syncs := [(0,1)] |}.
Definition exec_4_canonical : YamlExecution :=
  {| ye_nprocs := 4; ye_syncs := [(0,1);(1,2);(2,3);(0,2)] |}.
Definition poset_s3 : YamlPoset :=
  {| yp_nverts := 6; yp_edges := [(0,4);(0,5);(1,3);(1,5);(2,3);(2,4)] |}.

(* byte-fidelity against the actual data/*.yaml files *)
Example dump_exec_dim2_eq : dump (DocExecution exec_dim2) = "execution:<nl>  n_procs: 2<nl>  syncs:<nl>    - [0, 1]<nl>".
Example dump_exec_4_eq    : dump (DocExecution exec_4_canonical) = "<bytes of exec_4_canonical.yaml>".
Example dump_poset_s3_eq  : dump (DocPoset poset_s3) = "<bytes of poset_s3.yaml>".

(* a loaded execution is a real schedule; a loaded poset is a real poset *)
Example exec_dim2_schedule_nprocs : sch_nprocs (schedule_of_yaml exec_dim2) = 2.
Example poset_s3_is_poset : IsPoset (Vert poset_s3) (yaml_order poset_s3).
```
- The `dump_*_eq` lemmas: write the expected RHS as an explicit Coq `string` with `nl`
  for newlines (literally the file bytes — read `data/*.yaml` to get the exact bytes,
  esp. trailing newline). Prove by `vm_compute; reflexivity`.
- `poset_s3_is_poset`: `apply yaml_order_IsPoset`; discharge `wf_yaml_poset poset_s3`
  (range: `vm_compute`/membership; acyclic: the S(3,1) cover is bipartite `{0,1,2}→{3,4,5}`,
  no cycle — prove the `~ clos_trans … x x` by a finite argument, OR derive acyclicity
  from a rank/strata function `level : nat -> nat` (`0,1,2 ↦ 0`; `3,4,5 ↦ 1`) strictly
  increasing along edges, mirroring `Rank.v`). Provide a helper
  `acyclic_of_strict_rank` if it keeps the example short.

## Files, wiring, testing

- New: `execution/Yaml.v` (+ optional `execution/YamlPoset.v`), `execution/YamlExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the new modules.
- `execution/Execution.v`: export `Yaml` (+ `YamlPoset`); NOT the examples.
- `docs/INDEX.md`: add a "YAML I/O" subsection.
- Every file builds via the wrapper; whole-`execution` and `@all` green; **zero
  `Admitted`**. Files <500 lines, each `Qed` <5 min.
- `Print Assumptions` on `dump`, `yaml_order_IsPoset`, the examples — expected only
  standard axioms; recorded.

## Acceptance criteria

1. `Yaml.v`: `YamlExecution`/`YamlPoset`/`Document`, `wf_yaml_execution`/`wf_yaml_poset`,
   `string_of_nat`, `dump_execution`/`dump_poset`/`dump`, `schedule_of_yaml` (+ structural
   lemmas), `Vert`/`yaml_edge`/`yaml_order`, `yaml_order_IsPoset`, `yaml_vert_finite`.
   Zero admits.
2. `YamlExamples.v`: the three data-file instances, `dump_*_eq` byte-equality,
   `exec_dim2_schedule_nprocs`, `poset_s3_is_poset`. Zero admits.
3. Whole-project green; INDEX updated; `Print Assumptions` recorded.

## Out of scope (later C slices)

The string **parser** (`parse : string -> option Document`); the **round-trip proof**
(`parse (dump d) = Some d`); **OCaml-extracted real file I/O** (`load_file`/`save_file`);
full **yaml-cpp-emitter byte-equivalence** beyond the example files; the poset-doc →
`EdgeSpec`/message-model bridge (the `Vert`/`yaml_order` finite-poset is the bridge
this slice provides).

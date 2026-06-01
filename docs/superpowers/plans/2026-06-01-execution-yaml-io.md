# YAML I/O — Datatypes, Printer & Model Bridges — Implementation Plan (C slice 1)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans. Steps use checkbox (`- [ ]`).
>
> **Coq convention:** Definitions and lemma statements are authoritative — implement verbatim. "Test passes" = file builds via `bash .claude/scripts/timed-build.sh <secs> execution/<File>.vo 2` (exit 0; 124→split; 137→`-j1`). ZERO `Admitted`. Files <500 lines, each `Qed` <5 min.

**Goal:** Coq datatypes for the libnomadim YAML format (execution + poset documents), a `dump` printer matching the format byte-for-byte against the example files, and model bridges (YAML execution → `Schedule`; YAML poset → a finite poset via reachability closure).

**Architecture:** New `execution/Yaml.v` (datatypes, wf predicates, `string_of_nat`, `dump`, `schedule_of_yaml`, and the `Vert`/`yaml_order` finite-poset bridge), `execution/YamlExamples.v` (the three libnomadim data-file instances, test-only). Split the poset bridge into `execution/YamlPoset.v` if `Yaml.v` exceeds ~500 lines.

**Tech Stack:** Coq/Rocq 9.1; Stdlib `Strings.String`/`Ascii`/`List`/`Arith`/`Relation_Operators`/`Ensembles`/`Finite_sets`; `Posets.PosetClasses`/`FinitePoset`; `Dimension.Theorems` (`cardinal_subtype_full`); execution `Schedule`.

**External format ground truth** (exact bytes of `~/code/research/playground_two/playground/nomadim/data/*.yaml`, confirmed via `od -c`): block maps, 2-space nesting, sequence entries `    - [a, b]` (4 spaces, `- `, `[`, `, ` separator, `]`), each line ends `\n`, file ends with a single `\n`, NO trailing whitespace. The expected `dump` outputs (with `<LF>` = newline char) are:
- exec_dim2: `execution:<LF>  n_procs: 2<LF>  syncs:<LF>    - [0, 1]<LF>`
- exec_4_canonical: `execution:<LF>  n_procs: 4<LF>  syncs:<LF>    - [0, 1]<LF>    - [1, 2]<LF>    - [2, 3]<LF>    - [0, 2]<LF>`
- poset_s3: `poset:<LF>  n_vertices: 6<LF>  edges:<LF>    - [0, 4]<LF>    - [0, 5]<LF>    - [1, 3]<LF>    - [1, 5]<LF>    - [2, 3]<LF>    - [2, 4]<LF>`

---

## File structure

| File | Responsibility |
|------|----------------|
| `execution/Yaml.v` | `YamlExecution`/`YamlPoset`/`Document`; `wf_yaml_execution`/`wf_yaml_poset`; `string_of_nat`; `dump_execution`/`dump_poset`/`dump`; `schedule_of_yaml` (+ structural lemmas); `Vert`/`yaml_edge`/`yaml_order`; `yaml_order_IsPoset`; `yaml_vert_finite`. |
| `execution/YamlExamples.v` | `exec_dim2`/`exec_4_canonical`/`poset_s3`; `dump_*_eq` byte-equality; `exec_dim2_schedule_nprocs`; `poset_s3_is_poset` (test-only). |
| wiring | `execution/dune`, `_CoqProject`, `execution/Execution.v`, `docs/INDEX.md`. |

Canonical names (verbatim): `YamlExecution`, `ye_nprocs`, `ye_syncs`, `YamlPoset`, `yp_nverts`, `yp_edges`, `Document`, `DocExecution`, `DocPoset`, `wf_yaml_execution`, `wf_yaml_poset`, `string_of_nat`, `dump_execution`, `dump_poset`, `dump`, `schedule_of_yaml`, `Vert`, `yaml_edge`, `yaml_order`, `yaml_order_IsPoset`, `yaml_vert_finite`, `exec_dim2`, `exec_4_canonical`, `poset_s3`.

---

## Task YA0: Scaffold

**Files:** create `execution/Yaml.v`, `execution/YamlExamples.v` (one comment line each); modify `execution/dune`, `_CoqProject`.

- [ ] **Step 1:** Create the two stubs.
- [ ] **Step 2:** Add `Yaml`, `YamlExamples` to the `(modules …)` list in `execution/dune` (that order, after the sync-shape modules).
- [ ] **Step 3:** Add the two `.v` paths to `_CoqProject` (same order, after `SyncShapeExamples.v`).
- [ ] **Step 4:** Build a stub: `bash .claude/scripts/timed-build.sh 120 execution/Yaml.vo 2`. Exit 0.
- [ ] **Step 5:** Commit:
```bash
git add execution/Yaml.v execution/YamlExamples.v execution/dune _CoqProject
git commit -m "scaffold YAML I/O modules"
```

---

## Task YA1: Datatypes + `string_of_nat` + printer (`Yaml.v`)

**Files:** `execution/Yaml.v`

- [ ] **Step 1: Imports + datatypes + wf predicates**

```coq
From Stdlib Require Import String Ascii List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Record YamlExecution := { ye_nprocs : nat; ye_syncs : list (nat * nat) }.
Record YamlPoset := { yp_nverts : nat; yp_edges : list (nat * nat) }.

Inductive Document :=
  | DocExecution (e : YamlExecution)
  | DocPoset (p : YamlPoset).

Definition wf_yaml_execution (e : YamlExecution) : Prop :=
  0 < ye_nprocs e /\
  (forall a b, List.In (a, b) (ye_syncs e) -> a < ye_nprocs e /\ b < ye_nprocs e /\ a <> b).
```
(The `wf_yaml_poset` predicate is added in YA3 with the closure machinery; not needed yet.)

- [ ] **Step 2: `string_of_nat`**

```coq
(* one decimal digit (0..9) as a Char *)
Definition digit_char (n : nat) : ascii := ascii_of_nat (48 + n).

(* string_of_nat via fuel = the number itself; standard pattern *)
Fixpoint string_of_nat_aux (fuel n : nat) (acc : string) : string :=
  let d := digit_char (Nat.modulo n 10) in
  let acc' := String d acc in
  match fuel with
  | 0 => acc'
  | S f => match Nat.div n 10 with
           | 0 => acc'
           | q => string_of_nat_aux f q acc'
           end
  end.

Definition string_of_nat (n : nat) : string := string_of_nat_aux n n "".
```
(Standard fuel-based decimal printer producing no leading zeros: `string_of_nat 0 = "0"`, `string_of_nat 2 = "2"`, `string_of_nat 10 = "10"`. Sanity-check by `Compute string_of_nat 0`, `... 10`, `... 123` mentally; the examples use only 0..6.)

- [ ] **Step 3: Build (datatypes + string_of_nat compile)** — `bash .claude/scripts/timed-build.sh 120 execution/Yaml.vo 2`. Exit 0.

- [ ] **Step 4: The printer**

```coq
Definition nl : string := String (ascii_of_nat 10) "".

Definition pair_line (xy : nat * nat) : string :=
  "    - [" ++ string_of_nat (fst xy) ++ ", " ++ string_of_nat (snd xy) ++ "]" ++ nl.

Definition dump_execution (e : YamlExecution) : string :=
  "execution:" ++ nl ++
  "  n_procs: " ++ string_of_nat (ye_nprocs e) ++ nl ++
  "  syncs:" ++ nl ++
  String.concat "" (map pair_line (ye_syncs e)).

Definition dump_poset (p : YamlPoset) : string :=
  "poset:" ++ nl ++
  "  n_vertices: " ++ string_of_nat (yp_nverts p) ++ nl ++
  "  edges:" ++ nl ++
  String.concat "" (map pair_line (yp_edges p)).

Definition dump (d : Document) : string :=
  match d with DocExecution e => dump_execution e | DocPoset p => dump_poset p end.
```
(Confirm `String.concat` exists in Rocq 9.1 Stdlib — if not, define a local `concat_str := fold_right append ""`. `++` is `String.append` under `string_scope`.)

- [ ] **Step 5: Build** — `bash .claude/scripts/timed-build.sh 180 execution/Yaml.vo 2`. Exit 0; zero admits.
- [ ] **Step 6: Commit** — `git add execution/Yaml.v && git commit -m "feat(execution): YAML datatypes, string_of_nat, dump printer"`.

---

## Task YA2: Execution bridge (`Yaml.v`)

**Files:** `execution/Yaml.v` (extend)

- [ ] **Step 1: `schedule_of_yaml` + structural lemmas**

```coq
From Execution Require Import Schedule.

Definition schedule_of_yaml (e : YamlExecution) : Schedule :=
  {| sch_nprocs := ye_nprocs e;
     sch_frontiers := map (fun s => [s]) (ye_syncs e) |}.

Lemma schedule_of_yaml_nprocs :
  forall e, sch_nprocs (schedule_of_yaml e) = ye_nprocs e.

Lemma schedule_of_yaml_nfrontiers :
  forall e, length (sch_frontiers (schedule_of_yaml e)) = length (ye_syncs e).
```
Proofs: `reflexivity` (nprocs); `simpl; rewrite length_map; reflexivity` (nfrontiers). (`Schedule` import needs to be added to the `From Execution Require Import …` line at the top — adjust the import block.)

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 180 execution/Yaml.vo 2`. Exit 0.
- [ ] **Step 3: Commit** — `git add execution/Yaml.v && git commit -m "feat(execution): YAML execution -> Schedule bridge"`.

---

## Task YA3: Poset bridge — finite poset via reachability (`Yaml.v`)

**Files:** `execution/Yaml.v` (extend)

- [ ] **Step 1: `wf_yaml_poset` + the `Vert`/`yaml_edge`/`yaml_order` construction**

Add to the imports: `From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Relation_Operators. From Posets Require Import PosetClasses FinitePoset. From Dimension Require Import Theorems.`

```coq
Definition wf_yaml_poset (p : YamlPoset) : Prop :=
  (forall u v, List.In (u, v) (yp_edges p) -> u < yp_nverts p /\ v < yp_nverts p) /\
  (forall x : { n : nat | n < yp_nverts p },
     ~ clos_trans { n : nat | n < yp_nverts p }
         (fun a b => List.In (proj1_sig a, proj1_sig b) (yp_edges p)) x x).

Definition Vert (p : YamlPoset) : Type := { n : nat | n < yp_nverts p }.

Definition yaml_edge (p : YamlPoset) (x y : Vert p) : Prop :=
  List.In (proj1_sig x, proj1_sig y) (yp_edges p).

Definition yaml_order (p : YamlPoset) : Vert p -> Vert p -> Prop :=
  clos_refl_trans (Vert p) (yaml_edge p).
```

- [ ] **Step 2: `yaml_order_IsPoset`**

```coq
Lemma yaml_order_IsPoset :
  forall p, wf_yaml_poset p -> IsPoset (Vert p) (yaml_order p).
```
Strategy: `intros p [Hrange Hacyc]. constructor.`
- refl: `intro x. apply rt_refl.`
- trans: `intros x y z. apply rt_trans.`
- antisym: `intros x y Hxy Hyx.` Need `x = y`. `destruct (classic (x = y))` (needs `Classical`; add to imports). If `x = y`, done. Else (`x <> y`): derive a `clos_trans … x x` cycle, contradicting `Hacyc x`. Build it: from `yaml_order x y` (= `clos_refl_trans … x y`) and `x <> y`, get `clos_trans … x y` (a small lemma `crt_neq_ct : clos_refl_trans A R a b -> a <> b -> clos_trans A R a b` — by `clos_refl_trans` induction: `rt_refl` contradicts `a<>b`; `rt_step` ⟹ `t_step`; `rt_trans a m b` ⟹ case `a=m`/`m=b`/both-distinct using `t_trans`; needs decidable-ish handling via `classic`). Similarly `clos_trans … y x` from `yaml_order y x` (here `y <> x`). Then `t_trans … x y x : clos_trans … x x`, contradicting `Hacyc x`. `exfalso; apply (Hacyc x); eapply t_trans; eauto`.
  - Prove `crt_neq_ct` as a local lemma above `yaml_order_IsPoset` (general over `A R`). The `rt_trans` case: `clos_refl_trans A R a m`, `clos_refl_trans A R m b`, IH on each, `a <> b`; `destruct (classic (a = m))`: if `a = m` then `m <> b` (since `a<>b`), use IH on the second ⟹ `clos_trans m b` = `clos_trans a b`; if `a <> m`, IH on first ⟹ `clos_trans a m`; then need `clos_trans m b` OR `m = b`: `destruct (classic (m = b))` — if `m=b`, `clos_trans a m = clos_trans a b`; else IH on second ⟹ `clos_trans m b`, `t_trans` with `clos_trans a m`. (`Classical` for the `classic` splits.)

- [ ] **Step 3: `yaml_vert_finite`**

```coq
Lemma yaml_vert_finite :
  forall p, Finite (Vert p) (Full_set (Vert p)).
```
Strategy: `Vert p = { n | n < yp_nverts p }`. Build `cardinal nat (fun n => n < yp_nverts p) (yp_nverts p)` (the `[0, yp_nverts p)` set) — reuse the `cardinal_of_NoDup_nat`/`[0;1;…]`-via-`seq` pattern from `TransformA.v`'s `B_square_Hfin` (or `Finite.v`'s `cardinal_of_NoDup_list`): the ensemble `(fun n => n < N)` equals `fun x => List.In x (seq 0 N)`, `NoDup (seq 0 N)` (`seq_NoDup`), `length (seq 0 N) = N`. Then `cardinal_subtype_full nat (fun n => n < yp_nverts p) (yp_nverts p) <that>` ⟹ `cardinal (Vert p) (Full_set _) (yp_nverts p)`; `cardinal_finite` ⟹ `Finite`. (READ `TransformA.v`'s `B_square_Hfin` and reuse its helper.)

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 360 execution/Yaml.vo 1`. Exit 0; zero admits. If `Yaml.v` > 500 lines, MOVE `wf_yaml_poset`/`Vert`/`yaml_edge`/`yaml_order`/`yaml_order_IsPoset`/`yaml_vert_finite` (+ `crt_neq_ct`) into `execution/YamlPoset.v` (`From Execution Require Import Yaml.`; wire dune + `_CoqProject`); report if split.
- [ ] **Step 5: Commit** — `git add execution/Yaml.v && git commit -m "feat(execution): YAML poset -> finite poset via reachability closure"`.

---

## Task YA4: Examples (`YamlExamples.v`)

**Files:** `execution/YamlExamples.v`

- [ ] **Step 1: The three data-file instances + dump byte-equality + bridge checks**

```coq
From Stdlib Require Import String Ascii List Arith Lia Classical Relation_Operators
                          Ensembles Finite_sets.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Schedule Yaml.
Import ListNotations.
Open Scope string_scope.

Definition exec_dim2 : YamlExecution := {| ye_nprocs := 2; ye_syncs := [(0,1)] |}.
Definition exec_4_canonical : YamlExecution :=
  {| ye_nprocs := 4; ye_syncs := [(0,1);(1,2);(2,3);(0,2)] |}.
Definition poset_s3 : YamlPoset :=
  {| yp_nverts := 6; yp_edges := [(0,4);(0,5);(1,3);(1,5);(2,3);(2,4)] |}.

(* byte-fidelity vs data/*.yaml; nl is the newline. Write the RHS with explicit nl. *)
Definition nl_e : string := String (Ascii.ascii_of_nat 10) "".

Example dump_exec_dim2_eq :
  dump (DocExecution exec_dim2) =
  "execution:" ++ nl_e ++ "  n_procs: 2" ++ nl_e ++ "  syncs:" ++ nl_e ++
  "    - [0, 1]" ++ nl_e.

Example dump_exec_4_eq :
  dump (DocExecution exec_4_canonical) =
  "execution:" ++ nl_e ++ "  n_procs: 4" ++ nl_e ++ "  syncs:" ++ nl_e ++
  "    - [0, 1]" ++ nl_e ++ "    - [1, 2]" ++ nl_e ++ "    - [2, 3]" ++ nl_e ++
  "    - [0, 2]" ++ nl_e.

Example dump_poset_s3_eq :
  dump (DocPoset poset_s3) =
  "poset:" ++ nl_e ++ "  n_vertices: 6" ++ nl_e ++ "  edges:" ++ nl_e ++
  "    - [0, 4]" ++ nl_e ++ "    - [0, 5]" ++ nl_e ++ "    - [1, 3]" ++ nl_e ++
  "    - [1, 5]" ++ nl_e ++ "    - [2, 3]" ++ nl_e ++ "    - [2, 4]" ++ nl_e.

Example exec_dim2_schedule_nprocs : sch_nprocs (schedule_of_yaml exec_dim2) = 2.

Example poset_s3_is_poset : IsPoset (Vert poset_s3) (yaml_order poset_s3).
```
Strategies:
- `dump_*_eq`: `vm_compute. reflexivity.` (the printer is computational; both sides reduce to the same `string`. If `vm_compute` mismatches, run `Compute dump (DocExecution exec_dim2).` and align the RHS to the actual output — but it MUST match the `data/*.yaml` bytes given above. NB `nl_e` here must be the SAME char as `Yaml.nl` — both `ascii_of_nat 10`.)
- `exec_dim2_schedule_nprocs`: `reflexivity` (or `apply schedule_of_yaml_nprocs`).
- `poset_s3_is_poset`: `apply yaml_order_IsPoset.` Discharge `wf_yaml_poset poset_s3`:
  - range conjunct: `intros u v Hin.` `simpl in Hin` (the 6-element edge list); `repeat (destruct Hin as [Heq | Hin]; [injection Heq; intros; subst; split; lia | ]); destruct Hin.` (each edge endpoint `< 6`).
  - acyclic conjunct: `intros x Hcyc.` The S(3,1) cover is bipartite: edges go `{0,1,2} -> {3,4,5}` only. A `clos_trans` cycle `x ↝ x` is impossible because every edge strictly increases a level (`level n := if n <? 3 then 0 else 1`), and `level` strictly increases along each edge, so along `clos_trans` it's non-decreasing AND a single step strictly increases — a cycle would need `level (proj1_sig x) < level (proj1_sig x)`. Prove a helper `yaml_edge_level_lt : forall a b, yaml_edge poset_s3 a b -> level (proj1_sig a) < level (proj1_sig b)` (finite check on the 6 edges: each `(u,v)` has `level u = 0 < 1 = level v`; `vm_compute`/case), then `clos_trans`-induction lifts it to `level (proj1_sig x) < level (proj1_sig x)` for the cycle, `lia`. Provide `level` and the helper locally. (Mirror `Rank.v`'s strict-rank-along-edges ⟹ acyclic pattern.)

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/YamlExamples.vo 2`. Exit 0; zero admits.
- [ ] **Step 3: Commit** — `git add execution/YamlExamples.v && git commit -m "test(execution): YAML data-file examples, dump byte-fidelity, poset_s3 is a poset"`.

---

## Task YA5: Export, whole-project build, INDEX, audit

**Files:** `execution/Execution.v`, `docs/INDEX.md`

- [ ] **Step 1:** Add `Yaml` (+ `YamlPoset` if YA3 split it) to the `Require Export` line in `execution/Execution.v` (NOT the examples).
- [ ] **Step 2:** Build whole `execution`: `bash .claude/scripts/timed-build.sh 900 execution 2`. Exit 0.
- [ ] **Step 3:** Whole-project: `bash .claude/scripts/timed-build.sh 1800 @all 2`. Exit 0.
- [ ] **Step 4:** `Print Assumptions` audit — temporarily append `Print Assumptions dump.` and `Print Assumptions yaml_order_IsPoset.` to `Yaml.v`, `Print Assumptions dump_poset_s3_eq.` and `Print Assumptions poset_s3_is_poset.` to `YamlExamples.v`; build each; read the axiom blocks (`dump` should be axiom-free / "Closed under the global context"; the poset ones expect standard classical/choice axioms); then `git checkout -- execution/Yaml.v execution/YamlExamples.v`. Record the lists.
- [ ] **Step 5:** Update `docs/INDEX.md` — add a "YAML I/O" subsection:
```
#### `execution/Yaml.v` — YAML I/O (datatypes, printer, model bridges)

The libnomadim YAML format (execution: n_procs + syncs; poset: n_vertices + cover edges) as Coq datatypes, a `dump` printer matching the format byte-for-byte, and bridges into the model: a YAML execution becomes a `Schedule`; a YAML poset becomes a finite poset (reachability closure of its cover edges). (Parser + round-trip + real file I/O are later C slices.)

| Name | Meaning |
|------|---------|
| `YamlExecution` / `YamlPoset` / `Document` | the two document kinds + their sum |
| `wf_yaml_execution` / `wf_yaml_poset` | well-formedness (mirroring libnomadim `validate`) |
| `string_of_nat` / `dump` | decimal printer; YAML serializer matching the format |
| `schedule_of_yaml` | a YAML execution as a `Schedule` (each sync = a singleton frontier) |
| `Vert` / `yaml_edge` / `yaml_order` | a YAML poset's vertices, cover edges, reachability order |
| `yaml_order_IsPoset` / `yaml_vert_finite` | the reachability order is a finite poset (under acyclicity) |
| `dump_*_eq` / `poset_s3_is_poset` | (test) byte-fidelity vs `data/*.yaml`; a loaded poset is a real poset |
```
Match the actual headers/style used elsewhere.
- [ ] **Step 6:** Commit — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export YAML I/O; index results"`.

---

## Self-review notes

- **Spec coverage:** Component 1 (datatypes/wf) → YA1 Step 1 + YA3 Step 1; Component 2 (printer) → YA1 Steps 2,4; Component 3 (execution bridge) → YA2; Component 4 (poset bridge) → YA3; Component 5 (examples) → YA4; wiring/testing/audit → YA0 + YA5. All mapped.
- **The substantive proofs:** `yaml_order_IsPoset`'s antisymmetry (via `crt_neq_ct` — closure→cycle, the one real lemma) and `poset_s3_is_poset`'s acyclicity (via a `level` rank function). `dump` + bridges are computational/structural. The `dump_*_eq` are `vm_compute; reflexivity` against the exact `data/*.yaml` bytes (given in the header).
- **Byte-fidelity ground truth (from `od -c`):** each file ends with a SINGLE `\n`, no trailing whitespace; 2-space nesting; `    - [a, b]` entries (4-space, `, ` separator). The RHS strings in YA4 encode exactly this.
- **Name consistency:** all `Yaml`/`yaml_`/`ye_`/`yp_` names per the canonical list; `nl` (Yaml.v) and `nl_e` (examples) are both `ascii_of_nat 10` — keep them the same char.
- **Reused (confirmed):** `Schedule`/`sch_nprocs`/`sch_frontiers` (Schedule); `cardinal_subtype_full` (Theorems); `B_square_Hfin`/`cardinal_of_NoDup_nat` pattern (TransformA.v) for `yaml_vert_finite`; `Rank.v` strict-rank-⟹-acyclic pattern for `poset_s3` acyclicity; `seq_NoDup`/`length_seq`/`String.concat`/`classic` (Stdlib).
- **Execution-time checks:** `String.concat` exists in Rocq 9.1 (else local `fold_right append ""`); `clos_trans`/`clos_refl_trans` constructor names (`t_step`/`t_trans`, `rt_step`/`rt_refl`/`rt_trans`); `Compute dump …` to confirm byte output before writing the `_eq` RHS.

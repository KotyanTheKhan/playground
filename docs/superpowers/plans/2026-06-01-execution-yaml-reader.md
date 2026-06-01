# YAML Reader (lenient libnomadim parser) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A lenient Coq parser `parse_document : string -> option Document` that reads real libnomadim YAML (comments, varied indent, flow/block, extra spaces) back into the Slice-1 datatypes, with instance-level read↔write round-trip checks.

**Architecture:** Three layers — `YamlLex.v` (string → cleaned `Line` list, where leniency lives), `YamlParse.v` (field/pair parsers + document assembler over `Line`s), `YamlParseExamples.v` (round-trip + messy-acceptance tests). Parsing is structural recursion over `list ascii`.

**Tech Stack:** Rocq 9.1, Stdlib `String`/`Ascii`/`List`/`Arith`. Builds via `bash .claude/scripts/timed-build.sh`. Depends on Slice-1 `execution/Yaml.v`.

---

## Task YB0: Scaffold

**Files:**
- Create: `execution/YamlLex.v`, `execution/YamlParse.v`, `execution/YamlParseExamples.v`
- Modify: `execution/dune`, `_CoqProject`

- [ ] **Step 1: Create three stub files**

`execution/YamlLex.v`:
```coq
(* YAML lexer / line model — leniency layer (comments, indent, blank lines). *)
From Stdlib Require Import String Ascii List Arith Lia.
Import ListNotations.
Open Scope string_scope.
```
`execution/YamlParse.v`:
```coq
(* YAML parser — field/pair parsers + document assembler over cleaned lines. *)
From Stdlib Require Import String Ascii List Arith Lia.
From Execution Require Import Yaml YamlLex.
Import ListNotations.
Open Scope string_scope.
```
`execution/YamlParseExamples.v`:
```coq
(* YAML reader examples (test-only): round-trip + messy-input acceptance. *)
From Stdlib Require Import String Ascii List Arith.
From Execution Require Import Yaml YamlLex YamlParse.
Import ListNotations.
Open Scope string_scope.
```

- [ ] **Step 2: Register in `execution/dune`** — add `YamlLex`, `YamlParse`, `YamlParseExamples` to the `(modules …)` list (after `YamlExamples`).

- [ ] **Step 3: Register in `_CoqProject`** — add three lines after `execution/YamlExamples.v`:
```
execution/YamlLex.v
execution/YamlParse.v
execution/YamlParseExamples.v
```

- [ ] **Step 4: Build** — `bash .claude/scripts/timed-build.sh 120 execution/YamlParseExamples.vo 2`. Expected EXIT=0.

- [ ] **Step 5: Commit** — `git add -A && git commit -m "chore(execution): scaffold YAML reader modules"`.

---

## Task YB1: Lexer / line model (`YamlLex.v`)

**Files:** Modify `execution/YamlLex.v` (replace after the header).

- [ ] **Step 1: Write the full lexer**

```coq
(* ---- char helpers ---- *)
Definition is_space (c : ascii) : bool :=
  orb (Nat.eqb (nat_of_ascii c) 32) (Nat.eqb (nat_of_ascii c) 9).
Definition is_digit (c : ascii) : bool :=
  andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57).
Definition digit_val (c : ascii) : nat := nat_of_ascii c - 48.
Definition is_char (c : ascii) (code : nat) : bool := Nat.eqb (nat_of_ascii c) code.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with EmptyString => [] | String c r => c :: list_of_string r end.
Fixpoint string_of_list (l : list ascii) : string :=
  match l with [] => EmptyString | c :: r => String c (string_of_list r) end.

(* ---- line splitting on '\n' (code 10) ---- *)
Fixpoint split_lines (l : list ascii) : list (list ascii) :=
  match l with
  | [] => [[]]
  | c :: r => if is_char c 10
              then [] :: split_lines r
              else match split_lines r with
                   | [] => [[c]]            (* unreachable; split_lines is always nonempty *)
                   | h :: t => (c :: h) :: t
                   end
  end.

(* ---- per-line cleaning ---- *)
Definition strip_cr (l : list ascii) : list ascii :=
  filter (fun c => negb (is_char c 13)) l.
Fixpoint strip_comment (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: r => if is_char c 35 (* '#' *) then [] else c :: strip_comment r
  end.
Fixpoint measure_indent (l : list ascii) : nat * list ascii :=
  match l with
  | c :: r => if is_space c then let (n, rest) := measure_indent r in (S n, rest)
              else (0, l)
  | [] => (0, [])
  end.
Fixpoint drop_leading_space (l : list ascii) : list ascii :=
  match l with c :: r => if is_space c then drop_leading_space r else l | [] => [] end.
Definition trim_both (l : list ascii) : list ascii :=
  drop_leading_space (rev (drop_leading_space (rev l))).
Definition trim_trailing (l : list ascii) : list ascii :=
  rev (drop_leading_space (rev l)).

Record Line := { ln_indent : nat; ln_text : list ascii }.

Definition clean_one (raw : list ascii) : option Line :=
  let nocr := strip_cr raw in
  let nocomment := strip_comment nocr in
  let (ind, rest) := measure_indent nocomment in
  match trim_trailing rest with
  | [] => None
  | t => Some {| ln_indent := ind; ln_text := t |}
  end.

Definition clean_lines (s : string) : list Line :=
  fold_right (fun raw acc => match clean_one raw with Some ln => ln :: acc | None => acc end)
             [] (split_lines (list_of_string s)).

(* ---- lenient decimal ---- *)
Fixpoint nat_of_digits_aux (l : list ascii) (acc : nat) : option nat :=
  match l with
  | [] => Some acc
  | c :: r => if is_digit c then nat_of_digits_aux r (acc * 10 + digit_val c) else None
  end.
Definition nat_of_digits (l : list ascii) : option nat :=
  match l with [] => None | _ => nat_of_digits_aux l 0 end.

(* ---- boolean list-of-ascii equality ---- *)
Fixpoint la_eqb (a b : list ascii) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => andb (Nat.eqb (nat_of_ascii x) (nat_of_ascii y)) (la_eqb a' b')
  | _, _ => false
  end.
```

- [ ] **Step 2: Sanity-check by `Compute` (temporary, then REMOVE).** Add then delete:
```coq
Compute nat_of_digits (list_of_string "123").     (* Some 123 *)
Compute clean_lines "execution:
  n_procs: 2
  # a comment

  syncs:
    - [0, 1]".                                      (* 4 Lines: indents 0,2,2,4 *)
```
Confirm `nat_of_digits "123" = Some 123` and the blank+comment lines are dropped (4 `Line`s, not 6). Then DELETE both `Compute`.

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 180 execution/YamlLex.vo 2`. EXIT=0; no `Compute` left.

- [ ] **Step 4: Commit** — `git add execution/YamlLex.v && git commit -m "feat(execution): YAML lexer / line model (leniency layer)"`.

---

## Task YB2: Field & pair parsers (`YamlParse.v`, part 1)

**Files:** Modify `execution/YamlParse.v` (append after header).

- [ ] **Step 1: Write the value parsers**

```coq
(* split on first ':' *)
Fixpoint split_colon (l : list ascii) : option (list ascii * list ascii) :=
  match l with
  | [] => None
  | c :: r => if is_char c 58 (* ':' *) then Some ([], r)
              else match split_colon r with
                   | Some (k, v) => Some (c :: k, v)
                   | None => None
                   end
  end.
Definition parse_key_value (l : list ascii) : option (list ascii * list ascii) :=
  match split_colon l with
  | Some (k, v) => Some (trim_both k, trim_both v)
  | None => None
  end.

Definition match_key (key : string) (ln : Line) : bool :=
  match parse_key_value (ln_text ln) with
  | Some (k, v) => andb (la_eqb k (list_of_string key))
                        (match v with [] => true | _ => false end)
  | None => false
  end.
Definition parse_nat_field (key : string) (ln : Line) : option nat :=
  match parse_key_value (ln_text ln) with
  | Some (k, v) => if la_eqb k (list_of_string key) then nat_of_digits v else None
  | None => None
  end.

(* lenient "[a, b]" or "a, b" *)
Definition strip_brackets (l : list ascii) : list ascii :=
  let l1 := match l with c :: r => if is_char c 91 (* '[' *) then r else l | [] => l end in
  match rev l1 with
  | c :: r => if is_char c 93 (* ']' *) then rev r else l1
  | [] => l1
  end.
Fixpoint split_comma (l : list ascii) : list ascii * list ascii :=
  match l with
  | [] => ([], [])
  | c :: r => if is_char c 44 (* ',' *) then ([], r)
              else let (a, b) := split_comma r in (c :: a, b)
  end.
Definition parse_pair (l : list ascii) : option (nat * nat) :=
  let inner := strip_brackets (trim_both l) in
  let (a, b) := split_comma inner in
  match nat_of_digits (trim_both a), nat_of_digits (trim_both b) with
  | Some x, Some y => Some (x, y)
  | _, _ => None
  end.

Definition parse_seq_item (ln : Line) : option (nat * nat) :=
  match ln_text ln with
  | c :: r => if is_char c 45 (* '-' *) then parse_pair (trim_both r) else None
  | [] => None
  end.
```

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 180 execution/YamlParse.vo 2`. EXIT=0.
- [ ] **Step 3: Commit** — `git add execution/YamlParse.v && git commit -m "feat(execution): YAML field/pair value parsers"`.

---

## Task YB3: Document assembler (`YamlParse.v`, part 2)

**Files:** Modify `execution/YamlParse.v` (append).

- [ ] **Step 1: Write the assembler**

```coq
(* greedily consume leading seq-item lines *)
Fixpoint parse_pairs_block (lines : list Line) : list (nat * nat) * list Line :=
  match lines with
  | ln :: rest =>
      match parse_seq_item ln with
      | Some p => let (ps, leftover) := parse_pairs_block rest in (p :: ps, leftover)
      | None => ([], lines)
      end
  | [] => ([], [])
  end.

Fixpoint parse_exec_fields (lines : list Line) (nprocs : option nat)
                           (syncs : option (list (nat * nat))) : option YamlExecution :=
  match lines with
  | [] => match nprocs with
          | Some n => Some {| ye_nprocs := n;
                              ye_syncs := match syncs with Some s => s | None => [] end |}
          | None => None
          end
  | ln :: rest =>
      match parse_nat_field "n_procs" ln with
      | Some n => parse_exec_fields rest (Some n) syncs
      | None => if match_key "syncs" ln
                then let (ps, leftover) := parse_pairs_block rest in
                     parse_exec_fields leftover nprocs (Some ps)
                else parse_exec_fields rest nprocs syncs   (* lenient: skip unknown *)
      end
  end.

Fixpoint parse_poset_fields (lines : list Line) (nverts : option nat)
                            (edges : option (list (nat * nat))) : option YamlPoset :=
  match lines with
  | [] => match nverts with
          | Some n => Some {| yp_nverts := n;
                              yp_edges := match edges with Some e => e | None => [] end |}
          | None => None
          end
  | ln :: rest =>
      match parse_nat_field "n_vertices" ln with
      | Some n => parse_poset_fields rest (Some n) edges
      | None => if match_key "edges" ln
                then let (ps, leftover) := parse_pairs_block rest in
                     parse_poset_fields leftover nverts (Some ps)
                else parse_poset_fields rest nverts edges
      end
  end.

Definition parse_document (s : string) : option Document :=
  match clean_lines s with
  | ln :: rest =>
      if match_key "execution" ln
      then match parse_exec_fields rest None None with
           | Some e => Some (DocExecution e) | None => None end
      else if match_key "poset" ln
      then match parse_poset_fields rest None None with
           | Some p => Some (DocPoset p) | None => None end
      else None
  | [] => None
  end.
```

- [ ] **Step 2: Sanity `Compute` (temporary, then REMOVE).**
```coq
Compute parse_document "execution:
  n_procs: 2
  syncs:
    - [0, 1]".   (* Some (DocExecution {| ye_nprocs := 2; ye_syncs := [(0,1)] |}) *)
```
Confirm it yields exactly `Some (DocExecution {| ye_nprocs := 2; ye_syncs := [(0, 1)] |})`. DELETE the `Compute`.

- [ ] **Step 3: Build** — `bash .claude/scripts/timed-build.sh 180 execution/YamlParse.vo 2`. EXIT=0; no `Compute` left.
- [ ] **Step 4: Commit** — `git add execution/YamlParse.v && git commit -m "feat(execution): YAML document assembler (parse_document)"`.

---

## Task YB4: Round-trip + messy-acceptance tests (`YamlParseExamples.v`)

**Files:** Modify `execution/YamlParseExamples.v`.

**Note on round-trip scope:** the parser is lenient, so we prove **instance-level** round-trip on the three real data documents (a genuine read↔write check) by `vm_compute`. The *universal* `forall d, wf_document d -> parse_document (dump d) = Some d` is deferred (recorded in INDEX/audit as a stretch lemma — its proof needs `string_of_nat`↔`nat_of_digits` inversion plus `split_lines`/`++` commutation, a separate effort).

- [ ] **Step 1: Write the tests**

```coq
Definition exec_dim2 : YamlExecution := {| ye_nprocs := 2; ye_syncs := [(0,1)] |}.
Definition exec_4_canonical : YamlExecution :=
  {| ye_nprocs := 4; ye_syncs := [(0,1);(1,2);(2,3);(0,2)] |}.
Definition poset_s3 : YamlPoset :=
  {| yp_nverts := 6; yp_edges := [(0,4);(0,5);(1,3);(1,5);(2,3);(2,4)] |}.

(* read back exactly what we wrote (instance-level round-trip) *)
Example roundtrip_exec_dim2 :
  parse_document (dump (DocExecution exec_dim2)) = Some (DocExecution exec_dim2).
Proof. vm_compute. reflexivity. Qed.

Example roundtrip_exec_4 :
  parse_document (dump (DocExecution exec_4_canonical)) = Some (DocExecution exec_4_canonical).
Proof. vm_compute. reflexivity. Qed.

Example roundtrip_poset_s3 :
  parse_document (dump (DocPoset poset_s3)) = Some (DocPoset poset_s3).
Proof. vm_compute. reflexivity. Qed.

(* leniency: a messy hand-edited variant parses to the SAME document *)
Definition messy_exec : string :=
"# an execution file
execution:
  n_procs:   2

  syncs:
    -  [0,1]   # the only sync
".

Example accept_messy_exec :
  parse_document messy_exec = Some (DocExecution exec_dim2).
Proof. vm_compute. reflexivity. Qed.

Definition messy_poset : string :=
"poset:
  n_vertices: 6
  edges:
    - [0,4]
    - [0, 5]
    -   [1,3]
    - [1, 5]
    - [2,3]
    - [2, 4]
".

Example accept_messy_poset :
  parse_document messy_poset = Some (DocPoset poset_s3).
Proof. vm_compute. reflexivity. Qed.
```

- [ ] **Step 2: Build** — `bash .claude/scripts/timed-build.sh 300 execution/YamlParseExamples.vo 2`. EXIT=0.
  - If any `vm_compute; reflexivity` FAILS, run the matching `Compute parse_document <input>.` to see the actual result, and fix the *parser* (`YamlLex.v`/`YamlParse.v`) leniency bug it reveals — NOT the expected RHS (the expected `Document` values are correct by construction). Re-build the dependency then this file. Do not weaken a test to pass.
- [ ] **Step 3: Commit** — `git add execution/YamlParseExamples.v && git commit -m "test(execution): YAML reader round-trip + messy-input acceptance"`.

---

## Task YB5: Export, whole-project build, INDEX, audit

**Files:** Modify `execution/Execution.v`, `docs/INDEX.md`.

- [ ] **Step 1: Export the two non-test modules** — in `execution/Execution.v`, append `YamlLex YamlParse` to the `Require Export` list (after `Yaml`). Do NOT export `YamlParseExamples`.

- [ ] **Step 2: Whole-project build** — `bash .claude/scripts/timed-build.sh 1800 @all 4`. EXIT=0. (Pre-existing dune loadpath-remap warnings are benign.)

- [ ] **Step 3: Audit** — temporarily register a scratch `execution/YamlReaderAudit.v` (add to `dune` + `_CoqProject`) containing:
```coq
From Execution Require Import YamlParse YamlParseExamples.
Print Assumptions parse_document.
Print Assumptions roundtrip_exec_dim2.
Print Assumptions accept_messy_poset.
```
Build it via the wrapper, capture the `Print Assumptions` output (expected: `Closed under the global context` — axiom-free, pure computable parsing), then REMOVE the scratch file and revert its `dune`/`_CoqProject` registration.

- [ ] **Step 4: INDEX** — add a `#### execution/YamlLex.v + YamlParse.v — YAML reader (lenient)` subsection to `docs/INDEX.md` (after the Yaml subsection) with a name/meaning table covering `clean_lines`, `nat_of_digits`, `parse_pair`, `parse_nat_field`, `parse_document`, and the round-trip/acceptance examples; note the universal round-trip is deferred.

- [ ] **Step 5: Commit** — `git add execution/Execution.v docs/INDEX.md && git commit -m "feat(execution): export YAML reader + INDEX entry"`.

---

## Self-Review (checked against the spec)

- **Spec coverage:** Layer 1 (`YamlLex.v`) → YB1; Layer 2 field/pair parsers → YB2; Layer 3 assembler → YB3; instance round-trip + acceptance examples → YB4; export/INDEX/audit → YB0+YB5. Universal `parse_dump_roundtrip` explicitly deferred (spec permits instance-level fallback). All mapped.
- **Name consistency:** `is_char`/`is_space`/`is_digit`/`digit_val`, `list_of_string`/`string_of_list`, `split_lines`, `clean_lines`, `nat_of_digits`, `la_eqb` (YamlLex) used verbatim in YamlParse; `parse_key_value`/`match_key`/`parse_nat_field`/`parse_pair`/`parse_seq_item`/`parse_pairs_block`/`parse_exec_fields`/`parse_poset_fields`/`parse_document` consistent across YB2–YB4. Field keys `"n_procs"`/`"syncs"`/`"n_vertices"`/`"edges"`/`"execution"`/`"poset"` match `dump`'s output in `Yaml.v`.
- **No placeholders:** every code step shows complete code; every build step gives the exact wrapper command and EXIT=0 expectation.
- **Type consistency:** `parse_document : string -> option Document`; `DocExecution`/`DocPoset`/`ye_nprocs`/`ye_syncs`/`yp_nverts`/`yp_edges` exactly as defined in Slice-1 `Yaml.v`.

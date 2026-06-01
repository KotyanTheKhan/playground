# YAML Reader (lenient libnomadim parser) — Design (Sub-project C, file-I/O slice 2)

**Date:** 2026-06-01
**Branch:** `execution_poset`
**Depends on:** Slice 1 — `execution/Yaml.v` (`YamlExecution`/`YamlPoset`/`Document`, `dump`, `wf_yaml_execution`/`wf_yaml_poset`, `string_of_nat`).
**Paper / format:** libnomadim on-disk YAML (`data/*.yaml`), yaml-cpp block-map emitter.

## Goal & framing

Slice 1 made *write* possible (`dump : Document -> string`, byte-faithful). This slice makes
*read* possible: a **lenient** parser

```coq
parse_document : string -> option Document
```

that ingests real libnomadim YAML — not only our own canonical `dump` bytes, but also
hand-edited / other-tool output with comments, blank lines, varied indentation, optional
spaces, and either flow (`[a, b]`) or block sequence items. It returns `None` only on
genuinely malformed input.

**Leniency is the explicit choice** (user-selected over a strict round-trip parser). The
cost: a full bijective round-trip is not a theorem. The compensating guarantee we DO prove
is **one-directional soundness** on the canonical format:

```coq
Theorem parse_dump_roundtrip :
  forall d : Document, wf_document d -> parse_document (dump d) = Some d.
```

i.e. anything we emit, we read back exactly. Leniency only *adds* accepted inputs beyond
`dump`'s image, so this theorem still holds and is the real correctness anchor. We also
give *acceptance examples* (a commented / re-indented / extra-spaced variant of each data
file parses to the same `Document`) as executable `Example`s — evidence of leniency without
a universal leniency theorem (which would require formalizing "all of YAML", out of scope).

## Representation choice

Parse over `list ascii`, not `string` with `substring`/index arithmetic. Convert once
(`list_of_string : string -> list ascii`, and back), then all parsing is structural
recursion on the char list — far cleaner in Coq, and the round-trip proof reduces by
`vm_compute` on closed `dump` output. Char classification (`is_space`, `is_digit`,
`digit_val`, `is_newline`) via `nat_of_ascii` comparisons.

## Architecture — three layers

### Layer 1 — Lexer / line model (`execution/YamlLex.v`)

Turn raw text into a clean list of *logical lines*, each carrying its indentation and
trimmed content. This is where leniency lives.

```coq
Record Line := { ln_indent : nat; ln_text : list ascii }.   (* text = content after indent, comment/space-trimmed *)

list_of_string  : string -> list ascii
string_of_list  : list ascii -> string          (* for messages/tests; inverse of above *)
nat_of_digits   : list ascii -> option nat       (* lenient decimal; None if any non-digit *)
split_lines     : list ascii -> list (list ascii)   (* split on '\n'; '\r' stripped *)
strip_comment   : list ascii -> list ascii       (* drop from first unquoted '#' to EOL *)
measure_indent  : list ascii -> nat * list ascii  (* count/strip leading spaces *)
trim_trailing   : list ascii -> list ascii        (* drop trailing spaces *)
clean_lines     : string -> list Line             (* compose: split, strip comments, measure indent, trim, DROP blank *)
```

Leniency handled here: blank lines dropped; `# …` comments removed; `\r` and trailing
spaces stripped; indentation captured as a number, not assumed to be exactly 2.

### Layer 2 — Field / value parsers (`execution/YamlParse.v`)

Small total parsers over a single `Line`'s `ln_text`:

```coq
parse_key_value : list ascii -> option (list ascii * list ascii)
   (* split on first ':' ; returns (key, value) each trimmed; value may be empty *)
parse_nat_field : forall (key : string), Line -> option nat
   (* line is "key: N" (any spacing); returns N *)
parse_pair      : list ascii -> option (nat * nat)
   (* lenient "[a, b]" : optional spaces around '[' ']' ',' ; also accepts "a, b" without brackets *)
parse_seq_item  : Line -> option (nat * nat)
   (* line is "- [a, b]" (leading "- " optional-spaced) ; delegates to parse_pair *)
match_key       : forall (key : string), Line -> bool
   (* line is exactly "key:" (a sequence/section header) modulo spacing *)
```

### Layer 3 — Document assembler (`execution/YamlParse.v`)

```coq
parse_pairs_block : nat -> list Line -> option (list (nat*nat) * list Line)
   (* consume consecutive seq-item lines indented deeper than the given header indent *)
parse_execution   : list Line -> option YamlExecution
   (* expects an n_procs field and a syncs: block in either order; lenient on order *)
parse_poset       : list Line -> option YamlPoset
parse_document    : string -> option Document
   (* clean_lines; dispatch on the first content line: "execution:" -> DocExecution,
      "poset:" -> DocPoset; else None *)
```

`wf_document d := match d with DocExecution e => wf_yaml_execution e | DocPoset p => wf_yaml_poset p end`.

## Correctness

- **`parse_dump_roundtrip`** (the theorem): `forall d, wf_document d -> parse_document (dump d) = Some d`.
  Strategy: `dump d` is a closed computation; for the *concrete* data instances the proof is
  `vm_compute; reflexivity`. For the *universal* statement we prove it by structural case on
  `d` and reduction lemmas connecting each parser layer to its printer counterpart
  (`parse_nat_field key (line of "key: " ++ string_of_nat n) = Some n`, `parse_pair` ∘
  `pair_line` = `Some`, `parse_pairs_block` ∘ `map pair_line` = the list). If the fully
  universal proof proves heavy, we FALL BACK to proving it for the three real data documents
  (`exec_dim2`, `exec_4_canonical`, `poset_s3`) by `vm_compute` — still a genuine read↔write
  check, just instance-level — and record the universal form as a deferred lemma. Decide per
  effort budget; prefer universal.
- **Acceptance examples** (`execution/YamlParseExamples.v`, test-only): for each data file, a
  *messy* variant string (leading comment line, a blank line, `n_procs:   2` extra spaces,
  `-  [0,1]` no inner space) parses via `parse_document` to exactly the same `Document` as the
  clean file — by `vm_compute; reflexivity`.

## Files, wiring, testing

- New: `execution/YamlLex.v`, `execution/YamlParse.v`, `execution/YamlParseExamples.v` (test-only).
- `execution/dune` + `_CoqProject`: add the three modules.
- `execution/Execution.v`: export `YamlLex YamlParse` (not the examples).
- `docs/INDEX.md`: add a "YAML reader" subsection.
- Every file builds via the wrapper; whole-`@all` green; **zero `Admitted`** (any instance-level
  fallback is an honest *proved* `Example`, never an `admit`). Files <500 lines, each `Qed` <5 min.
- `Print Assumptions parse_document parse_dump_roundtrip` recorded — expected axiom-free (pure
  computable string parsing), no classical/choice.

## Out of scope (later micro-slices)

- OCaml `Extraction` + a `read_file`/`write_file` shim for real on-disk I/O (user deferred it
  this round; the pure `string`-level reader is the deliverable now).
- A *universal* leniency theorem ("parser accepts all valid YAML"); we give examples, not a
  proof over all of YAML.
- Quoted scalars, multi-document streams, anchors/aliases, nested maps beyond this two-level
  format — yaml-cpp emits none of these for libnomadim, so the parser may reject them.

## Acceptance criteria

1. `YamlLex.v`: lexer/line model; `clean_lines` drops blanks, strips comments + `\r` + trailing
   spaces, measures indent. Zero admits.
2. `YamlParse.v`: `parse_pair`/`parse_nat_field`/`parse_execution`/`parse_poset`/`parse_document`
   (lenient). `parse_dump_roundtrip` (universal, or instance-level fallback recorded). Zero admits.
3. `YamlParseExamples.v`: messy-variant acceptance `Example`s for all three data files. Zero admits.
4. Whole-project green; `Execution.v` exports the two non-test modules; INDEX updated;
   `Print Assumptions` recorded.

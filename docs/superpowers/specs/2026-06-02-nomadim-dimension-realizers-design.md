# nomadim: general dimension, realizers, and meta fields — design

Date: 2026-06-02
Branch: `feat/nomadim-dimension`

## Goal

Extend the `nomadim/` C++ project (currently a dimension-≤2 tool) with:

1. **General poset dimension** (including > 2), computed by coloring the
   hypergraph of incomparable critical pairs.
2. **Realizers** — find one realizer, and enumerate all minimum realizers
   (reported as colorings paired with the linear extensions they induce).
3. **`meta` file-format fields** for notes/comments, the computed dimension,
   and realizers (cached annotations).

Exposed across all three surfaces: **C++ library + CLI + WASM/web editor**.

## Math foundation

- **Critical pair** `(x, y)`: `x`, `y` incomparable, with `D(x) ⊆ D(y)` and
  `U(y) ⊆ U(x)` (down-sets / up-sets, strict). The existing
  `find_critical_pairs` (faithful to upstream) is reused unchanged.
- **Reversible set** `S` of critical pairs: the order `P` augmented with reverse
  edges `{ y → x : (x, y) ∈ S }` remains acyclic. Singletons are always
  reversible (reversing one incomparable pair cannot close a cycle).
- **Hyperedge**: a *minimal* non-reversible set of critical pairs (an
  alternating cycle). The hypergraph `H` has critical pairs as vertices and
  minimal non-reversible sets as edges.
- **dim(P) = χ(H)**: the fewest colors such that no hyperedge is monochromatic.
  Each color class is a reversible set and yields one linear extension of a
  realizer; the linear extensions' intersection is exactly `P`.
- Edge cases: a chain (no critical pairs) → dimension 1; the empty poset
  (`n = 0`) → 0. These are handled before the coloring search.

This is the Felsner–Trotter hypergraph-coloring characterization of dimension.

## Approach (chosen: B)

Primary engine is hypergraph coloring (Approach A). In addition, a **brute-force
oracle** — enumerate all linear extensions, find a minimum-size subset whose
intersection equals `P` — is built **for tests only** (not linked into the CLI
or WASM). It provides an independent ground-truth dimension, validates that
induced realizers actually realize `P`, and lets the standard example Sₙ
(dimension = n) serve as a golden check.

## Modules (C++ core)

| File | Contents |
|------|----------|
| `include/nomadim/order_relation.hpp` | Extract the dense transitive-closure `StrictRel` currently inside `realizer.cpp` (add-and-close with cycle detection, `linearize`). Shared by realizer + hypergraph. |
| `include/nomadim/hypergraph.hpp`, `src/hypergraph.cpp` | `is_reversible(P, set)`, `enumerate_hyperedges(...)` (minimal alternating cycles), `chromatic_number(...)`, `enumerate_min_colorings(...)`. |
| `include/nomadim/dimension.hpp`, `src/dimension.cpp` | All existing functions kept; add `DimensionResult dimension(g, Caps)`. |
| `include/nomadim/realizer.hpp`, `src/realizer.cpp` | Keep the dim-2 `find_realizer` for back-compat; add `find_one_realizer(g, Caps)` and `find_all_realizers(g, Caps)` built on min colorings. |
| `include/nomadim/oracle.hpp`, `src/oracle.cpp` | **Test-only** brute-force linear-extension enumeration + minimum realizer. Not referenced by CLI/WASM. |

## Data types

```cpp
struct Caps {                 // all overridable; sane defaults
  int max_vertices = 16;
  int max_critical_pairs = 64;
  int max_results = 1000;     // colorings / realizers cap
};

using LinearExt = std::vector<int>;          // permutation, least element first
using RealizerLE = std::vector<LinearExt>;   // `dim` linear extensions

struct Coloring {                            // one minimum proper coloring of H
  std::vector<std::vector<critical_pair>> classes;  // dim reversible classes
  RealizerLE realizer;                       // induced (deterministic topo per class)
};

struct DimensionResult {
  int dimension;
  std::vector<critical_pair> critical_pairs;
  std::vector<std::vector<int>> hyperedges;  // indices into critical_pairs
  std::vector<Coloring> colorings;           // "both, labeled"
};
```

- `find_one_realizer` → the first `Coloring.realizer`.
- `find_all_realizers` → all distinct minimum colorings, each with its induced
  realizer. The induced linear extension per class is a deterministic
  smallest-index-first topological sort, so each coloring yields exactly one
  (stable, dedup-able) realizer.
- Exceeding any cap → `throw std::runtime_error("...too large: <what> exceeds
  <cap>")`.

## File format — `meta` (cached annotations)

New top-level key alongside `execution` / `poset`:

```yaml
meta:
  notes: "free text, user-authored"
  dimension: 3
  source_hash: "ab12cd…"      # hash of the poset edges these results came from
  realizers:
    - - [0, 1, 2, 3]
      - [3, 2, 1, 0]
      - [2, 0, 3, 1]
```

- `notes` is authoritative user text, always round-tripped.
- `dimension` / `realizers` are a **cache**: written on save with a
  `source_hash` of the poset edges. On load, if `source_hash` ≠ the current
  poset's hash, they are treated as stale and recomputed (never trusted blindly).
  Missing/empty `meta` is valid.
- `Document` gains `std::optional<Meta> meta`. `parse_document` reads it; a new
  `dump_document` writes execution + poset + meta together.

```cpp
struct Meta {
  std::optional<std::string> notes;
  std::optional<int> dimension;
  std::optional<std::vector<RealizerLE>> realizers;
  std::optional<std::string> source_hash;
};
```

## CLI

New subcommand (existing `check` stays as the dim-≤2 boolean):

```
nomadim dimension <file> [--realizers] [--all] [--max-vertices N] [-o out.yaml]
```

- bare: print the dimension number (exit 0).
- `--realizers`: also print one realizer.
- `--all`: print every minimum coloring + induced realizer.
- `-o`: write a document with `meta` filled in (dimension, realizers,
  source_hash), preserving any existing `notes`.
- Cap exceeded → stderr message + nonzero exit.

## WASM / editor

New bindings (keep `findRealizer` for back-compat):

- `dimension(adjJson, capsJson?)` → `{dimension}` or `{error}`
- `findOneRealizer(adjJson, capsJson?)` → `{dimension, realizer}` or `{error}`
- `allRealizers(adjJson, capsJson?)` → `{dimension, colorings:[{classes,realizer}], hyperedges, error?}`
- `parseDocument` / new `dumpDocument` carry `meta`.

Editor UI:

- A **dimension panel** showing the number.
- A **realizers list** (selectable; each realizer highlightable on the poset).
- A **notes** text field; `meta` persisted on save.
- The explicit `hyperedges` data is exposed to JS; rendering a basic
  **critical-pair conflict list** is in scope. A full hypergraph drawing is a
  stretch goal (not required for completion).

## Guards

Configurable `Caps` with clear errors (chosen option). Defaults: `max_vertices
16`, `max_critical_pairs 64`, `max_results 1000`. CLI flag and WASM `capsJson`
override them. Library throws `std::runtime_error`; CLI prints to stderr and
exits nonzero; WASM returns `{error: "..."}` so the editor surfaces it
gracefully.

## Testing

- **Golden:** standard example Sₙ (2n elements `a_1..a_n, b_1..b_n`, `a_i < b_j`
  iff `i ≠ j`; dimension = n) for n = 2, 3, 4 → exact dimension.
- **Oracle:** brute-force minimum realizer agrees with `dimension()` on all small
  / random posets; `dimension == 2 ⟺ is_dim2`; `dimension == 1 ⟺ chain`.
- **Realizer validity:** every induced realizer has size = dimension and
  intersection exactly = `P`.
- **Hyperedges:** minimal and non-reversible on known posets (antichains,
  N-poset).
- **IO:** `meta` round-trips; a stale `source_hash` forces recompute.
- **Caps:** oversized input throws the documented error.

## Out of scope (YAGNI)

- Parallelism for the dimension/realizer search (the existing `enumerate`
  threading is untouched).
- Full interactive hypergraph visualization in the editor (stretch only).
- Trusting cached `meta` results without a `source_hash` match.

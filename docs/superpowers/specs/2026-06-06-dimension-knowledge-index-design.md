# Order-Dimension Knowledge Index — Design

**Date:** 2026-06-06
**Status:** Approved (design phase)

## Goal

Build a comprehensive, standalone scholarly **knowledge index of poset
order-dimension theory**: facts, definitions, theorems, conjectures, and
algorithms, each tied to its authoritative source. The index is meant to be a
durable reference for the project — broad coverage of dimension theory regardless
of immediate relevance to any one proof, but with a lightweight cross-link to
results already formalized in this repo.

This serves the project's north star (logical clocks cheaper than vector clocks,
via execution-poset dimension) indirectly: it gives every future formalization
task a single place to look up what is known, what is open, and what has already
been mechanized here — without re-deriving the literature each session.

## Scope

**In scope:** order dimension of partially ordered sets — Dushnik–Miller
dimension and its core machinery (realizers, critical pairs, alternating cycles,
standard examples), bounds, computational complexity, dimension of special poset
classes (interval orders, planar posets, Boolean lattices, bipartite posets), and
the major variants (interval dimension, fractional dimension, Boolean dimension,
local dimension). Definitions and supporting lemmas (Dilworth/width, comparability
graphs) are included **only** to the extent dimension theory references them.

**Out of scope (YAGNI):**
- A programmatic query layer (no YAML/JSON records, no generator script).
- General order theory beyond what dimension proofs need (lattice theory, fixed
  points, general Dilworth/Mirsky development).
- An auto-rendering / publishing pipeline.

## Organizing principle

**By topic, with typed entries** (chosen over "by entry type" and "by source").

The master file follows the conceptual spine of dimension theory. Within each
topical section, every item carries a **type tag** and a **stable ID**, so the
file reads like a textbook's logical structure *and* stays greppable by type
(`grep '\[CONJ\]'` lists every open problem; `grep '\[THM\]'` every theorem).

Type tags:
- `[DEF]` — definition
- `[FACT]` — elementary/folklore fact
- `[THM]` — named or numbered theorem
- `[LEM]` — supporting lemma worth indexing on its own
- `[ALG]` — algorithm / complexity result
- `[CONJ]` — conjecture / open problem

Proposed section spine of `docs/references/dimension-index.md`:

1. **Foundations** — posets, linear extensions, realizers; Dushnik–Miller
   definition of dimension; dimension as intersection of linear extensions;
   critical pairs and alternating cycles; the characterization `dim ≤ 2 ⟺
   incomparability graph is a comparability graph` / permutation graphs.
2. **Standard examples & lower bounds** — standard example `S_n` (dim = n);
   constructions forcing high dimension.
3. **Upper bounds & inequalities** — `dim ≤ width`; Hiraguchi's theorem
   `dim ≤ ⌊n/2⌋`; Hiraguchi/Trotter removal inequalities (point, chain,
   antichain); product bound `dim(P×Q) ≤ dim P + dim Q`.
4. **Computational complexity** — `dim ≤ 2` poly-time recognition;
   Yannakakis: deciding `dim ≥ 3` is NP-complete.
5. **Special classes** — interval orders & interval dimension; planar posets
   (Baker–Fishburn–Roberts `dim ≤ 2` with 0,1; Kelly's unbounded-dimension
   planar posets); Boolean lattice `2^[n]` dimension; bipartite posets.
6. **Variants** — interval dimension; fractional dimension
   (Brightwell–Scheinerman; Removable Pair proven fractionally, BHPT 2014);
   Boolean dimension; local dimension.
7. **Open problems** — Removable Pair Conjecture (integer case) and others.

Sections are added/renamed as the corpus dictates; this is the starting spine.

## Entry schema

Every indexed item uses this shape:

```markdown
#### [THM] dim-hiraguchi — Hiraguchi's Theorem
**Statement.** For a poset P with |P| ≥ 4, dim(P) ≤ ⌊|P|/2⌋.
**Status.** Proven (Hiraguchi 1951). Tight.
**Depends on.** [THM dim-le-width], [LEM removable-antichain]
**Sources.** Hiraguchi 1951 [H51]; Trotter 1992 §3 [T92]; Kimble 1973 [K73].
**In this repo.** `hiraguchi_bound_direct` (1 honest classical admit) —
  posets/dimension/.../Hiraguchi.v
**Notes.** Optional clarifications, proof sketch pointers, caveats.
```

Rules:
- **Stable ID** is kebab-case, unique within the file, prefixed by topic where
  helpful (`dim-`, `frac-`, `bool-`). IDs are referenced in `Depends on.` lines.
- `Status.` is one of: *Proven* (with year/attribution), *Open*, *Refuted*,
  *Partial* (state what part).
- `In this repo.` is present **only** when a corresponding Coq result exists;
  it names the lemma, its admit/soundness status, and the file path. Omit
  otherwise.
- `Sources.` cites BibTeX keys defined in `sources.bib`.

## Source acquisition

`docs/references/sources.bib` is the provenance backbone (BibTeX). Acquisition
policy ("catalog + download what's open"):

- **Download** freely-available PDFs into `docs/references/`: arXiv preprints,
  open surveys, theses (e.g. Kimble MIT DSpace), Hiraguchi's Kanazawa scans,
  papers on author homepages (Trotter's site). Filenames follow the existing
  convention (`author-year-shorttitle.pdf`).
- **Catalog only** for paywalled/book items: Trotter's 1992 book
  *Combinatorics and Partially Ordered Sets: Dimension Theory*, JSTOR/Springer
  papers. These get a full BibTeX entry + link.
- Produce a **hand-fetch list** — a clearly marked `## Hand-fetch (paywalled)`
  section at the end of `dimension-index.md` listing every paywalled item the
  user should obtain manually, with title, citation, and best link.

### Backbone corpus to target

**Books**
- W. T. Trotter, *Combinatorics and Partially Ordered Sets: Dimension Theory*,
  Johns Hopkins Univ. Press, 1992 — the canonical text (catalog; hand-fetch).
- B. Schröder, *Ordered Sets: An Introduction* (background, catalog).
- Caspard, Leclerc, Monjardet, *Finite Ordered Sets* (background, catalog).
- Davey & Priestley, *Introduction to Lattices and Order* (background, catalog).

**Foundational papers**
- Dushnik & Miller, *Partially ordered sets*, Amer. J. Math. 63 (1941) — the
  definition of dimension and realizers.
- Hiraguchi, *On the dimension of partially ordered sets* (1951) and *On the
  dimension of orders* (1955) — Kanazawa scans (download).
- Yannakakis, *The complexity of the partial order dimension problem* (1982).
- Rabinovitch & Rival — alternating cycles / critical pairs.
- Kelly — planar posets of unbounded dimension.
- Baker, Fishburn, Roberts — planar posets with 0 and 1 have dim ≤ 2.

**Surveys**
- Trotter, "Partially ordered sets" chapter, *Handbook of Combinatorics* (1995).
- Trotter, *Dimension for Posets and Chromatic Number for Graphs* (the "149"
  survey — already saved at `docs/references/trotter-149-dimension-chromatic.pdf`).
- An interval-orders survey.

**Variants / recent**
- Brightwell & Scheinerman — fractional dimension.
- Biró, Hamburger, Pór, Trotter (2014) — Removable Pair Conjecture proven for
  fractional dimension.
- Recent arXiv on Boolean dimension and local dimension.

The existing `docs/references/hiraguchi-sources.md` is folded into the index /
`sources.bib` and kept as-is (no deletion).

## Workflow & deliverables

1. Assemble `docs/references/sources.bib`; download open PDFs into
   `docs/references/`; emit the hand-fetch list of paywalled items.
2. Read each accessible source; extract typed entries into the master file
   `docs/references/dimension-index.md` following the section spine + schema.
3. Cross-link `Depends on.` edges and populate `In this repo.` lines by checking
   the project's existing Coq dimension results (`posets/dimension/`, `docs/INDEX.md`,
   `docs/critical-review.md`).
4. Commit. The master Markdown file is the single source of truth; `sources.bib`
   and the PDFs are supporting material.

**Primary deliverable:** `docs/references/dimension-index.md`.
**Supporting:** `docs/references/sources.bib`, downloaded PDFs, hand-fetch list.

## Success criteria

- The index covers all seven topical sections with the major theorems,
  conjectures, and definitions of each.
- Every entry is sourced (a BibTeX key in `sources.bib`).
- Open problems are clearly tagged `[CONJ]` and findable by grep.
- Results already formalized in this repo carry an `In this repo.` line.
- A clear hand-fetch list tells the user exactly which paywalled sources to get
  by hand, so coverage gaps are explicit rather than silent.

## Risks / open questions

- **Coverage completeness vs. literature size.** "Comprehensive" is bounded by
  what is accessible; the hand-fetch list makes gaps explicit. We do not claim
  exhaustiveness of every paper ever written on dimension.
- **Accuracy of extracted statements.** Theorems are transcribed from sources;
  where a statement is paraphrased or simplified, the `Notes.` line flags it.
  No statement is invented — if a source can't be read, the entry is marked
  *pending source* rather than guessed.

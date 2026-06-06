# Order-Dimension Knowledge Index — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a comprehensive, sourced Markdown knowledge index of poset
order-dimension theory (facts, definitions, theorems, conjectures, algorithms),
backed by a BibTeX source file and downloaded open-access PDFs.

**Architecture:** A single master file `docs/references/dimension-index.md`
organized by topic (7 sections) with type-tagged entries
(`[DEF]/[FACT]/[THM]/[LEM]/[ALG]/[CONJ]`), each carrying a stable ID,
`Depends on.` links, sourced citations (BibTeX keys), and an optional
`In this repo.` cross-link to formalized Coq results. Provenance lives in
`docs/references/sources.bib`; open PDFs are downloaded alongside; paywalled
items are listed for manual fetch.

**Tech Stack:** Markdown, BibTeX, `curl` for downloads, `grep`/`awk` for
verification. No build step. This is content work — "tests" are structural
checks (bib parses, every entry sourced, IDs unique, conjectures greppable).

Spec: `docs/superpowers/specs/2026-06-06-dimension-knowledge-index-design.md`

---

## File structure

- Create: `docs/references/sources.bib` — BibTeX provenance backbone.
- Create: `docs/references/dimension-index.md` — the master index (primary deliverable).
- Download into: `docs/references/*.pdf` — open-access PDFs (existing convention `author-year-shorttitle.pdf`).
- Keep as-is: `docs/references/hiraguchi-sources.md` (folded in by reference, not deleted).
- Keep as-is: existing `trotter-*.pdf` files.

---

## Task 1: Scaffold sources.bib

**Files:**
- Create: `docs/references/sources.bib`

- [ ] **Step 1: Write the BibTeX backbone**

Create `docs/references/sources.bib` with the following entries (these are the
known-good citations; add more as later tasks surface them):

```bibtex
% ---- Books ----
@book{T92,
  author    = {William T. Trotter},
  title     = {Combinatorics and Partially Ordered Sets: Dimension Theory},
  publisher = {Johns Hopkins University Press},
  year      = {1992},
  series    = {Johns Hopkins Studies in the Mathematical Sciences},
  note      = {Canonical text. Paywalled/book -- hand-fetch.}
}
@book{Schroder03,
  author    = {Bernd S. W. Schr{\"o}der},
  title     = {Ordered Sets: An Introduction},
  publisher = {Birkh{\"a}user},
  year      = {2003},
  note      = {Background. Hand-fetch.}
}
@book{CLM12,
  author    = {Nathalie Caspard and Bruno Leclerc and Bernard Monjardet},
  title     = {Finite Ordered Sets: Concepts, Results and Uses},
  publisher = {Cambridge University Press},
  year      = {2012},
  note      = {Background. Hand-fetch.}
}
@book{DP02,
  author    = {B. A. Davey and H. A. Priestley},
  title     = {Introduction to Lattices and Order},
  edition   = {2nd},
  publisher = {Cambridge University Press},
  year      = {2002},
  note      = {Background. Hand-fetch.}
}

% ---- Foundational papers ----
@article{DM41,
  author  = {Ben Dushnik and E. W. Miller},
  title   = {Partially ordered sets},
  journal = {American Journal of Mathematics},
  volume  = {63},
  number  = {3},
  pages   = {600--610},
  year    = {1941},
  doi     = {10.2307/2371374},
  note    = {Definition of dimension and realizers. JSTOR -- hand-fetch.}
}
@article{H51,
  author  = {Toshio Hiraguchi},
  title   = {On the dimension of partially ordered sets},
  journal = {Science Reports of the Kanazawa University},
  volume  = {1},
  pages   = {77--94},
  year    = {1951},
  url     = {http://scirep.w3.kanazawa-u.ac.jp/articles/01-02-001.pdf},
  note    = {Open scan -- download.}
}
@article{H55,
  author  = {Toshio Hiraguchi},
  title   = {On the dimension of orders},
  journal = {Science Reports of the Kanazawa University},
  volume  = {4},
  pages   = {1--20},
  year    = {1955},
  url     = {http://scirep.w3.kanazawa-u.ac.jp/articles/04-01-001.pdf},
  note    = {Open scan -- download.}
}
@article{Yannakakis82,
  author  = {Mihalis Yannakakis},
  title   = {The complexity of the partial order dimension problem},
  journal = {SIAM Journal on Algebraic and Discrete Methods},
  volume  = {3},
  number  = {3},
  pages   = {351--358},
  year    = {1982},
  doi     = {10.1137/0603036},
  note    = {dim >= 3 is NP-complete. Paywalled -- hand-fetch.}
}
@article{Trotter75,
  author  = {William T. Trotter},
  title   = {Inequalities in dimension theory for posets},
  journal = {Proceedings of the American Mathematical Society},
  volume  = {47},
  number  = {2},
  pages   = {311--316},
  year    = {1975},
  doi     = {10.2307/2039736},
  note    = {Saved: docs/references/trotter-1975-inequalities-dimension.pdf.}
}
@phdthesis{K73,
  author  = {Roger J. Kimble},
  title   = {Extremal Problems in Dimension Theory for Partially Ordered Sets},
  school  = {Massachusetts Institute of Technology},
  year    = {1973},
  url     = {https://dspace.mit.edu/bitstream/handle/1721.1/82903/30083917-MIT.pdf},
  note    = {Open (MIT DSpace) -- download. OCR poor.}
}

% ---- Surveys ----
@incollection{TrotterHandbook95,
  author    = {William T. Trotter},
  title     = {Partially ordered sets},
  booktitle = {Handbook of Combinatorics},
  editor    = {R. L. Graham and M. Gr{\"o}tschel and L. Lov{\'a}sz},
  publisher = {Elsevier / MIT Press},
  pages     = {433--480},
  year      = {1995},
  note      = {Survey. Hand-fetch.}
}
@incollection{Trotter149,
  author    = {William T. Trotter},
  title     = {Dimension for Posets and Chromatic Number for Graphs},
  booktitle = {50 Years of Combinatorics, Graph Theory, and Computing},
  year      = {2019},
  url       = {https://trotter.math.gatech.edu/papers/149-Dimension_and_chromatic_number.pdf},
  note      = {Saved: docs/references/trotter-149-dimension-chromatic.pdf.}
}

% ---- Special classes ----
@article{BFR72,
  author  = {Kirby A. Baker and Peter C. Fishburn and Fred S. Roberts},
  title   = {Partial orders of dimension 2},
  journal = {Networks},
  volume  = {2},
  number  = {1},
  pages   = {11--28},
  year    = {1972},
  doi     = {10.1002/net.3230020103},
  note    = {Planar posets with 0 and 1 have dim <= 2. Paywalled -- hand-fetch.}
}
@article{Kelly81,
  author  = {David Kelly},
  title   = {On the dimension of partially ordered sets},
  journal = {Discrete Mathematics},
  volume  = {35},
  pages   = {135--156},
  year    = {1981},
  doi     = {10.1016/0012-365X(81)90203-X},
  note    = {Planar posets of unbounded dimension. Paywalled -- hand-fetch.}
}

% ---- Variants ----
@article{BS92,
  author  = {Graham R. Brightwell and Edward R. Scheinerman},
  title   = {Fractional dimension of partial orders},
  journal = {Order},
  volume  = {9},
  pages   = {139--158},
  year    = {1992},
  doi     = {10.1007/BF00814405},
  note    = {Fractional dimension. Paywalled -- hand-fetch.}
}
@article{BHPT14,
  author  = {Csaba Bir{\'o} and Peter Hamburger and Attila P{\'o}r and William T. Trotter},
  title   = {The Proof of the Removable Pair Conjecture for Fractional Dimension},
  journal = {Electronic Journal of Combinatorics},
  volume  = {21},
  number  = {1},
  pages   = {P1.63},
  year    = {2014},
  url     = {https://doi.org/10.37236/3859},
  note    = {Open (EJC) -- download.}
}
```

- [ ] **Step 2: Verify the bib parses and entry count**

Run:
```bash
grep -c '^@' docs/references/sources.bib
awk '/^@/{c++} END{print c" entries"}' docs/references/sources.bib
```
Expected: `16` (4 books + 6 foundational + 2 surveys + 2 special + 2 variants).
If `bibtool` is available, also run `mise exec -- bibtool docs/references/sources.bib >/dev/null && echo OK` (optional; skip if not installed).

- [ ] **Step 3: Verify keys are unique**

Run:
```bash
grep -oE '^@[a-z]+\{[^,]+' docs/references/sources.bib | sed 's/.*{//' | sort | uniq -d
```
Expected: no output (no duplicate keys).

- [ ] **Step 4: Commit**

```bash
git add docs/references/sources.bib
git commit -m "docs(refs): BibTeX backbone for the order-dimension index"
```

---

## Task 2: Download open-access PDFs + build hand-fetch list

**Files:**
- Download: `docs/references/*.pdf`
- Create (stub): `docs/references/dimension-index.md` (hand-fetch section only for now)

- [ ] **Step 1: Download the open PDFs**

Run each; a download is "good" if the file is a non-trivial PDF (first bytes `%PDF`):
```bash
cd docs/references
curl -L -f -o hiraguchi-1951-dimension-posets.pdf  "http://scirep.w3.kanazawa-u.ac.jp/articles/01-02-001.pdf"
curl -L -f -o hiraguchi-1955-dimension-orders.pdf   "http://scirep.w3.kanazawa-u.ac.jp/articles/04-01-001.pdf"
curl -L -f -o kimble-1973-extremal-dimension.pdf     "https://dspace.mit.edu/bitstream/handle/1721.1/82903/30083917-MIT.pdf"
curl -L -f -o biro-hamburger-por-trotter-2014-removable-pair-fractional.pdf "https://doi.org/10.37236/3859"
cd -
```

- [ ] **Step 2: Verify each download is a real PDF**

Run:
```bash
for f in docs/references/hiraguchi-1951-dimension-posets.pdf \
         docs/references/hiraguchi-1955-dimension-orders.pdf \
         docs/references/kimble-1973-extremal-dimension.pdf \
         docs/references/biro-hamburger-por-trotter-2014-removable-pair-fractional.pdf; do
  if [ -s "$f" ] && head -c4 "$f" | grep -q '%PDF'; then echo "OK  $f"; else echo "FAIL $f"; fi
done
```
Expected: `OK` for each. For any `FAIL`, delete the bad file and move that source
to the hand-fetch list in Step 3 (do not leave a corrupt/HTML file in the repo).

- [ ] **Step 3: Create the index stub with the hand-fetch section**

Create `docs/references/dimension-index.md`:
```markdown
# Order-Dimension Knowledge Index

A topic-organized, sourced index of poset order-dimension theory. Entry types:
`[DEF]` definition, `[FACT]` folklore fact, `[THM]` theorem, `[LEM]` lemma,
`[ALG]` algorithm/complexity, `[CONJ]` conjecture/open problem. Citation keys
refer to `sources.bib`. `In this repo.` lines link to formalized Coq results.

See also `hiraguchi-sources.md` for the Hiraguchi-bound source dossier.

<!-- sections added in Tasks 3-9 -->

## Hand-fetch (paywalled)

These sources are paywalled or book-only; please obtain them by hand. The index
entries depending on them are marked *pending source* until then.

- **Trotter 1992** [T92] — *Combinatorics and Partially Ordered Sets: Dimension Theory* (book).
- **Schröder 2003** [Schroder03] — *Ordered Sets: An Introduction* (book).
- **Caspard–Leclerc–Monjardet 2012** [CLM12] — *Finite Ordered Sets* (book).
- **Davey–Priestley 2002** [DP02] — *Introduction to Lattices and Order* (book).
- **Dushnik–Miller 1941** [DM41] — JSTOR: https://doi.org/10.2307/2371374
- **Yannakakis 1982** [Yannakakis82] — https://doi.org/10.1137/0603036
- **Baker–Fishburn–Roberts 1972** [BFR72] — https://doi.org/10.1002/net.3230020103
- **Kelly 1981** [Kelly81] — https://doi.org/10.1016/0012-365X(81)90203-X
- **Brightwell–Scheinerman 1992** [BS92] — https://doi.org/10.1007/BF00814405
- **Trotter, Handbook of Combinatorics 1995** [TrotterHandbook95] — survey chapter.

<!-- Move any item here that failed to download in Task 2. -->
```

- [ ] **Step 4: Commit**

```bash
git add docs/references/*.pdf docs/references/dimension-index.md
git commit -m "docs(refs): download open dimension PDFs + index stub with hand-fetch list"
```

---

## Task 3: Foundations section

**Files:**
- Modify: `docs/references/dimension-index.md` (replace the `<!-- sections ... -->` marker)

- [ ] **Step 1: Write the Foundations entries**

Replace `<!-- sections added in Tasks 3-9 -->` with a `## 1. Foundations`
section. Required entries (use the spec's entry schema for each; statements
transcribed from the cited source, paraphrases flagged in `Notes.`):

- `[DEF] linear-extension` — a linear extension of P is a total order containing
  the relation of P. Source: [T92], [DM41].
- `[DEF] realizer` — a realizer of P is a set R of linear extensions with
  P = ∩R. Source: [DM41], [T92].
- `[DEF] dim-def` — dim(P) = min |R| over realizers R of P (Dushnik–Miller).
  Source: [DM41].
- `[FACT] dim-intersection` — dim(P) is the least t such that P is the
  intersection of t linear orders. Source: [DM41], [T92].
- `[DEF] critical-pair` — an incomparable ordered pair (x,y) with the standard
  down/up-set domination conditions. Source: [T92].
- `[DEF] alternating-cycle` — alternating cycle of critical pairs; a family is
  *reversible* iff it contains no alternating cycle. Source: [T92] (Rabinovitch–Rival lineage).
- `[THM] dim-via-critical-pairs` — dim(P) = min number of reversible sets
  covering all critical pairs. Source: [T92].
- `[THM] dim2-comparability` — dim(P) ≤ 2 iff the incomparability graph of P is
  a comparability graph (equivalently P is a permutation poset). Source: [T92], [DM41].

- [ ] **Step 2: Verify every Foundations entry is sourced and well-formed**

Run (counts entry headers vs `Sources.` lines in section 1):
```bash
awk '/^## 1\./{s=1} /^## 2\./{s=0} s' docs/references/dimension-index.md | grep -c '^#### \['
awk '/^## 1\./{s=1} /^## 2\./{s=0} s' docs/references/dimension-index.md | grep -c '\*\*Sources\.\*\*'
```
Expected: both numbers equal (every entry has a `Sources.` line). 8 entries.

- [ ] **Step 3: Verify all cited keys exist in sources.bib**

Run:
```bash
for k in $(awk '/^## 1\./{s=1} /^## 2\./{s=0} s' docs/references/dimension-index.md \
           | grep -oE '\[[A-Za-z][A-Za-z0-9]+[0-9]{2,}\]' | tr -d '[]' | sort -u); do
  grep -q "{$k," docs/references/sources.bib || echo "MISSING KEY: $k"
done
```
Expected: no `MISSING KEY` output. (This check is reused in every later task.)

- [ ] **Step 4: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- Foundations section"
```

---

## Task 4: Standard examples & lower bounds

**Files:**
- Modify: `docs/references/dimension-index.md`

- [ ] **Step 1: Write the section**

Add `## 2. Standard examples & lower bounds`. Required entries:
- `[DEF] standard-example` — S_n: the bipartite poset on {a_1..a_n, b_1..b_n}
  with a_i < b_j iff i ≠ j. Source: [T92], [DM41].
- `[THM] standard-example-dim` — dim(S_n) = n (n ≥ 2). Source: [T92], [DM41].
- `[FACT] dim-monotone-suborder` — dim is monotone under taking subposets
  (induced). Source: [T92].
- `[FACT] dim-contains-standard` — high dimension is "witnessed" by large
  standard examples in many classes; state the general lower-bound idea.
  Source: [T92]. (Flag as a heuristic statement in `Notes.`)

- [ ] **Step 2: Verify sourcing + keys (reuse Task 3 checks, section 2)**

Run the two checks from Task 3 Steps 2–3 with `## 2\.`/`## 3\.` as the range
delimiters. Expected: entry count == Sources count (4 entries); no `MISSING KEY`.

- [ ] **Step 3: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- standard examples & lower bounds"
```

---

## Task 5: Upper bounds & inequalities

**Files:**
- Modify: `docs/references/dimension-index.md`

- [ ] **Step 1: Write the section**

Add `## 3. Upper bounds & inequalities`. Required entries:
- `[THM] dim-le-width` — dim(P) ≤ width(P). Source: [T92], [Trotter149].
  `In this repo.` `dimension_le_width` — posets/dimension/ (see `docs/INDEX.md`).
- `[THM] dim-hiraguchi` — for |P| ≥ 4, dim(P) ≤ ⌊|P|/2⌋. Tight via standard
  examples. Source: [H51], [T92] §3, [K73], [Trotter149].
  `In this repo.` `hiraguchi_bound_direct` (1 honest classical admit) — see
  `docs/INDEX.md` / `project_dimension_merged_to_main`.
  Depends on. [THM dim-le-width], [THM dim-max-2-removed-antichain].
- `[THM] dim-max-2-removed-antichain` — dim(P) ≤ max{2, |P − A|} for a maximal
  antichain A (Trotter 1975, Lemma 5.6 lineage). Source: [Trotter75], [Trotter149], [K73].
- `[THM] dim-removal-point` — removing one point lowers dim by at most 1.
  Source: [T92], [Trotter75].
- `[THM] dim-product` — dim(P × Q) ≤ dim(P) + dim(Q). Source: [T92].

- [ ] **Step 2: Verify sourcing + keys + In-this-repo paths**

Run the two checks from Task 3 (range `## 3\.`/`## 4\.`; expect 5 entries, no
missing keys). Then verify the repo cross-links point at real artifacts:
```bash
grep -n 'dimension_le_width\|hiraguchi_bound_direct' docs/INDEX.md || echo "CHECK: names not in INDEX.md"
```
Expected: matches found, or a note added to the entry's `Notes.` if the name
differs in the current tree.

- [ ] **Step 3: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- upper bounds & inequalities"
```

---

## Task 6: Computational complexity

**Files:**
- Modify: `docs/references/dimension-index.md`

- [ ] **Step 1: Write the section**

Add `## 4. Computational complexity`. Required entries:
- `[ALG] dim2-poly` — testing dim(P) ≤ 2 is in P (via comparability-graph
  recognition / transitive orientation). Source: [T92], [BFR72].
  Depends on. [THM dim2-comparability].
- `[ALG] dim3-npc` — deciding dim(P) ≤ k is NP-complete for every fixed k ≥ 3
  (Yannakakis). Source: [Yannakakis82], [T92].
- `[FACT] dim-not-fpt-trivial` — note on parameterized status / what is and
  isn't known. Source: [T92]. (Flag scope in `Notes.`; keep to what the source states.)

- [ ] **Step 2: Verify (reuse Task 3 checks, range `## 4\.`/`## 5\.`)**

Expected: 3 entries, Sources count equal, no missing keys.

- [ ] **Step 3: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- computational complexity"
```

---

## Task 7: Special classes

**Files:**
- Modify: `docs/references/dimension-index.md`

- [ ] **Step 1: Write the section**

Add `## 5. Special classes`. Required entries:
- `[DEF] interval-order` — poset representable by intervals on the line with
  I < J iff I entirely left of J. Source: [T92].
- `[THM] interval-order-dim` — known dimension behavior of interval orders
  (bounded in terms of size/structure; state what [T92] gives). Source: [T92].
- `[THM] planar-01-dim2` — a planar poset with a 0 and a 1 has dim ≤ 2.
  Source: [BFR72], [T92].
- `[THM] planar-unbounded` — planar posets have unbounded dimension in general
  (Kelly's construction; standard examples embed in the plane). Source: [Kelly81], [T92].
- `[THM] boolean-lattice-dim` — dim(2^[n]) and its asymptotics (Dushnik's
  theorem). Source: [T92], [DM41].
- `[FACT] bipartite-dim` — dimension of bipartite/height-2 posets; standard
  examples are the extremal case. Source: [T92].

- [ ] **Step 2: Verify (reuse Task 3 checks, range `## 5\.`/`## 6\.`)**

Expected: 6 entries, Sources count equal, no missing keys.

- [ ] **Step 3: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- special classes"
```

---

## Task 8: Variants

**Files:**
- Modify: `docs/references/dimension-index.md`

- [ ] **Step 1: Write the section**

Add `## 6. Variants`. Required entries:
- `[DEF] interval-dim` — interval dimension: min # of interval extensions whose
  intersection is P. Source: [T92].
- `[DEF] fractional-dim` — fractional dimension via fractional realizers.
  Source: [BS92].
- `[THM] fractional-le-dim` — fdim(P) ≤ dim(P); basic properties. Source: [BS92].
- `[DEF] boolean-dim` — Boolean dimension. Source: [TrotterHandbook95]. (Mark
  *pending source* if only the survey states it; recheck against a downloaded source.)
- `[DEF] local-dim` — local dimension (recent variant). Source: *pending source*
  (add the arXiv key in Task 10 if a paper is located; otherwise leave as a
  flagged gap).

- [ ] **Step 2: Verify (reuse Task 3 checks, range `## 6\.`/`## 7\.`)**

Expected: 5 entries; Sources count == entries minus any explicitly marked
`*pending source*` (those have no bib key yet — that is acceptable and the only
case where the counts may differ; note it in the commit message).

- [ ] **Step 3: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- variants (interval/fractional/Boolean/local)"
```

---

## Task 9: Open problems

**Files:**
- Modify: `docs/references/dimension-index.md`

- [ ] **Step 1: Write the section**

Add `## 7. Open problems`. Required entries:
- `[CONJ] removable-pair` — Removable Pair Conjecture: every poset with ≥ 3
  points has a pair whose removal lowers dim by ≤ 1 (integer case OPEN).
  Source: [T92]; West open-problems list (URL in `Notes.`).
  `In this repo.` audited reduction on branch `removable-pair-attempt`
  (conjecture left open) — see `project_rpc_reduction_branch`.
- `[THM] removable-pair-fractional` — the Removable Pair Conjecture holds for
  fractional dimension. Source: [BHPT14].
  Depends on. [DEF fractional-dim], [CONJ removable-pair].

- [ ] **Step 2: Verify (reuse Task 3 checks, range `## 7\.`/`^## Hand-fetch`)**

Expected: 2 entries, Sources count equal, no missing keys. Also confirm at least
one `[CONJ]` is present:
```bash
grep -c '#### \[CONJ\]' docs/references/dimension-index.md
```
Expected: ≥ 1.

- [ ] **Step 3: Commit**

```bash
git add docs/references/dimension-index.md
git commit -m "docs(refs): dimension index -- open problems"
```

---

## Task 10: Cross-link pass, whole-file consistency, finalize

**Files:**
- Modify: `docs/references/dimension-index.md`, possibly `docs/references/sources.bib`

- [ ] **Step 1: Resolve `Depends on.` references**

For every `Depends on.` token, confirm the referenced ID exists as a `####`
header. Run:
```bash
ids=$(grep -oE '^#### \[[A-Z]+\] [a-z0-9-]+' docs/references/dimension-index.md | awk '{print $3}' | sort -u)
deps=$(grep -oE 'Depends on\.\*\* .*' docs/references/dimension-index.md | grep -oE '[a-z][a-z0-9-]+-[a-z0-9-]+' | sort -u)
for d in $deps; do echo "$ids" | grep -qx "$d" || echo "DANGLING DEP: $d"; done
```
Expected: no `DANGLING DEP`. Fix any by correcting the ID or adding the entry.

- [ ] **Step 2: Whole-file key check + unique IDs**

Run:
```bash
# every cited key exists
for k in $(grep -oE '\[[A-Za-z][A-Za-z0-9]+[0-9]{2,}\]' docs/references/dimension-index.md | tr -d '[]' | sort -u); do
  grep -q "{$k," docs/references/sources.bib || echo "MISSING KEY: $k"
done
# no duplicate entry IDs
grep -oE '^#### \[[A-Z]+\] [a-z0-9-]+' docs/references/dimension-index.md | awk '{print $3}' | sort | uniq -d
```
Expected: no `MISSING KEY`, no duplicate IDs.

- [ ] **Step 3: Confirm grep-by-type works and coverage is sane**

Run:
```bash
for t in DEF FACT THM LEM ALG CONJ; do printf '%s: ' "$t"; grep -c "#### \[$t\]" docs/references/dimension-index.md; done
```
Expected: nonzero counts for DEF, FACT, THM, ALG, CONJ (LEM may be 0). Total
should be ~35 entries across the 7 sections.

- [ ] **Step 4: Verify In-this-repo links resolve**

Run:
```bash
grep -nE '\*\*In this repo\.\*\*' docs/references/dimension-index.md
```
For each, eyeball that the named lemma/branch matches `docs/INDEX.md`,
`docs/critical-review.md`, or the memory notes; correct any stale name inline.

- [ ] **Step 5: Final commit**

```bash
git add docs/references/dimension-index.md docs/references/sources.bib
git commit -m "docs(refs): cross-link + finalize the order-dimension knowledge index"
```

---

## Self-review notes

- **Spec coverage:** 7 topical sections → Tasks 3–9; entry schema → applied in
  every section task; `sources.bib` → Task 1; downloads + hand-fetch list →
  Task 2; `In this repo.` cross-links → Tasks 5, 9 + verified in Task 10;
  success criteria (sourced, grep-able conjectures, hand-fetch list) → verified
  in Tasks 9–10.
- **Accuracy guard:** any statement that can't be verified against a readable
  source is marked `*pending source*` (Task 8 covers the mechanism) rather than
  guessed — matches the spec's "no invented statements" risk control.
- **Pending gaps that are acceptable:** Boolean/local dimension entries may stay
  `*pending source*` until the user hand-fetches the survey or an arXiv paper is
  located; this is explicit, not silent.

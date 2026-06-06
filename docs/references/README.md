# References

Source material and the knowledge indexes for poset theory.

- **`dimension-index.md`** — knowledge index for **order-dimension theory**
  (facts, definitions, theorems, conjectures, algorithms), organized by topic
  with type-tagged entries. TOC **auto-generated** between the TOC markers.
- **`poset-facts-index.md`** — companion index for **general poset & lattice
  theory** (lattices, fixed points, extremal set theory, well-quasi-orders,
  Möbius functions, Galois connections) — everything *not* about dimension.
  Same conventions and auto-generated TOC.
- **`sources.bib`** — BibTeX provenance for every citation key used in either index.
- **`hiraguchi-sources.md`** — source dossier for Hiraguchi's bound.
- **`*.pdf`** — downloaded open-access sources.

## Keeping the tables of contents in sync

`gen-toc.py` rebuilds the TOC of each `*-index.md` from its section/entry headers
(idempotent). With no arguments it processes every index file:

    python3 docs/references/gen-toc.py            # all *-index.md
    python3 docs/references/gen-toc.py docs/references/poset-facts-index.md  # one file

A pre-commit hook runs this automatically for any `*-index.md` that is part of a
commit. Git hooks are not version-controlled, so install it once per clone:

    ln -sf ../../docs/references/pre-commit.hook .git/hooks/pre-commit

(The hook source is `docs/references/pre-commit.hook`.)

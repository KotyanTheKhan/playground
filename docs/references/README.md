# References

Source material and the knowledge index for poset **order-dimension theory**.

- **`dimension-index.md`** — the master knowledge index (facts, definitions,
  theorems, conjectures, algorithms), organized by topic with type-tagged
  entries. Its table of contents is **auto-generated** between the TOC markers.
- **`sources.bib`** — BibTeX provenance for every citation key used in the index.
- **`hiraguchi-sources.md`** — source dossier for Hiraguchi's bound.
- **`*.pdf`** — downloaded open-access sources.

## Keeping the table of contents in sync

`gen-toc.py` rebuilds the TOC from the section/entry headers (idempotent):

    python3 docs/references/gen-toc.py

A pre-commit hook runs this automatically whenever `dimension-index.md` is part
of a commit. Git hooks are not version-controlled, so install it once per clone:

    ln -sf ../../docs/references/pre-commit.hook .git/hooks/pre-commit

(The hook source is `docs/references/pre-commit.hook`.)

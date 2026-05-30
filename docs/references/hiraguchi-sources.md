# Sources for Hiraguchi's bound `dim(P) ≤ ⌊n/2⌋` (direct proof)

The direct (admit-free) proof reduces to **Lemma 5.4** `dim ≤ width` (already
proven: `dimension_le_width`) + **Lemma 5.6** `dim(P) ≤ max{2, |P−A|}` for a
maximal antichain `A`. Lemma 5.6's proof is in:

## Primary — Lemma 5.6 (`dim ≤ max{2, |P−A|}`)

- **W. T. Trotter.** *Inequalities in dimension theory for posets.*
  Proceedings of the American Mathematical Society **47** (1975), 311–316.
  DOI: **10.2307/2039736** — https://doi.org/10.2307/2039736
  (Cleanest/shortest source; ~6 pages. JSTOR.)

- **R. J. Kimble.** *Extremal Problems in Dimension Theory for Partially Ordered
  Sets.* PhD thesis, MIT, 1973.
  Open PDF (MIT DSpace, handle 1721.1/82903):
  https://dspace.mit.edu/bitstream/handle/1721.1/82903/30083917-MIT.pdf
  (Chapter 1 = "Hiraguchi's Theorem". Freely downloadable but OCR is poor.)

## Modern alternative proof (matchings route)

- **W. T. Trotter, R. Wang.** *Dimension and matchings in comparability and
  incomparability graphs.* Order **33** (2016), 101–119.
  DOI: **10.1007/s11083-015-9355-y** — https://doi.org/10.1007/s11083-015-9355-y
  (Theorem with Claims 1–3; Claim 2 ≈ Lemma 5.6.)

## Survey used for the reduction (open)

- **W. T. Trotter.** *Dimension for Posets and Chromatic Number for Graphs.*
  In "50 Years of Combinatorics, Graph Theory, and Computing".
  https://trotter.math.gatech.edu/papers/149-Dimension_and_chromatic_number.pdf
  (Saved: `docs/references/trotter-149-dimension-chromatic.pdf`. States Lemmas
  5.4–5.6 + the combination; gives 5.6 as an exercise — Thm 5.2 is the bound.)

## Hiraguchi originals (open, Sci. Rep. Kanazawa Univ.)

- T. Hiraguchi. *On the dimension of partially ordered sets.* **1** (1951) 77–94.
  http://scirep.w3.kanazawa-u.ac.jp/articles/01-02-001.pdf
- T. Hiraguchi. *On the dimension of orders.* **4** (1955) 1–20.
  http://scirep.w3.kanazawa-u.ac.jp/articles/04-01-001.pdf

## Context: the OPEN conjecture (do NOT try to prove)

- D. B. West, "Removable Pair Conjecture" (open-problems list):
  https://faculty.math.illinois.edu/~west/openp/rempair.html
- Biró, Hamburger, Pór, Trotter. *The Proof of the Removable Pair Conjecture for
  Fractional Dimension.* Electron. J. Combin. 21(1) (2014) #P1.63.
  (Integer-dimension case remains open.)

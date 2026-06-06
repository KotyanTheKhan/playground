# Tractable-tier formalization — status & decomposition

**Track:** formalize the "tractable tier" of the two reference indexes
(`docs/references/dimension-index.md`, `poset-facts-index.md`) in Coq.
**Started:** 2026-06-06. **Protocol:** long-running-formalization.

## Scope decision

User chose the **tractable tier**: definitions + classical theorems with short
proofs or known formalizations. Excludes the research-grade tier (Schnyder,
duality, Yannakakis, Kruskal, Greene–Kleitman, …) and the 2 open conjectures
(removable-pair, 1/3–2/3).

## Phase A — already formalized (DONE; index links added 2026-06-06)

Survey found the dimension core is **already proved, admit-free, and built**
(`posets/dimension/*.v`, 12/12 `.vo`). `In this repo.` links added for:

| index id | repo |
|---|---|
| linear-extension, realizer, dim-def | `DimDefs.v` (`IsLinearExtension`/`IsRealizer`/`PosetDimension`) |
| dim-intersection | `Theorems.v` (`all_linear_extensions_is_realizer`, `dushnik_miller_exists`) |
| dim-monotone-suborder | `Theorems.v` (`subposet_dimension_le`) |
| critical-pair, alternating-cycle, dim-via-critical-pairs | `CriticalPairs.v` |
| dim-removal-point | `OnePointRemoval.v` (`one_point_removal`) |
| dim-product | `ProductDimension.v` (`product_dimension_le`) |
| szpilrajn | `Szpilrajn.v` (`szpilrajn_theorem`) |

Plus pre-existing links: dim-le-width, dim-max-2-removed-antichain, dim-hiraguchi
(1 admit), Dilworth, the execution dim≤2 family, Hall, lattice classes,
hb-not-semilattice, crdt convergence, standard-example, crown.

## Phase B — genuinely missing (TO PROVE)

Mostly independent small lemmas, not one deep admit — so this is batch
formalization (writing-plans + per-file build/commit), not a single research
admit. `vendor/ZornsLemma` (mapped `-R vendor/ZornsLemma ZornsLemma`) and
MathComp are available; **check them before proving** (searching-existing).

Ordered by (clock-relevance, then easiness):

| # | index id | claim | target file (new) | difficulty | notes |
|---|---|---|---|---|---|
| 1 | dim-self-dual | dim(P)=dim(Pᵈ) | `posets/dimension/DualDimension.v` | easy | reverse each L in a realizer; reuse `IsRealizer` |
| 2 | dim-geometric | dim≤d ⟺ embeds in product of d chains | `posets/dimension/Geometric.v` | easy–moderate | largely a restatement of `IsRealizer` as a coordinate map |
| 3 | dim2-comparability | dim≤2 ⟺ incomparability graph is a comparability graph | `posets/dimension/DimTwo.v` | moderate | one direction = build 2 linear exts from a transitive orientation of the incomparability graph |
| 4 | mirsky | min antichain cover = height | `posets/dilworth/Mirsky.v` | moderate | dual of `Dilworth`; reuse dilworth/ infrastructure |
| 5 | zorn | chain-bounded ⟹ maximal element | `posets/ZornReexport.v` | easy | re-export/wrap `vendor/ZornsLemma`; verify the exact statement matches |
| 6 | knaster-tarski | monotone map on complete lattice has lfp/gfp | `posets/FixedPoints.v` | moderate | classic; define complete lattice over `IsLattice` + sups |
| 7 | dickson | (ℕ^k,≤) is a wqo | `posets/wqo/Dickson.v` | moderate | check MathComp/stdlib first |
| 8 | mobius-inversion | f(x)=Σ μ(y,x) g(y) | `posets/Mobius.v` | moderate | finite locally-finite poset; incidence algebra |

Deferred within tractable (harder / lower priority): kleene-fixpoint (needs
dcpo + directed sups), davis-fpp (needs Knaster–Tarski + converse), sperner/lym
(binomials, symmetric chain decomposition), higman.

## Per-session log

- **2026-06-06 (session 1):** Survey + Phase A + Phase B #1. Added 11
  `In this repo.` links; wrote this status doc. **Proved Phase B #1
  (dim-self-dual)**: `posets/dimension/DualDimension.v`, admit-free, built
  (`dual_dimension_iff`, `dual_dimension_forward`, + 7 helpers). Linked in index.
  Notes learned: (a) the dimension classes take the *bare relation* (no IsPoset
  instance param) — `@PosetDimension A R d`; (b) coercion fields
  `linear_is_total`/`linear_extends`/`realizer_*` take the instance *explicitly*,
  but `total_is_poset`/`total_comparable` accept inferred `(L:=L)`; (c)
  `PosetDimension` is in `Type` (Ensemble realizer) so use a `*`-product, not
  `<->`; (d) the timed-build wrapper's exit code is unreliable — verify the `.vo`.

- **2026-06-06 (session 1, cont.):** **Proved Phase B #2 (dim-geometric)**:
  `posets/dimension/Geometric.v`, admit-free, built. `ChainIntersection R fam`
  (R = coordinatewise intersection of a family of total orders);
  `dimension_to_chain_intersection` (dim d ⇒ d-chain embedding, no finiteness);
  `chain_intersection_dimension_le` (d-chain embedding ⇒ dim ≤ d, finite P, via
  `dushnik_miller_exists` + `dimension_is_minimum`). Linked in index. API note:
  `dushnik_miller_exists` takes `R` as an explicit positional arg (implicits
  `A`, `H`).

## Next session

Phase B #3 (dim2-comparability): dim ≤ 2 ⟺ incomparability graph is a
comparability graph. Harder — needs a transitive orientation of the
incomparability graph ⇒ two linear extensions. Then #4 (Mirsky, reuse
`posets/dilworth/`), #5 (Zorn re-export from `vendor/ZornsLemma`). Build each via
`bash .claude/scripts/timed-build.sh 360 <file>.vo 2` and **verify the `.vo`**
(wrapper exit code is unreliable).

## Risk register

- Some "easy" items may hit framework friction (the repo's dimension layer uses
  `Ensemble`-valued realizers + `IsFinitePoset`; coordinate/embedding phrasings
  must match). Mitigation: reuse existing `DimDefs`/`Theorems` lemmas, don't
  re-found the theory.
- Zorn re-export: confirm `vendor/ZornsLemma`'s statement is the chain-bounded
  form we cite; if it's the Kuratowski/maximal-chain form, derive ours.
- Build/memory: per CLAUDE.md, always the timed wrapper; `-j2`, single files.

## Useful files

- Indexes: `docs/references/{dimension-index,poset-facts-index}.md`
- Existing dimension proofs: `posets/dimension/*.v`
- Dilworth infra: `posets/dilworth/`
- Vendored: `vendor/ZornsLemma`

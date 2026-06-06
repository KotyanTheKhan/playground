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

- **2026-06-06 (session 1, cont.):** **Proved Phase B #6 (Knaster–Tarski)** and
  **linked #5 (Zorn)**. `posets/KnasterTarski.v` (admit-free, built): complete
  lattice = poset + `inf`/`sup` operators; `lfp_is_fixed`/`lfp_least`,
  `gfp_is_fixed`/`gfp_greatest`. Zorn is already in `vendor/ZornsLemma`
  (`ZornsLemma`), linked in the poset-facts index — but in a constructive
  `chain_sup`+`inflation` packaging, NOT the bare chain-upper-bound form, so a
  clean re-export to our `IsPoset` vocab is a separate (deferred) task.

- **2026-06-06 (session 1, cont.):** **Proved foundational extras**:
  `posets/dimension/DimBasics.v` (admit-free, built) — `dimension_unique`
  (dimension is well-defined) and `total_order_is_realizer` +
  `total_order_dim_le_1` (a chain has dim ≤ 1; new index entry `dim-chain`).
  Confirmed the repo has **no** rank/height/longest-chain or well-founded infra,
  so Mirsky (#4) and any height-based result need that built first.

- **2026-06-06 (session 1, close):** Session-closing **full `@all` build is
  green** (`bash .claude/scripts/timed-build.sh 1800 @all 4`; 0 error lines, all
  new `.vo` present). New files this session: `DualDimension.v`, `Geometric.v`,
  `DimBasics.v` (Dimension lib), `KnasterTarski.v` (Posets lib) — all admit-free
  and integrated.

- **2026-06-06 (session 1, cont.):** **Proved Kleene fixed-point**
  (`posets/KleeneFixpoint.v`, admit-free, built): complete lattice as poset +
  inf/sup, ⊥ = inf(Full), Kleene chain `iter n = fⁿ⊥`, ω-continuity hypothesized;
  `kleene_lfp_fixed` (sup of iterates is a fixed point) + `kleene_lfp_least`.
  Linked in poset-facts index. The fixed-point cluster (Knaster–Tarski, Kleene,
  Zorn-linked) is now well covered.

- **2026-06-06 (session 1, cont.):** **Started Mirsky track**
  (`posets/dilworth/Mirsky.v`, admit-free, built). Proved the **lower-bound
  direction** `chain_le_antichain_cover` (any chain ≤ any antichain cover, via a
  choice-selected injection chain→cover + a local `cardinal_Im_inj` +
  `incl_card_le`). Reuses the Dilworth `IsChain`/`IsAntichainCover` layer. Index
  `mirsky` entry marked *Partial*. **Remaining (UB):** a height-sized antichain
  cover from a longest-chain **rank function** — the repo has no rank/height/
  well-founded layer, so that must be built first (the real Mirsky sub-project).

- **2026-06-06 (session 1, cont.):** **Landed the Mirsky-UB keystone**
  `posets/FinPosetWF.v` (admit-free, built): `fin_strict_wf : well_founded
  (StrictR R)` for a finite poset — strong induction on `|DownStrict x|` using
  `incl_st_card_lt` (note: NO `Finite` arg) + `Finite_downward_closed` +
  `finite_cardinal` + `cardinal_finite`. This enables well-founded
  recursion/induction on any finite poset (reusable beyond Mirsky). Used
  `#[local] Existing Instance fp_is_poset` so `poset_trans/antisym` resolve.

- **2026-06-06 (session 1, cont.):** **Mirsky-UB P2 done** — the rank function.
  `posets/FiniteMax.v` gained `the_lub` (deterministic finite max) +
  `the_lub_is_lub` + `the_lub_ext` (extensionality, from LUB uniqueness).
  `posets/FinPosetRank.v` (admit-free, built first try): `rank := Fix
  fin_strict_wf rank_step`; **L1** `rank_eq` (recurrence `rank x = 1 + lub{rank y
  | y<x}`, with `Fix_eq` discharged via `the_lub_ext` — the flagged risk is
  resolved), `rank_pos`, **L2** `rank_strict_mono` (y<x ⇒ rank y < rank x).
  Remaining for Mirsky-UB: L3 (levels = antichains; easy from L2), L4 (height =
  max rank), D1 (the cover), D2 (final).

- **2026-06-06 (session 1, cont.):** **Mirsky-UB L3/L4 + achiever/contiguity.**
  `posets/FiniteMax.v`: `finite_argmax` + `finite_max_achieved` (finite max is
  attained). `posets/FinPosetRank.v`: `rank_level_antichain` (L3), `height`
  +`rank_le_height` (L4), `rank_pred` (rank>1 ⇒ a predecessor of rank-1),
  `rank_achieves` (every k∈[1,rank x] is attained — contiguity). All admit-free.
  Rank-side machinery for Mirsky-UB is now COMPLETE. Remaining: cover assembly in
  the Dilworth layer (`Mirsky.v`): define `Level k`, build the cover = nonempty
  levels, `IsAntichainCover` + `cardinal = height`; plus a chain of size `height`
  (via `rank_pred`) to identify height with longest chain, then the final theorem.

- **2026-06-06 (session 1, cont.):** **Mirsky upper bound assembled** (admit-free).
  `posets/dilworth/Mirsky.v` MirskyUpper: `Level k`, `level_antichain`,
  `mirsky_cover` (nonempty levels), `mirsky_cover_is_cover` (IsAntichainCover);
  `cardinal_nat_interval`, `height_attained`, `levels_nonempty`, `cover_eq_image`,
  `Level_inj`, `mirsky_cover_cardinal` (= height); capstone `mirsky_height_cover`
  + `chain_card_le_height` (no chain exceeds height). Mirsky is now proven with
  `height := max rank` as the height invariant (both bounds). Only the literal
  identification height = longest-chain-length remains (a chain realizing height
  via `rank_pred` — straightforward recursion).

- **2026-06-06 (session 1, cont.):** **MIRSKY FULLY PROVEN (admit-free).**
  `posets/dilworth/Mirsky.v`: `chain_to_x` (chain of size rank x ending at x, via
  rank_pred recursion + IsChain Add case), `exists_chain_height`, and headline
  `mirsky` (height≥1): max chain size = min antichain cover size = height (max
  rank). Closes the Mirsky track (LB + full UB + matching chain). 6 supporting
  files all admit-free: FiniteMax, FinPosetWF, FinPosetRank, dilworth/Mirsky.

- **2026-06-06 (session 1, close):** full `@all` build green (0 errors) after Mirsky completion; all 9 new files' `.vo` present.

## Next session

Mirsky UB (now unblocked by `fin_strict_wf`): define `rank x` by well-founded
recursion (`Fix fin_strict_wf`) as `1 + max {rank y | y < x}` (0 if minimal),
prove x<y ⇒ rank x < rank y
(levels are antichains) and #levels = height, giving the height-sized cover.
Alternatively Phase B #3 (dim2-comparability): dim ≤ 2 ⟺ incomparability graph
is a comparability graph (needs a transitive orientation of the
incomparability graph ⇒ two linear extensions. Then #4 (Mirsky — repo
`posets/dilworth/` has chain-cover machinery but no longest-chain rank function
yet, so Mirsky needs that built; moderate), #7 (Dickson), #8 (Möbius). Build
each via `bash .claude/scripts/timed-build.sh 360 <file>.vo 2` and **verify the
`.vo`** (wrapper exit code is unreliable).

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

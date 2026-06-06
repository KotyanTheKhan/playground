# Order-Dimension Knowledge Index

A topic-organized, sourced index of poset order-dimension theory. Entry types:
`[DEF]` definition, `[FACT]` folklore fact, `[THM]` theorem, `[LEM]` lemma,
`[ALG]` algorithm/complexity, `[CONJ]` conjecture/open problem. Citation keys
refer to `sources.bib`. `In this repo.` lines link to formalized Coq results.

See also `hiraguchi-sources.md` for the Hiraguchi-bound source dossier.

## 1. Foundations

#### [DEF] linear-extension — Linear extension
**Statement.** A linear extension of a poset P is a total (linear) order on the same ground set that contains every relation of P (x ≤_P y implies x ≤_L y).
**Status.** Definition.
**Sources.** [DM41]; [T92].

#### [DEF] realizer — Realizer
**Statement.** A realizer of P is a family R of linear extensions of P whose intersection is exactly P, i.e. x ≤_P y iff x ≤_L y in every L ∈ R.
**Status.** Definition.
**Depends on.** [linear-extension]
**Sources.** [DM41]; [T92].

#### [DEF] dim-def — Order dimension (Dushnik–Miller)
**Statement.** The dimension dim(P) is the least cardinality of a realizer of P.
**Status.** Definition (Dushnik–Miller 1941).
**Depends on.** [realizer]
**Sources.** [DM41].

#### [FACT] dim-intersection — Dimension as intersection of linear orders
**Statement.** dim(P) equals the least t such that P is the intersection of t linear orders on its ground set. (Equivalent reformulation of the definition.)
**Status.** Proven (folklore/Dushnik–Miller).
**Depends on.** [dim-def]
**Sources.** [DM41]; [T92].

#### [DEF] critical-pair — Critical pair
**Statement.** An ordered pair (x,y) of distinct incomparable elements of P is a critical pair if every element below x is below y, and every element above y is above x (equivalently D(x) ⊆ D(y) and U(y) ⊆ U(x)). Reversing all critical pairs suffices to determine dimension.
**Status.** Definition.
**Sources.** [T92].
**Notes.** D(·)/U(·) denote strict down-set/up-set.

#### [DEF] alternating-cycle — Alternating cycle / reversible set
**Statement.** A set S of critical pairs contains an alternating cycle if there are pairs (x_1,y_1),…,(x_k,y_k) in S with y_i ≤ x_{i+1} (indices mod k). S is reversible iff it contains no alternating cycle; a reversible set can be reversed by a single linear extension.
**Status.** Definition (Rabinovitch–Rival lineage).
**Depends on.** [critical-pair]
**Sources.** [T92].

#### [THM] dim-via-critical-pairs — Dimension via critical pairs
**Statement.** dim(P) equals the least number of reversible sets needed to cover all critical pairs of P.
**Status.** Proven.
**Depends on.** [alternating-cycle], [dim-def]
**Sources.** [T92].

#### [THM] dim2-comparability — Two-dimensional posets
**Statement.** dim(P) ≤ 2 iff the incomparability graph of P is a comparability graph; equivalently, P is the intersection of two linear orders (a permutation poset).
**Status.** Proven (Dushnik–Miller).
**Depends on.** [dim-def]
**Sources.** [DM41]; [T92].

## 2. Standard examples & lower bounds

#### [DEF] standard-example — Standard example S_n
**Statement.** The standard example S_n is the height-2 poset on 2n elements {a_1,…,a_n, b_1,…,b_n} with a_i < b_j iff i ≠ j (and no other relations); the a_i form an antichain of minimal elements, the b_j an antichain of maximal elements.
**Status.** Definition.
**Sources.** [DM41]; [T92].

#### [THM] standard-example-dim — Dimension of the standard example
**Statement.** dim(S_n) = n for all n ≥ 2. The pairs (a_i, b_i) are critical and no two can be reversed by the same linear extension, forcing n linear extensions.
**Status.** Proven (Dushnik–Miller).
**Depends on.** [standard-example], [dim-def]
**Sources.** [DM41]; [T92].

#### [FACT] dim-monotone-suborder — Monotonicity under subposets
**Statement.** If Q is an induced subposet of P then dim(Q) ≤ dim(P). Dimension is monotone under taking induced subposets.
**Status.** Proven.
**Depends on.** [dim-def]
**Sources.** [T92].

#### [FACT] dim-lower-bound-standard — Standard examples as lower-bound witnesses
**Statement.** A large induced standard example forces large dimension: if S_n embeds as an induced subposet of P then dim(P) ≥ n. This is the standard route to dimension lower bounds.
**Status.** Proven (consequence of monotonicity + standard-example-dim).
**Depends on.** [dim-monotone-suborder], [standard-example-dim]
**Sources.** [T92].
**Notes.** A heuristic principle — not every high-dimension poset contains a large standard example, but containment is a sufficient lower-bound certificate.

## 3. Upper bounds & inequalities

#### [THM] dim-le-width — Dimension at most width
**Statement.** dim(P) ≤ width(P), where width(P) is the maximum size of an antichain. Every poset of width w is the intersection of w linear extensions.
**Status.** Proven.
**Depends on.** [dim-def]
**Sources.** [T92]; [Trotter149].
**In this repo.** `dimension_le_width` — `posets/dimension/WidthBound.v`.

#### [THM] dim-max-2-removed-antichain — Trotter's antichain-complement bound
**Statement.** For a maximal antichain A of P, dim(P) ≤ max{2, |P − A|}. (Trotter 1975, the key lemma behind Hiraguchi's bound.)
**Status.** Proven (Trotter 1975).
**Depends on.** [dim-le-width]
**Sources.** [Trotter75]; [Trotter149]; [K73].
**In this repo.** `antichain_complement_dim_bound` (Trotter 1975 Thm 2) — `posets/dimension/AntichainDimBound.v`.

#### [THM] dim-hiraguchi — Hiraguchi's Theorem
**Statement.** For a poset P with |P| ≥ 4, dim(P) ≤ ⌊|P|/2⌋. The bound is tight: dim(S_n) = n = |S_n|/2.
**Status.** Proven (Hiraguchi 1951).
**Depends on.** [dim-le-width], [dim-max-2-removed-antichain], [standard-example-dim]
**Sources.** [H51]; [T92]; [K73]; [Trotter149].
**In this repo.** `hiraguchi_bound_direct` — `posets/dimension/HiraguchiDirect.v` (sound; Print Assumptions = standard classical axioms + one base-case admit `small_complement_le_2`, Trotter Lemma 3; NOT dependent on the Removable Pair Conjecture).

#### [THM] dim-removal-point — Point-removal inequality
**Statement.** Removing a single point from P decreases the dimension by at most 1: dim(P) − 1 ≤ dim(P − {x}) ≤ dim(P).
**Status.** Proven (Hiraguchi; Trotter 1975).
**Depends on.** [dim-def]
**Sources.** [T92]; [Trotter75].

#### [THM] dim-product — Dimension of a product
**Statement.** dim(P × Q) ≤ dim(P) + dim(Q) for the Cartesian product order.
**Status.** Proven.
**Depends on.** [dim-def]
**Sources.** [T92].

## 4. Computational complexity

#### [ALG] dim2-poly — Recognizing dimension ≤ 2 is polynomial
**Statement.** Testing whether dim(P) ≤ 2 can be done in polynomial time, by checking whether the incomparability graph admits a transitive orientation (comparability-graph recognition).
**Status.** Proven (polynomial).
**Depends on.** [dim2-comparability]
**Sources.** [T92]; [BFR72].

#### [ALG] dim3-npc — Deciding dimension ≤ k is NP-complete for k ≥ 3
**Statement.** For every fixed k ≥ 3, deciding whether dim(P) ≤ k is NP-complete (Yannakakis 1982). In particular recognizing dimension-3 posets is NP-complete.
**Status.** Proven (Yannakakis 1982).
**Depends on.** [dim-def]
**Sources.** [Yannakakis82]; [T92].

#### [FACT] dim-complexity-gap — Dichotomy at k = 3
**Statement.** There is a sharp complexity jump: dim ≤ 2 is polynomial-time recognizable, while dim ≤ k for any fixed k ≥ 3 is NP-complete. No intermediate fixed k is known to be tractable.
**Status.** Proven.
**Depends on.** [dim2-poly], [dim3-npc]
**Sources.** [Yannakakis82]; [T92].
**Notes.** States only the known dichotomy; parameterized/approximation refinements are not asserted here.

## 5. Special classes

#### [DEF] interval-order — Interval order
**Statement.** An interval order is a poset representable by assigning each element a closed real interval so that x < y iff the interval of x lies entirely to the left of the interval of y. Equivalently, it is a poset with no induced 2+2 (two disjoint 2-chains).
**Status.** Definition.
**Sources.** [T92].

#### [THM] interval-order-dim — Dimension of interval orders
**Statement.** The dimension of an interval order is governed by its height: interval orders can have arbitrarily large dimension, growing (slowly) with the number of elements, and the extremal growth rate is known to be ~ lg lg n. Interval orders are a central testbed for dimension theory.
**Status.** Proven.
**Depends on.** [interval-order]
**Sources.** [T92].
**Notes.** The lg lg n growth (Füredi–Hajnal–Rödl–Trotter line of work) is reported as surveyed in [T92]; treat the precise asymptotic as *pending source* if exactness is needed.

#### [THM] planar-01-dim2 — Planar posets with 0 and 1
**Statement.** A poset whose Hasse diagram is planar and which has a least element 0 and a greatest element 1 has dim ≤ 2.
**Status.** Proven (Baker–Fishburn–Roberts 1972).
**Depends on.** [dim2-comparability]
**Sources.** [BFR72]; [T92].

#### [THM] planar-unbounded — Planar posets have unbounded dimension
**Statement.** Without the 0/1 hypothesis, planar posets can have arbitrarily large dimension; Kelly constructed planar posets containing large standard examples, so planarity alone does not bound dimension.
**Status.** Proven (Kelly 1981).
**Depends on.** [standard-example], [planar-01-dim2]
**Sources.** [Kelly81]; [T92].
**Notes.** Contrast with [planar-01-dim2] — the 0/1 (bounded) hypothesis is essential.

#### [THM] boolean-lattice-dim — Dimension of the Boolean lattice
**Statement.** The dimension of the Boolean lattice 2^[n] (subsets of an n-set ordered by inclusion) equals n for n ≥ 2 (its standard example S_n sits at the middle two levels and forces dim ≥ n; n linear extensions suffice).
**Status.** Proven (Dushnik–Miller).
**Depends on.** [standard-example-dim]
**Sources.** [DM41]; [T92].
**Notes.** Often attributed to Dushnik–Miller; the lower bound is exactly the embedded standard example.

#### [FACT] bipartite-dim — Height-2 (bipartite) posets
**Statement.** Height-2 posets (a bipartite split into minimal and maximal elements) already realize the full difficulty of dimension theory — standard examples are height-2, and dimension of height-2 posets is itself NP-hard to compute. Restricting to height 2 does not make dimension easy.
**Status.** Proven.
**Depends on.** [standard-example], [dim3-npc]
**Sources.** [T92]; [Yannakakis82].

## 6. Variants

#### [DEF] interval-dim — Interval dimension
**Statement.** The interval dimension idim(P) is the least number of interval-order extensions of P whose intersection is P. Always idim(P) ≤ dim(P).
**Status.** Definition.
**Depends on.** [interval-order], [dim-def]
**Sources.** [T92].

#### [DEF] fractional-dim — Fractional dimension
**Statement.** The fractional dimension fdim(P) is the linear-programming relaxation of dimension: the minimum total weight on linear extensions such that each critical pair is reversed by extensions of total weight ≥ 1 (equivalently a fractional realizer).
**Status.** Definition (Brightwell–Scheinerman 1992).
**Depends on.** [realizer], [critical-pair]
**Sources.** [BS92].

#### [THM] fractional-le-dim — Fractional vs integer dimension
**Statement.** fdim(P) ≤ dim(P) for every poset, and fractional dimension is bounded below by 2 for any poset that is not a chain; it can be strictly smaller than the integer dimension.
**Status.** Proven (Brightwell–Scheinerman 1992).
**Depends on.** [fractional-dim], [dim-def]
**Sources.** [BS92].

#### [DEF] boolean-dim — Boolean dimension
**Statement.** The Boolean dimension bdim(P) is the least d such that the order relation of P can be recovered by a fixed Boolean formula from d linear orders on the ground set (the comparison x < y is decided by a Boolean function of the d pairwise comparisons). Always bdim(P) ≤ dim(P).
**Status.** Definition.
**Depends on.** [dim-def]
**Sources.** *pending source*
**Notes.** Introduced by Nešetřil–Pudlák; a precise citable source has not yet been secured for this index — recheck on hand-fetch.

#### [DEF] local-dim — Local dimension
**Statement.** The local dimension ldim(P) is defined via partial linear extensions: the minimum, over coverings of the critical pairs by partial realizers, of the maximum number of partial linear extensions covering any single element. It refines dimension with ldim(P) ≤ dim(P).
**Status.** Definition.
**Depends on.** [dim-def], [critical-pair]
**Sources.** *pending source*
**Notes.** Introduced by Ueckerdt (2016) and developed by Kim–Martin–Masařík–Shull–Smith–Uzzell–Wang; a precise citable source has not yet been secured — recheck on hand-fetch.

## 7. Open problems

#### [CONJ] removable-pair — Removable Pair Conjecture
**Statement.** (Trotter) Every poset P with |P| ≥ 3 contains a pair of elements {x,y} whose removal decreases the dimension by at most 1: dim(P) − dim(P − {x,y}) ≤ 1. The integer-dimension case is OPEN.
**Status.** Open.
**Depends on.** [dim-removal-point]
**Sources.** [T92].
**In this repo.** A sound, audited *reduction* of the conjecture exists on branch `removable-pair-attempt` (18 Qed / 0 admits); the conjecture itself is left open. The "two maximals" approach was shown FALSE. See memory note `project_rpc_reduction_branch`.
**Notes.** West's open-problems list tracks it: https://faculty.math.illinois.edu/~west/openp/rempair.html

#### [THM] removable-pair-fractional — Removable Pair holds for fractional dimension
**Statement.** The Removable Pair Conjecture is TRUE when dimension is replaced by fractional dimension: every poset with ≥ 3 points has a pair whose removal lowers the fractional dimension by at most 1 (Biró–Hamburger–Pór–Trotter 2014). The integer case remains open.
**Status.** Proven (BHPT 2014, fractional version only).
**Depends on.** [fractional-dim], [removable-pair]
**Sources.** [BHPT14].

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
- **Kimble 1973** [K73] — MIT DSpace (429 rate-limit at fetch time): https://dspace.mit.edu/bitstream/handle/1721.1/82903/30083917-MIT.pdf

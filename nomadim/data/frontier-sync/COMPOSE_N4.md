# Composing minimum dimension-2 N=4 executions

**Question.** Take the building blocks `mPsi4 dim2` = the 10 minimum (S=5)
dimension-2 fully frontier-synchronized executions of N=4 processes. Compose two
of them, A then B, by gluing A's output frontier (4 end events) to B's input
frontier (4 start events). The result is a 10-sync execution that is
automatically fully synchronized. **For every A, which B keep the composition at
dimension 2?** The frontier is an unordered set of 4 channels, so we try all
`4! = 24` ways to wire A's outputs to B's inputs; A->B is "dim-2 composable" if
ANY matching keeps it dimension 2. (For N=4 the dimension is always 2 or 3, so
dim 3 is the "crown" case that breaks dim-2 closure.) Dimensions decided by the
z3 SMT oracle.

## Result

**The 10 blocks are fully closed under dim-2 composition: every ordered pair
(A, B) admits a dimension-2 composition for some frontier matching (100 of 100).
So for every A, all 10 B work.** But the matching is decisive:

| quantity | value |
|----------|-------|
| compositions total (100 ordered pairs x 24 matchings) | 2400 |
| dimension 2 | 672 (28%) |
| dimension 3 (crown) | 1728 (72%) |
| ordered pairs dim-2 via SOME matching | **100 / 100** |
| ordered pairs dim-2 via ALL 24 matchings | 0 / 100 |
| ordered pairs that are ALWAYS a crown | 0 / 100 |

So **no pair is unconditionally safe and no pair is hopeless**: every pair has
some matchings that stay dimension 2 and some that form a crown and jump to
dimension 3. On average only ~7 of the 24 frontier alignments per pair preserve
dimension 2.

### The matching is what matters (same blocks, both outcomes)

The cleanest witness is a block composed with itself, `B1 ; B1`
(`B1` = the star gossip `(0,1)(0,2)(0,3)(0,2)(0,1)`):

- identity matching `pi=(0,1,2,3)` -> dimension **2**
  (`N4_compose_dim2_example.yaml`): two star gossips stacked stay 2-dimensional.
- swap channels 2,3 `pi=(0,1,3,2)` -> dimension **3**
  (`N4_compose_dim3_crown_example.yaml`): the crossed gluing creates a crown that
  raises the dimension.

## Reading

- "Connecting two dim-2 blocks gives a dim-2 execution" is **true but only for
  the right frontier alignment** -- about 28% of alignments. Most alignments
  (72%) cross the frontier into a crown and cost a third clock coordinate.
- This is the empirical face of the Coq `frontier-compose` work on `dev`
  (`threshold_dim_le2`: a non-crossing frontier preserves dim<=2;
  `crown3_dim_ge_3`: an S3-crown frontier forces dim>=3). Here every pair of
  blocks can be aligned to avoid the crown, but a generic alignment will hit one.

## The distinct dim-2 compositions (non-isomorphic)

The 672 dimension-2 compositions collapse, up to isomorphism of the composed
happened-before poset, to just **5 classes** (distinct Weisfeiler-Leman
signatures of the reachability closure; all confirmed dimension 2 by both z3 and
nomadim's independent brute-force). Every one is built from the two extreme
blocks **B1 = star** `(0,1)(0,2)(0,3)(0,2)(0,1)` and **B9 = two-pairs**
`(0,1)(2,3)(0,2)(0,1)(2,3)`:

| # | composition | # min realizers | critical pairs | copies | file |
|---|-------------|-----------------|----------------|--------|------|
| 1 | B1 ; B1 (star -> channel-rotated star) | 4 | 46 | 256 | `N4_compose_dim2_distinct_01.yaml` |
| 2 | B1 ; B1 (star -> star, identity) | 8 | 44 | 128 | `N4_compose_dim2_distinct_02.yaml` |
| 3 | B1 ; B9 (star -> two-pairs) | 16 | 45 | 128 | `N4_compose_dim2_distinct_03.yaml` |
| 4 | B9 ; B1 (two-pairs -> star) | 16 | 45 | 128 | `N4_compose_dim2_distinct_04.yaml` |
| 5 | B9 ; B9 (two-pairs -> two-pairs) | 64 | 44 |  32 | `N4_compose_dim2_distinct_05.yaml` |

All are 34-vertex, dimension 2, fully synchronized. `#3` and `#4` are
**order-duals** (the composition reversed): same realizer/critical-pair counts,
yet non-isomorphic -- WL distinguishes them. So **every** dim-2 composition of any
of the 10 blocks is isomorphic to one of these 5; the dim-2-preserving
compositions are governed entirely by the star and two-pairs archetypes.

Reproduce: `compose_n4.py` (the full relation + counts) and
`compose_n4_distinct.py` (the non-isomorphic representatives).

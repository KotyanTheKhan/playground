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

## Connector composition: one extra sync rescues every crown

Instead of gluing A's output frontier directly to B's input frontier, insert a
short **connector** of `c` syncs in between: `A.syncs + connector + pi(B.syncs)`.
The connector re-mixes the frontier before B runs, and it dramatically widens
dim-2 preservation:

| connector budget | dim-2 variants (of 2400) |
|------------------|--------------------------|
| <=0 (direct)     | 672 = **28%** |
| **<=1 (one sync)** | **2400 = 100%** |

The 1728 crown (dim-3) variants form **5 non-isomorphic crown classes**, and
**every one is rescued to dimension 2 by a single connector sync** (e.g. `(1,2)`,
`(2,3)`, `(0,3)`). So a 1-sync bridge takes dim-2 preservation from 28% to 100%.

Concretely (`N4_connector1_rescue_dim2.yaml`, dim 2 by both z3 and nomadim):
`(0,1)(0,2)(0,3)(0,2)(0,1)` **`(1,2)`** `(0,2)(0,1)(0,3)(0,1)(0,2)` is dimension 2,
whereas the same composition without the middle `(1,2)` is the dimension-3 crown.
Intuition: the crown is an S3-type frontier crossing; one synchronization across
the crossing breaks it, dropping the order back to 2-dimensional (one clock
coordinate saved). This is the constructive counterpart of the
`threshold_dim_le2` / `crown3_dim_ge_3` dichotomy.

### Which connector rescues a crown: the crossed pair, not any pair

A generic connector does NOT work -- typically only **1 of the 6** possible
single syncs rescues a given crown (one class allows 2). And the rescuing sync is
not arbitrary: it is exactly the **pair of processes that the frontier matching
crosses**.

| crown class | matching pi | pi transposes | rescuing connector(s) (of 6) |
|-------------|-------------|---------------|------------------------------|
| #1  B1;B1 | (0,1,3,2) | 2<->3 | `(2,3)` |
| #2  B1;B1 | (0,2,1,3) | 1<->2 | `(1,2)` |
| #3  B1;B9 | (0,2,1,3) | 1<->2 | `(1,2)` |
| #4  B9;B1 | (0,2,1,3) | 1<->2 | `(1,2)` |
| #5  B9;B9 | (0,2,1,3) | 1<->2 | `(1,2)` and `(0,3)` |

Every crown here is created by a matching that **transposes two channels**, and
the unique rescuing connector is a sync on **precisely those two crossed
processes**. Structurally: the crown is the S3-type crossing introduced by
swapping two channels; placing one synchronization across exactly that crossing
collapses it and the order returns to 2-dimensional. The lone exception, #5
(two-pairs ; two-pairs), also accepts `(0,3)`, because the B9 block carries two
independent `{0,1}`/`{2,3}` groupings and thus a second equivalent crossing that
`(0,3)` resolves.

Takeaway: the connector must be **targeted at the crossed pair**. A random
connector sync rescues a given crown only ~1/6 (sometimes 2/6) of the time, even
though *some* single-sync connector always exists.

### Connector length 1-4: rescuer counts and the crossed pair

Number of connectors of each length that rescue the crown to dim 2 (and the
shortest length whose rescuers can AVOID the crossed pair -- the channels the
matching transposes):

| crown | crossed pair | L1 / 6 | L2 / 36 | L3 / 216 | L4 / 1296 | first length avoiding crossed pair |
|-------|--------------|--------|---------|----------|-----------|------------------------------------|
| #1 B1;B1 | (2,3) | 1 | 7 | 33 | 153 | L4 (only 4) |
| #2 B1;B1 | (1,2) | 1 | 5 | 25 | 121 | L3 (only 1) |
| #3 B1;B9 | (1,2) | 1 | 6 | 33 | 172 | L2 (1) |
| #4 B9;B1 | (1,2) | 1 | 6 | 33 | 172 | L2 (1) |
| #5 B9;B9 | (1,2) | 2 | 10 | 54 | 278 | L1 (1) |

Two facts:

1. **The rescue COUNT grows with length, but the FRACTION stays flat (~10-22%)** --
   it never runs away toward "any connector works". Star crowns drift slightly
   down (16.7% -> 11.8%); the two-pairs crown #5 stays highest (33% -> 21%). A
   longer connector gives proportionally more rescuers, not an easier problem.

2. **The crossed pair is mandatory for short connectors; only longer ones route
   around it, always as a minority.** Pure-star crowns (#1, #2) cannot avoid the
   crossed pair through length 2 (first dodge at length 3-4, a handful: 1 or 4 of
   thousands). Two-pairs crowns (#3-5) dodge it earlier and more often, via the
   **alternative `(0,3)` crossing** (avoidance climbs 1 -> 8 -> 47 for #3/#4;
   1 -> 5 -> 27 -> 131 for #5).

So even with up to 4 syncs you must still synchronize across one of the crown's
crossings; longer connectors merely let you reach the *alternative* crossing or
take a roundabout route, and crossed-pair-free rescues remain a small minority.
The crown's crossing structure is the gatekeeper at every length.

Reproduce: `compose_n4.py` (the full relation + counts),
`compose_n4_distinct.py` (the non-isomorphic dim-2 representatives),
`compose_n4_connector.py` (the connector rescue),
`check_connector_pairs.py` (which single connector pair rescues each crown),
`check_connectors2.py` (length-1 vs length-2 connectors), and
`check_connectors_len.py` (rescuer counts for connector lengths 1-4).

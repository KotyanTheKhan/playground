# One sync to untangle them: rescuing a "crown" back to a 2-coordinate clock

*Who this is for: engineers and scientists comfortable with distributed systems
and a little discrete math, but not with order-dimension theory or this project's
notation. If you've read the companion piece `EXPLAINER.md` you're more than
ready; if not, the next section recaps everything you need.*

---

## The hook

You have two distributed-system executions that are each *cheap* — each can be
timestamped with a clock of just **two** numbers per event instead of one per
process. You glue them together end to end, expecting the result to stay cheap.
Most of the time it doesn't: gluing two cheap things accidentally creates a
**crown**, an obstruction that drags the cost up to a *third* coordinate.

The fix is almost comically small. **A single extra synchronization — one
conversation, placed in exactly the right spot — buys back the cheap clock**,
every single time. Not any sync: the *right* sync, on the precise pair of
processes that the gluing crossed. Place it anywhere else and it usually does
nothing.

This is a concrete, minimal *dimension-repair* operation, and it's the story
below.

---

## The setup (recap in one screen)

A tiny model of a distributed system. You have **N processes** — think of them
as N people, each on their own timeline. Occasionally two of them
**synchronize**: they meet, swap everything they know, and carry on. An
*execution* is N people plus an ordered list of these pairwise meetings.

Each meeting weaves two timelines together, so an execution expands into a web of
events where some provably **happened before** others and some are
**concurrent**. That happened-before relation is a **partial order** (a *poset*).

How tangled is that poset? The measure is its **order dimension**: the fewest
plain timelines whose *agreement* reconstructs the true order — X is before Y in
*every* timeline exactly when X really happened before Y. Dimension 2 means a
flat, grid-like order that two timelines pin down; dimension 3 means you
genuinely need a third independent viewpoint.

Why care? **The order dimension is the number of coordinates a minimal logical
clock needs.** A vector clock spends `N` numbers per event (one per process); a
poset of dimension `d` can be faithfully timestamped with just `d`. So
"dimension 2 vs 3" is literally "two-number clock vs three-number clock." That
gap — sub-vector-clock memory — is this project's north star.

One more piece of vocabulary. We only look at executions that are **fully
frontier-synchronized**: by the end, *everyone's* opening news has reached
*everyone*. The opening events form the **input frontier**, the closing events
the **output frontier** — each a set of N channels, one per process.

---

## The building blocks

Fix **N = 4**. The cheapest fully-synchronized executions that are still
dimension 2 use exactly **5 syncs**, and there are exactly **10** of them. These
are the **blocks** we'll compose. Two archetypes do all the work:

- **The star** `(0,1)(0,2)(0,3)(0,2)(0,1)` — everyone reports in to hub 0, then
  hub 0 scatters the merged news back out. (Called `B1`.)
- **The two-pairs** `(0,1)(2,3)(0,2)(0,1)(2,3)` — two independent pairs that mix
  through a middle sync. (Called `B9`.)

Both are dimension 2 — a two-coordinate clock each. They're the cheap parts we
want to keep cheap.

---

## Composing two blocks: the crown appears

Now glue block A to block B. A finishes with an output frontier of 4 channels; B
starts with an input frontier of 4 channels. To compose them you wire A's outputs
to B's inputs — but a frontier is an *unordered* set, so there are `4! = 24` ways
to do the wiring. Each wiring is a **matching**.

Two facts fall out of trying all of them (100 ordered pairs of blocks × 24
matchings = **2400** composed executions, with each dimension decided by the
**z3 SMT oracle**):

- The composition stays fully synchronized automatically. Good.
- But **only 28% (672 of 2400) stay dimension 2.** The other **72% (1728) jump to
  dimension 3.**

That dimension-3 case has a name: a **crown**. It's a specific frontier
*crossing* — wire two channels so they cross, and you've embedded an S₃-type
obstruction that forces dimension ≥ 3. (This is the empirical face of the Coq
theorems on `dev`: `threshold_dim_le2` says a non-crossing frontier keeps
dimension ≤ 2, and `crown3_dim_ge_3` says an S₃-crown frontier forces
dimension ≥ 3.)

Here's the cleanest crown — the star block glued to *itself*, but with channels 2
and 3 swapped:

![Gluing block A's output frontier to block B's input frontier with a matching that swaps two channels makes the wires cross — a crown — and the dimension jumps from 2 to 3.](figs/rescue_crossing.svg)

The same blocks with a *non*-crossing (identity) matching stay dimension 2. So
**the matching is the whole story**: the blocks are innocent, the wiring is
guilty. Up to isomorphism, all those crowns collapse to just **5 classes** — two
pure-star, two star/two-pairs duals, and one pure two-pairs.

![Direct gluing keeps dimension 2 only 28% of the time; one well-placed connector sync rescues every crown, taking it to 100%.](figs/rescue_headline.svg)

---

## The rescue: one sync, on exactly the crossed pair

Here is the heart of the piece. Instead of gluing A's output frontier *directly*
to B's input frontier, slip a short **connector** of a few syncs in between:
`A.syncs + connector + matched(B.syncs)`. The connector re-mixes the frontier
before B runs.

The headline result:

| connector | dim-2 variants (of 2400) |
|-----------|--------------------------|
| none (direct glue) | 672 = **28%** |
| **one sync** | **2400 = 100%** |

**A single connector sync rescues every crown back to dimension 2.** All five
crown classes, gone. 28% → 100%.

But — and this is the non-obvious part — it has to be the *right* sync. A generic
single connector typically rescues a given crown only **1 in 6** of the time (one
class allows 2 of 6). The rescuing sync is not arbitrary: **it is a sync on
exactly the pair of processes that the matching crossed** — the *crossed pair*.

| crown class | matching swaps | rescuing connector(s), of 6 |
|-------------|----------------|------------------------------|
| #1  star;star | 2 ↔ 3 | `(2,3)` |
| #2  star;star | 1 ↔ 2 | `(1,2)` |
| #3  star;two-pairs | 1 ↔ 2 | `(1,2)` |
| #4  two-pairs;star | 1 ↔ 2 | `(1,2)` |
| #5  two-pairs;two-pairs | 1 ↔ 2 | `(1,2)` **and** `(0,3)` |

Every crown here is born from a matching that *transposes two channels*, and the
unique rescuing connector is a sync on *precisely those two crossed processes*.
Put one synchronization across the crossing and the crossing collapses — the
order falls back to two dimensions. One clock coordinate, bought back.

![Placing one connector sync on exactly the crossed pair (2,3) routes the crossed channels through it; the crown collapses and the dimension drops from 3 back to 2.](figs/rescue_connector.svg)

The concrete witness, verified dimension 2 by both z3 *and* nomadim's independent
brute force (`N4_connector1_rescue_dim2.yaml`):

```
(0,1)(0,2)(0,3)(0,2)(0,1)   (1,2)   (0,2)(0,1)(0,3)(0,1)(0,2)
                            ^^^^^
                         the connector
```

That whole thing is dimension 2. **Remove the middle `(1,2)` and it's the
dimension-3 crown.** One sync is the entire difference between a two-number clock
and a three-number clock.

---

## Why a longer connector doesn't make it free

You might hope a *bigger* connector — more syncs to play with — eventually makes
the problem trivial, so that "almost any connector works." It doesn't. Counting
how many connectors of each length (L1 = 1 sync, up to L4 = 4 syncs) rescue each
crown:

![Rescuer counts per connector length for the five crown classes. The count grows with length, but the fraction that works stays flat at roughly 10–22%. Red rows are pure-star crowns, whose crossed pair is unavoidable until length 3–4; the green row is the two-pairs crown #5, which has a second crossing (0,3) that lets short connectors dodge the (1,2) pair earlier — but always as a minority.](figs/rescue_lengths.svg)

Two things to read off it:

1. **The rescuer count grows with length, but the *fraction* stays flat
   (~10–22%).** It never runs away toward "anything works." Star crowns even
   drift slightly *down* (16.7% at L1 to 11.8% at L4); the two-pairs crown #5
   stays highest (33% down to 21%). A longer connector gives you proportionally
   more rescuers — not an easier puzzle.

2. **You still have to synchronize across one of the crown's crossings.** For the
   pure-star crowns (#1, #2) the crossed pair is *mandatory* through length 2 —
   the first connector that rescues *without* touching the crossed pair appears
   only at length 3 or 4, and there are just a handful (1 or 4 out of thousands).
   The two-pairs crowns (#3–#5) escape earlier because the `B9` block carries two
   independent groupings — `{0,1}` and `{2,3}` — and so has a **second equivalent
   crossing, the pair `(0,3)`**. Routing across *that* alternative crossing also
   works, and crossed-pair-free rescues climb (1 → 8 → 47 for #3/#4; 1 → 5 → 27 →
   131 for #5) — but they stay a minority at every length.

The conclusion is clean: **the crown's crossing structure is the gatekeeper at
every length.** Longer connectors only let you reach the *alternative* crossing
or take a roundabout route across the same one. You never get to ignore the
crossing.

---

## How we know (and what's sampled vs verified)

The dimensions here are decided by the **z3 SMT oracle**, the same tool used
throughout this folder: it asks directly whether the happened-before poset equals
the intersection of `t` timelines, and an unsatisfiable answer at `t = d−1` with
a satisfiable one at `t = d` pins the dimension to exactly `d`. The marquee
example (the `(1,2)`-rescued composition) was additionally confirmed by
nomadim's **independent brute-force** dimension algorithm — two methods, same
answer.

The composition sweep itself is **exhaustive within its scope**: all 2400 `(A, B,
matching)` variants were generated and classified, not sampled, and the "28% stay
dim 2 / one sync → 100%" counts are exact over that set. The 5 crown classes and
5 dim-2 classes come from a Weisfeiler–Leman isomorphism signature on the
reachability closure. The crossed-pair and connector-length counts in the tables
are direct enumerations (`check_connector_pairs.py`, `check_connectors_len.py`).

The honest scope: all of this is **N = 4, blocks of 5 syncs, connectors up to
length 4**. It is a complete and verified picture *of that world*. It is not a
proof that the "one sync on the crossed pair" rule holds for larger N — that
generalization isn't claimed here. What *is* claimed is backed either by
exhaustive enumeration or by the z3 oracle (with the headline case double-checked
by brute force).

---

## Why it matters

Composition is how you'd actually build big executions out of small, cheap ones —
stack a `√N`-coordinate-clock execution on top of another and hope the result
stays cheap. This result is the warning *and* the remedy:

- **The warning:** gluing two dimension-2 blocks is *usually* (72% of wirings) a
  trap. A generic frontier alignment crosses into a crown and silently costs you
  a third clock coordinate.
- **The remedy:** that cost is repairable with the smallest possible move. One
  synchronization, placed across the crossing the gluing introduced, collapses
  the crown and restores the two-coordinate clock.

So "dimension repair" isn't an abstraction here — it's a concrete operation with
a concrete recipe: *find the pair your matching crossed, and sync it once.* The
crossing structure tells you both that you have a problem and exactly where to
put the one sync that fixes it.

---

*Source: `COMPOSE_N4.md` in this folder (the authoritative writeup, with the
2400-variant sweep, the 5 crown / 5 dim-2 classes, the crossed-pair table, and
the length-1–4 rescuer counts). Background: `FINDINGS.md` (the order-dimension /
√N story) and `EXPLAINER.md` (the companion piece). Verified example:
`N4_connector1_rescue_dim2.yaml`. Reproduce with `compose_n4.py`,
`compose_n4_connector.py`, `check_connector_pairs.py`, `check_connectors2.py`,
`check_connectors_len.py`.*

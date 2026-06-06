# Mirsky's theorem — upper-bound track (decomposition)

> Sub-track of the tractable-tier formalization. Goal: the **upper bound** of
> Mirsky's theorem — a finite poset has an antichain cover of size = height
> (longest-chain length) — which with the already-proved lower bound
> (`chain_le_antichain_cover`, `posets/dilworth/Mirsky.v`) gives equality.

**Status of prerequisites:** `fin_strict_wf : well_founded (StrictR R)` is DONE
(`posets/FinPosetWF.v`) — enables well-founded recursion on a finite poset.

## Strategy: rank by longest chain

Define `rank x` = length of a longest chain with top `x`, via
`rank x = 1 + max { rank y | StrictR y x }` (minimal elements ⇒ max over ∅ = 0
⇒ rank 1). Then height = max rank, levels `{x | rank x = k}` are antichains, and
the nonempty levels form a height-sized antichain cover.

## Components (categorized per long-running-formalization D1)

### Mechanical / reusable prerequisites
- **[P1] `finite_max_exists`** — for finite `S` and `f : A → nat`, there is `m`
  with `(∀x∈S, f x ≤ m)` and (`S=∅ ∧ m=0`) or (`∃x∈S, f x = m`). Induction on
  `cardinal S`, `Nat.max` at each step. *(starting this now)*
- **[P2] rank definition** — `rank := Fix fin_strict_wf (fun x rec => 1 + max
  over {y | StrictR y x} of (rec y _))`. The max-over-predecessors uses [P1]
  applied to `DownStrict x` (finite) with the dependent `rec`. Needs the
  `Fix_eq` recurrence (functional extensionality of the step) — the fiddliest
  mechanical piece. *Risk: Fix_eq plumbing.*

### Iterable / medium lemmas
- **[L1] rank recurrence** `rank x = 1 + max {rank y | y < x}` (from Fix_eq).
- **[L2] strict monotonicity** `StrictR y x → rank y < rank x` (from L1 + [P1]
  upper-bound clause).
- **[L3] levels are antichains** `Level k := {x | rank x = k}` is an antichain
  (comparable + equal rank ⇒ equal, by L2).
- **[L4] height = max rank** — `H := finite_max_exists (Full_set) rank`. A chain
  has length ≤ H (ranks strictly increase along it, L2 + pigeonhole/injectivity
  into `{1..H}`); and a chain of length = rank x exists (follow max-predecessor).

### Deep / assembly
- **[D1] the cover** `cover := { Level k | 1 ≤ k ≤ H, Level k ≠ ∅ }`:
  IsAntichainCover (covers: every x has rank∈[1,H]; antichains: L3) and
  `cardinal cover = H` (ranks 1..H each achieved ⇒ H distinct nonempty levels).
- **[D2] final** `mirsky_upper : ∃ cover, IsAntichainCover R (Full_set) cover ∧
  cardinal cover H` with `H` the height; combine with `chain_le_antichain_cover`
  for `mirsky` equality.

## Order of attack
P1 (now) → P2/L1 (rank + recurrence) → L2 → L3 → L4 → D1 → D2.
Each lands admit-free and builds via `timed-build.sh … <file>.vo 2` (verify `.vo`).

## Risks
- **Fix_eq plumbing (P2)**: the step function must be provably extensional in
  the recursive argument; `max`-over-Ensemble via [P1] uses `rec` only through
  `f`, so extensionality should go through, but this is the main risk. Fallback:
  define `rank` *relationally* (`RankIs x k`) with existence+uniqueness by
  well-founded induction, avoiding `Fix_eq` entirely.
- **L4 chain construction** (longest chain realizing rank x): may need its own
  recursion; if heavy, state height via max-rank as the *definition* and prove
  only the cover side (D1/D2), deferring the "= longest chain" identification.

# CRDT Implementations

This directory contains formal Coq implementations of various Conflict-free Replicated Data Types (CRDTs).

## Structure

Each CRDT is implemented in its own module file:

### State-Based CRDTs

- **GCounter.v** - Grow-only Counter
  - Monotonically increasing counter (increment only)
  - State: vector of natural numbers (one per replica)
  - Merge: component-wise maximum

- **PNCounter.v** - Positive-Negative Counter
  - Counter with increment and decrement operations
  - State: pair of G-Counters (positive and negative)
  - Merge: merge both underlying G-Counters

- **GSet.v** - Grow-only Set
  - Set supporting only additions
  - State: list of elements
  - Merge: set union

- **TwoPhaseSet.v** (2P-Set)
  - Set supporting add and remove (but no re-add)
  - State: pair of G-Sets (added and removed)
  - Merge: merge both underlying G-Sets
  - Membership: in added set but not in removed set

- **LWWRegister.v** - Last-Write-Wins Register
  - Single-value register with timestamp-based conflict resolution
  - State: value with timestamp
  - Merge: keep value with higher timestamp

## Properties

All CRDTs satisfy the core properties:

1. **Commutativity**: `merge(a, b) = merge(b, a)`
2. **Associativity**: `merge(merge(a, b), c) = merge(a, merge(b, c))`
3. **Idempotence**: `merge(a, a) = a`

These properties ensure **strong eventual consistency**: replicas that have received the same set of updates will converge to the same state.

## Usage

```coq
Require Import eventualConsistency.crdts.GCounter.
Require Import eventualConsistency.crdts.PNCounter.

(* Create and use a G-Counter *)
Definition counter := GCounter.init 3.  (* 3 replicas *)
Definition counter' := GCounter.increment counter 0.
Compute GCounter.query counter'.

(* Create and use a PN-Counter *)
Definition pn := PNCounter.init 2.
Definition pn' := PNCounter.increment pn 0.
Definition pn'' := PNCounter.decrement pn' 1.
```

## References

- Shapiro, M., Preguiça, N., Baquero, C., & Zawirski, M. (2011). "Conflict-free replicated data types"
- Shapiro, M., Preguiça, N., Baquero, C., & Zawirski, M. (2011). "A comprehensive study of CRDTs" (Technical Report)

# Happened-Before Relation Module

This submodule implements Lamport's happened-before relation for distributed systems.

## Structure

The module is divided into the following files:

### Core Files

1. **EventStructure.v** - Basic types and helper functions
   - `Event` record (process, clock)
   - `Message` record (send_event, recv_event)
   - `History` type (list of messages)
   - Helper functions: `In`, `nat_eqb`, `nat_leb`
   - Notation: `⟨p, c⟩` for events, `e1 →ₘ e2` for messages
   - **Lemmas**:
     - `message_connects_distinct_events`: Messages cannot loop to same event
   - **Properties**:
     - `lamport_clock_property`: `clock(send) < clock(recv)` (enforced by `Message` record)

2. **CausalRelation.v** - Happened-before and concurrency definitions
   - `same_process_before` - Events on same process
   - `message_link` - Direct message causality
   - `happened_before` - Inductive relation (reflexive-transitive closure)
   - `concurrent` - Events that are not ordered
   - Notation: `e1 ≺[h] e2`, `e1 ∥[h] e2`
   - **Theorems**:
     - `happened_before_acyclic`: Antisymmetry property

3. **PosetInstance.v** - Proof that happened-before is a partial order
   - `IsPoset` instance for `happened_before`
   - **Fully Proven**: Reflexivity, Antisymmetry, Transitivity

4. **LatticeOperations.v** - Meet and join operations
   - `event_meet` - Greatest lower bound (earlier event)
   - `event_join` - Least upper bound (later event)
   - Notation: `e1 ⊓[h] e2`, `e1 ⊔[h] e2`

5. **LatticeInstances.v** - Lattice proofs
   - `IsMeetSemilattice` instance
   - `IsJoinSemilattice` instance
   - `IsLattice` instance
   - `IsDistributiveLattice` instance
   - **Note**: These are currently admitted because the definitions in `LatticeOperations.v` correspond to a lexicographical total order, which contradicts the partial order nature of `happened_before`.

6. **Examples.v** - Concrete examples
   - Basic events and messages
   - Same-process ordering
   - Message causality
   - Transitive causality
   - Concurrent events (**Fully Proven**)
   - Meet/join examples
   - Complex multi-hop causality

7. **HappenedBefore.v** - Main aggregator
   - Imports and exports all submodules
   - Documentation of notation
   - Summary of theoretical properties

## Usage

```coq
Require HappenedBefore.HappenedBefore.

(* Create events *)
Definition e1 := ⟨0, 1⟩.  (* Process 0, clock 1 *)
Definition e2 := ⟨1, 0⟩.  (* Process 1, clock 0 *)

(* Create a message *)
Definition m := e1 →ₘ e2.

(* Define history *)
Definition h := cons m nil.

(* Use happened-before relation *)
Example causality : e1 ≺[h] e2.
```

## Notation Summary

| Notation | Meaning |
|----------|---------|
| `⟨p, c⟩` | Event with process `p` and clock `c` |
| `e1 →ₘ e2` | Message from `e1` to `e2` |
| `e1 ≺[h] e2` | `e1` happened-before `e2` in history `h` |
| `e1 ∥[h] e2` | `e1` and `e2` are concurrent in history `h` |
| `e1 ⊓[h] e2` | Meet (GLB) of `e1` and `e2` |
| `e1 ⊔[h] e2` | Join (LUB) of `e1` and `e2` |

Note: Notation without `[h]` assumes empty history (`nil`).

## Theoretical Properties

The happened-before relation forms:

1. **Poset** - Partial order (reflexive, antisymmetric, transitive) ✅ **Proven**
2. **Meet Semilattice** - Has greatest lower bounds ⚠️ **Invalid Definition**
3. **Join Semilattice** - Has least upper bounds ⚠️ **Invalid Definition**
4. **Lattice** - Has both meets and joins with absorption ⚠️ **Invalid Definition**
5. **Distributive Lattice** - Meet distributes over join ⚠️ **Invalid Definition**

This structure is fundamental to understanding causality in distributed systems,
vector clocks, and eventual consistency.

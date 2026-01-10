# Happened-Before Relation Module

This submodule implements Lamport's happened-before relation for distributed systems.

## Structure

The module is divided into the following files:

### Core Files

1. **EventStructure.v** - Basic types and helper functions
   - `Event` record (process ID)
   - `Message` record (send_event, recv_event)
   - `History` type (list of messages)
   - Helper functions: `In`, `nat_eqb`, `nat_leb`
   - Notation: `⟨p⟩` for events, `e1 →ₘ e2` for messages

2. **CausalRelation.v** - Happened-before and concurrency definitions
   - `message_link` - Direct message causality
   - `happened_before` - Inductive relation (reflexive-transitive closure)
   - `strict_happened_before` - Transitive closure (strict ordering)
   - `concurrent` - Events that are not ordered
   - `IsAcyclic` - Predicate ensuring no event strictly happens before itself
   - Notation: `e1 ≺[h] e2`, `e1 ≺+[h] e2`, `e1 ∥[h] e2`

3. **CausalRelationProps.v** - Properties and lemmas
   - `hb_refl_antisym`
   - `shb_implies_hb`
   - `hb_implies_shb_or_eq`
   - `hb_antisym_of_acyclic` - Proof that acyclicity implies antisymmetry

4. **PosetInstance.v** - Proof that happened-before is a partial order
   - `IsPoset` instance for `happened_before` (Requires `IsAcyclic h` hypothesis)
   - **Fully Proven**: Reflexivity, Antisymmetry, Transitivity

5. **LatticeOperations.v** - Meet and join operations
   - `event_meet` - Greatest lower bound (earlier event)
   - `event_join` - Least upper bound (later event)
   - Notation: `e1 ⊓[h] e2`, `e1 ⊔[h] e2`

6. **LatticeInstances.v** - Lattice proofs
   - `IsMeetSemilattice` instance
   - `IsJoinSemilattice` instance
   - `IsLattice` instance
   - `IsDistributiveLattice` instance
   - **Note**: These are currently admitted.

7. **Examples.v** - Concrete examples
   - Basic events and messages
   - Message causality
   - Transitive causality
   - Concurrent events (**Fully Proven**)
   - Meet/join examples
   - Complex multi-hop causality

8. **HappenedBefore.v** - Main aggregator
   - Imports and exports all submodules
   - Documentation of notation
   - Summary of theoretical properties

## Usage

```coq
Require HappenedBefore.HappenedBefore.

(* Create events *)
Definition e1 := ⟨0⟩.  (* Process 0 *)
Definition e2 := ⟨1⟩.  (* Process 1 *)

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
| `⟨p⟩` | Event with process `p` |
| `e1 →ₘ e2` | Message from `e1` to `e2` |
| `e1 ≺[h] e2` | `e1` happened-before `e2` in history `h` |
| `e1 ≺+[h] e2` | `e1` strictly happened-before `e2` in history `h` |
| `e1 ∥[h] e2` | `e1` and `e2` are concurrent in history `h` |
| `e1 ⊓[h] e2` | Meet (GLB) of `e1` and `e2` |
| `e1 ⊔[h] e2` | Join (LUB) of `e1` and `e2` |

Note: Notation without `[h]` assumes empty history (`nil`).

## Theoretical Properties

The happened-before relation forms:

1. **Poset** - Partial order (reflexive, antisymmetric, transitive) ✅ **Proven** (Given `IsAcyclic h`)
2. **Meet Semilattice** - Has greatest lower bounds ❌ **Proven Impossible** (`happened_before_not_poset_semilattice`)
3. **Join Semilattice** - Has least upper bounds ❌ **Proven Impossible** (`happened_before_not_join_semilattice_poset`)
4. **Lattice** - Has both meets and joins with absorption ❌ **Proven Impossible**
5. **Distributive Lattice** - Meet distributes over join ❌ **Proven Impossible**

This structure is fundamental to understanding causality in distributed systems,
vector clocks, and eventual consistency.

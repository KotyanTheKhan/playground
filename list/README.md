# List Poset Module

Custom list structure with length-based ordering and lattice operations.

## Structure

### Files

1. **Structure.v** - List data type and ordering
   - `List` inductive type (Nil, Cons)
   - `length_List` - Count elements
   - `append_List` - Concatenate lists
   - `list_le` - Ordering by length
   - Notation: `[]`, `[1; 2; 3]`, `l1 ++ l2`, `l1 ≤ₗ l2`

2. **Operations.v** - Lattice operations
   - `list_meet` - Returns shorter list
   - `list_join` - Returns longer list
   - Notation: `l1 ⊓ₗ l2`, `l1 ⊔ₗ l2`

3. **Instances.v** - Poset and lattice proofs
   - `IsPoset` instance
   - `IsMeetSemilattice` instance
   - `IsJoinSemilattice` instance
   - `IsLattice` instance

4. **Examples.v** - Usage examples
   - Example lists of various lengths
   - Ordering examples
   - Meet/join examples
   - Append and length examples

5. **List.v** - Main aggregator with documentation

## Usage

```coq
Require List.List.

(* Create lists *)
Definition l1 := [1; 2; 3].
Definition l2 := [4; 5].

(* Use ordering *)
Example ex : l2 ≤ₗ l1.  (* 2 elements ≤ 3 elements *)

(* Use lattice operations *)
Definition meet_result := l1 ⊓ₗ l2.  (* Returns l2, the shorter *)
Definition join_result := l1 ⊔ₗ l2.  (* Returns l1, the longer *)
```

## Notation

| Notation | Meaning |
|----------|---------|
| `[]` | Empty list |
| `[1; 2; 3]` | List with elements |
| `l1 ++ l2` | Append lists |
| `l1 ≤ₗ l2` | List ordering (by length) |
| `l1 ⊓ₗ l2` | List meet (shorter) |
| `l1 ⊔ₗ l2` | List join (longer) |

## Key Property

Lists are ordered by **length**, not by lexicographic comparison.
This means `[5] ≤ₗ [1; 2]` is true because 1 ≤ 2.

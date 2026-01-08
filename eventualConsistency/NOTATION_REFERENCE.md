# Eventual Consistency - Notation Quick Reference

## 📋 Construction & Building Blocks

| Notation | Meaning | Example |
|----------|---------|---------|
| `⟨r, s, v⟩ᵣ` | Replica state | `⟨0, myState, [1;2;0]⟩ᵣ` |
| `⟨o, r, ctx⟩ᵤ` | Update | `⟨increment, 1, [0;1;0]⟩ᵤ` |
| `s ⟶ r ∶ u` | Message | `0 ⟶ 1 ∶ update` |

## 📊 Version Vectors

| Notation | Meaning | Description |
|----------|---------|-------------|
| `v1 ⊑ v2` | Causally precedes | v1[i] ≤ v2[i] for all i |
| `v1 ⊔ᵥ v2` | Merge/Join | max(v1[i], v2[i]) for all i |
| `v ↑ r` | Increment | Increment version at replica r |

## 🔧 State Operations

| Notation | Meaning | Properties |
|----------|---------|------------|
| `s1 ⊔ s2` | Merge states | Commutative, Associative, Idempotent |
| `s ⊕ op` | Apply operation | Modifies state |
| `rs ⊙ u` | Apply update to replica | Updates state & version |
| `rs1 ⊔ᵣ rs2` | Merge replicas | Merges both state & version |

## 🔗 Relations & Ordering

### Causality
| Notation | Meaning | When true |
|----------|---------|-----------|
| `u1 ≺ᵤ u2` | Causal precedence | u1 happened before u2 |
| `u1 ∥ᵤ u2` | Concurrent | Neither happened before the other |

### States
| Notation | Meaning | Definition |
|----------|---------|------------|
| `s1 ≈ s2` | Equivalent states | s1 ⊔ s2 = s2 ⊔ s1 |
| `s1 ⊑ₛ s2` | Monotonic growth | s1 ⊔ s2 = s2 |

### Replicas
| Notation | Meaning | Definition |
|----------|---------|------------|
| `rs1 ≈ᵣ rs2` | Replicas converged | state rs1 = state rs2 |
| `⊤[cfg]` | Configuration converged | All replicas have same state |

## 📐 Consistency Axioms (using notation)

```coq
(* Commutativity *)
s1 ⊔ s2 = s2 ⊔ s1

(* Associativity *)
(s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3)

(* Idempotency *)
s ⊔ s = s

(* Monotonicity *)
s ⊑ₛ (s ⊕ op)
```

## 🎯 Common Patterns

### Applying an update
```coq
r' = r ⊙ u
(* Equivalent to:
   {| replica_id := id r
    ; state := (state r) ⊕ (op u)
    ; version := (version r) ⊔ᵥ (causal_context u)
   |}
*)
```

### Checking causality
```coq
if u1 ≺ᵤ u2 then
  (* u1 must be applied before u2 *)
else if u1 ∥ᵤ u2 then
  (* u1 and u2 can be applied in any order *)
```

### Convergence check
```coq
if ⊤[cfg] then
  (* All replicas agree on state *)
```

## 🔍 Theorem Statements (using notation)

```coq
(* Strong Eventual Consistency *)
∀ replicas updates.
  deliver_all_updates replicas updates ⟹ ⊤[replicas]

(* Concurrent Updates Commute *)
∀ u1 u2. u1 ∥ᵤ u2 ⟹ 
  (s ⊕ (op u1)) ⊕ (op u2) = (s ⊕ (op u2)) ⊕ (op u1)

(* Monotonic Growth *)
∀ rs u. (state rs) ⊑ₛ (state (rs ⊙ u))
```

## 💡 Tips

1. **⊔** (sqcup) represents "join" or "least upper bound" - always merges upward
2. **⊑** (sqsubseteq) represents "grows to" or "less than or equal" in the lattice
3. **≺** (prec) represents "causally before" - strict ordering
4. **∥** (parallel) represents "concurrent" - no causal relationship
5. **≈** (approx) represents "equivalent" - can merge to same state
6. **⊤** (top) represents "convergence" - all at the top of the lattice

## 🌟 Example Usage

```coq
(* Create replicas *)
Definition r0 := ⟨0, initial_state, [0;0]⟩ᵣ.
Definition r1 := ⟨1, initial_state, [0;0]⟩ᵣ.

(* Create concurrent updates *)
Definition u0 := ⟨op_inc, 0, [0;0]⟩ᵤ.
Definition u1 := ⟨op_inc, 1, [0;0]⟩ᵤ.

(* Apply updates (order doesn't matter for concurrent) *)
Definition r0' := r0 ⊙ u0 ⊙ u1.
Definition r1' := r1 ⊙ u1 ⊙ u0.

(* Both reach same state *)
Lemma convergence : r0' ≈ᵣ r1'.
```

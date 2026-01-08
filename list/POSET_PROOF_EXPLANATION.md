# Complete Poset Proof Explanation

## 📚 Overview

This document provides a step-by-step explanation of proving that **lists form a partially ordered set (poset)** under the `list_le` relation.

---

## 🎯 What is a Poset?

A **partially ordered set** requires three properties:

1. **Reflexivity**: `∀ x, x ≤ x`
2. **Antisymmetry**: `∀ x y, x ≤ y → y ≤ x → x = y`
3. **Transitivity**: `∀ x y z, x ≤ y → y ≤ z → x ≤ z`

---

## 📝 The List Ordering Definition

```coq
Definition list_le (l1 l2 : List) : Prop :=
  length_List l1 < length_List l2 \/
  (length_List l1 = length_List l2 /\ list_lex_le l1 l2).
```

**Meaning**: List `l1 ≤ l2` if either:
- `l1` is **shorter** than `l2`, OR
- They have **equal length** AND `l1` is **lexicographically** less than or equal to `l2`

### Lexicographic Ordering

```coq
Fixpoint list_lex_le (l1 l2 : List) : Prop :=
  match l1, l2 with
  | Nil, _ => True                    (* Empty list ≤ anything *)
  | Cons _ _, Nil => False            (* Non-empty > empty *)
  | Cons x xs, Cons y ys =>
      x < y \/ (x = y /\ list_lex_le xs ys)  (* Compare heads, then tails *)
  end.
```

---

## ✅ Proof 1: Reflexivity

### Goal
Prove: `∀ l, l ≤ l`

### Strategy

1. **Unfold** `list_le` reveals:
   ```coq
   length l < length l \/ (length l = length l /\ list_lex_le l l)
   ```

2. **Choose `right`** - The left side (`length l < length l`) is false

3. **Split** the conjunction into two goals:
   - `length l = length l` ✓ (trivial by reflexivity)
   - `list_lex_le l l` (requires induction)

4. **Induction** on `l`:

   **Base case** (`Nil`):
   - Goal after `simpl`: `True`
   - Solved by `trivial`

   **Inductive case** (`Cons a l'`):
   - Goal after `simpl`: `a < a \/ (a = a /\ list_lex_le l' l')`
   - Choose `right` (since `a < a` is false)
   - Split into:
     - `a = a` (solved by `reflexivity`)
     - `list_lex_le l' l'` (solved by inductive hypothesis)

### Key Tactics
- `right`: Choose right side of disjunction (`\/`)
- `split`: Break conjunction (`/\`) into separate goals
- `simpl`: Compute fixpoint definitions
- `trivial`: Prove `True`

---

## ✅ Proof 2: Antisymmetry

### Goal
Prove: `∀ l1 l2, l1 ≤ l2 → l2 ≤ l1 → l1 = l2`

### Strategy

1. **Unfold** both `l1 ≤ l2` and `l2 ≤ l1`

2. **Case Analysis** on both hypotheses (4 cases total):

   | Case | H12 (l1 ≤ l2) | H21 (l2 ≤ l1) | Result |
   |------|---------------|---------------|---------|
   | 1 | `len l1 < len l2` | `len l2 < len l1` | Contradiction! ✗ |
   | 2 | `len l1 < len l2` | `len l2 = len l1` | Contradiction! ✗ |
   | 3 | `len l1 = len l2` | `len l2 < len l1` | Contradiction! ✗ |
   | 4 | `len l1 = len l2` | `len l2 = len l1` | Need lexicographic antisymmetry |

3. **Cases 1-3**: Use `lia` to derive contradiction from arithmetic inequalities

4. **Case 4**: Prove by **lexicographic antisymmetry**
   - Use induction on `l1`
   - **Base case** (`Nil`): If `l1 = Nil` and lengths equal, then `l2 = Nil` → equal
   - **Inductive case** (`Cons a1 l1'`):
     - `l2` must be `Cons a2 l2'` (lengths equal)
     - After `simpl`, we have:
       - `Hlex12`: `a1 < a2 \/ (a1 = a2 /\ list_lex_le l1' l2')`
       - `Hlex21`: `a2 < a1 \/ (a2 = a1 /\ list_lex_le l2' l1')`
     - **Sub-case analysis**:
       - `a1 < a2` and `a2 < a1` → Contradiction ✗
       - `a1 < a2` and `a2 = a1` → Contradiction ✗
       - `a1 = a2` and `a2 < a1` → Contradiction ✗
       - `a1 = a2` and `a2 = a1` → Both heads equal, use IH for tails ✓

5. **Final step**: Use `f_equal` to prove `Cons a1 l1' = Cons a2 l2'` by showing:
   - `a1 = a2` (from hypothesis)
   - `l1' = l2'` (by inductive hypothesis with 3 arguments)

### Key Tactics
- `destruct H as [H1 | H2]`: Case analysis on disjunction
- `lia`: Solve linear arithmetic (finds contradictions)
- `discriminate`: Prove contradiction from impossible constructor equality
- `injection ... as ...`: Extract equality from constructor equality
- `f_equal`: Prove constructor equality by proving field equalities
- `subst`: Substitute equalities

### Critical Insight
After `simpl in Hlex12, Hlex21`, the variables change! We saved copies with `assert` before simplifying to avoid losing them.

---

## ✅ Proof 3: Transitivity

### Goal
Prove: `∀ l1 l2 l3, l1 ≤ l2 → l2 ≤ l3 → l1 ≤ l3`

### Strategy

1. **Unfold** all three relations

2. **Case Analysis** on `H12` and `H23` (4 cases):

   | Case | H12 (l1 ≤ l2) | H23 (l2 ≤ l3) | Result |
   |------|---------------|---------------|---------|
   | 1 | `len l1 < len l2` | `len l2 < len l3` | `len l1 < len l3` by transitivity of `<` |
   | 2 | `len l1 < len l2` | `len l2 = len l3` | `len l1 < len l3` (since `l1 < l2 = l3`) |
   | 3 | `len l1 = len l2` | `len l2 < len l3` | `len l1 < len l3` (since `l1 = l2 < l3`) |
   | 4 | `len l1 = len l2` | `len l2 = len l3` | Need lexicographic transitivity |

3. **Cases 1-3**: Use `left` and `lia` to prove length inequality

4. **Case 4**: Prove by **lexicographic transitivity**
   - Use `right` and prove:
     - `length l1 = length l3` (by transitivity of equality)
     - `list_lex_le l1 l3` (by induction)
   
   - **Induction** on `l1`:
     - **Base case** (`Nil`): `list_lex_le Nil l3 = True` (trivial)
     - **Inductive case** (`Cons a1 l1'`):
       - `l2` must be `Cons a2 l2'` (length equality)
       - `l3` must be `Cons a3 l3'` (length equality)
       - After `simpl`, we have:
         - `Hlex12`: `a1 < a2 \/ (a1 = a2 /\ list_lex_le l1' l2')`
         - `Hlex23`: `a2 < a3 \/ (a2 = a3 /\ list_lex_le l2' l3')`
       - **Sub-case analysis** (4 cases):
         - `a1 < a2 < a3` → `a1 < a3` by transitivity ✓
         - `a1 < a2 = a3` → `a1 < a3` ✓
         - `a1 = a2 < a3` → `a1 < a3` ✓
         - `a1 = a2 = a3` → Use IH: `list_lex_le l1' l2'` and `list_lex_le l2' l3'` imply `list_lex_le l1' l3'` ✓

### Key Tactics
- `left` / `right`: Choose side of disjunction
- `lia`: Solve arithmetic transitivity
- `apply (IH l2')`: Apply inductive hypothesis with middle element
- `exact`: Provide exact proof term
- `simpl in ...`: Simplify specific hypotheses

### Critical Pattern
The "middle element" pattern: To prove `l1 ≤ l3`, use `l2` as a bridge:
```coq
apply (IH l2').
```

---

## 🎓 Key Lessons Learned

### 1. **Definitions Matter**
`list_le` uses logical connectives (`\/`, `/\`), not inductive constructors. This affects which tactics work.

### 2. **Bullet Discipline**
Coq requires strict nesting:
```
-     (top level)
  +   (second level)
    * (third level)
      --   (fourth level)
        ++ (fifth level)
          *** (sixth level)
            ---- (seventh level)
              +++++ (eighth level)
```

### 3. **Variable Hygiene**
After `simpl` or `destruct`, variable names can change. Use `assert` to save copies when needed.

### 4. **Induction Patterns**
- **Structural induction**: On the data structure itself
- **Nested induction**: Inner induction happens in a sub-bullet
- **Generalize dependent**: Prepare variables for induction

### 5. **Case Analysis Strategy**
When you have `H: A \/ B`:
- Use `destruct H as [HA | HB]` to split into cases
- Eliminate impossible cases with `lia` or `discriminate`
- Handle remaining cases constructively

---

## 🔧 Tactic Reference

| Tactic | Purpose | Example |
|--------|---------|---------|
| `unfold` | Reveal definition | `unfold list_le` |
| `intros` | Introduce variables | `intros l1 l2 H` |
| `split` | Prove conjunction | Turns `A /\ B` into two goals |
| `left` / `right` | Choose disjunction side | For goal `A \/ B` |
| `destruct` | Case analysis | `destruct H as [H1 \| H2]` |
| `induction` | Structural induction | `induction l as [\| a l' IH]` |
| `simpl` | Compute/simplify | `simpl in H` |
| `lia` | Linear arithmetic solver | Proves `x < y`, finds contradictions |
| `discriminate` | Constructor contradiction | `0 = S n` is impossible |
| `injection` | Extract from constructor | `S x = S y` → `x = y` |
| `f_equal` | Prove by parts | `Cons a l = Cons b m` → prove `a=b` and `l=m` |
| `subst` | Substitute equalities | Replace variable with its equal |
| `assumption` | Use hypothesis | Goal matches a hypothesis |
| `exact` | Provide exact term | `exact H` |
| `trivial` | Prove `True` | Auto-solves trivial goals |
| `exfalso` | Proof by contradiction | Changes goal to `False` |
| `reflexivity` | Prove `x = x` | Auto-proves reflexive equality |
| `clear` | Remove hypothesis | Clean up context |
| `generalize dependent` | Prepare for induction | Make variable general |
| `assert` | Create new hypothesis | `assert (H := expr)` |

---

## 🎯 Proof Patterns

### Pattern 1: Reflexivity with OR
```coq
unfold definition.
right.  (* Choose non-trivial side *)
split.
  + (* Prove equality part *)
    reflexivity.
  + (* Prove structural part *)
    induction ...
```

### Pattern 2: Antisymmetry with Case Analysis
```coq
destruct H1 as [bad_case | [eq_case good_case]];
destruct H2 as [bad_case' | [eq_case' good_case']].
  + (* bad + bad *) lia.
  + (* bad + good *) lia.
  + (* good + bad *) lia.
  + (* good + good *) (* actual proof *)
```

### Pattern 3: Transitivity with Middle Element
```coq
apply (IH middle_element).
  - (* Prove first connection *)
  - (* Prove second connection *)
```

---

## 🚀 Next Steps

Now that you've completed the list poset proof, you can:

1. **Prove other instances**: Trees, sets, multisets
2. **Prove lattice properties**: If lists form a lattice
3. **Prove derived properties**: Using poset laws
4. **Build abstractions**: Generic proofs over any poset

**Congratulations on completing this complex proof!** 🎉

---

*This proof demonstrates the power of structural induction and careful case analysis in Coq. Each tactic was chosen deliberately to match the structure of the definitions.*

# Element_Size_6 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the `Admitted` in `Element_Size_6` with a complete Coq proof.

**Architecture:** Two-step enumeration proof. (1) Assert `Full_set Element` equals an explicit 6-element `Add`-chain via `Extensionality_Ensembles`. (2) Count with nested `card_add`/`card_empty`, closing non-membership goals by inversion chains. Mirrors `MyAntichain_Size` (line 230 of the same file).

**Tech Stack:** Coq / Ensembles stdlib (`Extensionality_Ensembles`, `card_add`, `card_empty`, `solve_not_in_empty`)

---

### Task 1: Prove Element_Size_6

**Files:**
- Modify: `posets/dilworth/ConcreteExample.v:526`

- [ ] **Step 1: Replace the Admitted with the complete proof**

Replace lines 525–526 of `posets/dilworth/ConcreteExample.v`:

```coq
  Lemma Element_Size_6 : cardinal Element (Full_set Element) 6.
  Proof. Admitted.
```

with:

```coq
  Lemma Element_Size_6 : cardinal Element (Full_set Element) 6.
  Proof.
    assert (Heq : Full_set Element =
      Add Element (Add Element (Add Element (Add Element
        (Add Element (Add Element (Empty_set Element)
          (AA I0)) (AA I1)) (AA I2))
          (BB I0)) (BB I1)) (BB I2)).
    { apply Extensionality_Ensembles; intro e; split.
      - intros _; destruct e as [i|i]; destruct i;
        repeat first [apply Union_intror; apply In_singleton | apply Union_introl].
      - intros _; apply Full_intro. }
    rewrite Heq.
    apply card_add; [apply card_add; [apply card_add; [apply card_add;
      [apply card_add; [apply card_add |] |] |] |] |].
    - apply card_empty.
    - solve_not_in_empty.
    - intros H; inversion H; subst; inversion H0.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1; subst;
        inversion H2.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1; subst;
        inversion H2; subst; inversion H3.
    - intros H; inversion H; subst; inversion H0; subst; inversion H1; subst;
        inversion H2; subst; inversion H3; subst; inversion H4.
  Qed.
```

**Proof sketch (for the reviewer):**

`Heq` rewrites `Full_set Element` as the explicit 6-element chain
`Add^6 Empty (AA I0)(AA I1)(AA I2)(BB I0)(BB I1)(BB I2)`.

Forward direction of `Extensionality_Ensembles`: `destruct e as [i|i]; destruct i` produces 6 cases. `repeat first [apply Union_intror; apply In_singleton | apply Union_introl]` walks right-first through the chain: tries to place the element via `Union_intror + In_singleton` at each level; if the singleton doesn't match, falls back to `Union_introl` to go one level deeper. This terminates because the chain is finite and each element appears exactly once.

Backward direction: `apply Full_intro` (everything is in `Full_set`).

After `rewrite Heq`, the 6 nested `card_add` calls peel off one element at a time, leaving 7 goals:
1. `cardinal Empty 0` → `card_empty`
2. `¬ In Empty (AA I0)` → `solve_not_in_empty`
3. `¬ In {AA I0} (AA I1)` → 2-level inversion chain (H, H0)
4. `¬ In {AA I0, AA I1} (AA I2)` → 3-level chain (H, H0, H1)
5. `¬ In {AA I0, AA I1, AA I2} (BB I0)` → 4-level chain (H through H2)
6. `¬ In {AA I0..BB I0} (BB I1)` → 5-level chain (H through H3)
7. `¬ In {AA I0..BB I1} (BB I2)` → 6-level chain (H through H4)

Each inversion chain decomposes the `Union`/`Singleton` structure until reaching `In (Empty_set) _` (no constructors, closes) or `In (Singleton X) Y` where `X ≠ Y` (constructor or index mismatch, closes via `inversion`'s internal `discriminate`).

- [ ] **Step 2: Build**

Run: `mise run build-posets`

Expected: clean build, no errors, no admitted warnings for `Element_Size_6`.

- [ ] **Step 3: Commit**

```bash
git add posets/dilworth/ConcreteExample.v
git commit -m "Complete Element_Size_6 proof — explicit enumeration of all 6 elements"
```

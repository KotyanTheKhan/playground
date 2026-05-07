# Element_Size_6 proof — design

**Date:** 2026-05-06  
**Target:** `posets/dilworth/ConcreteExample.v`, line 526  
**Scope:** Replace `Admitted` in `Element_Size_6` with a complete proof. No other changes.

## Statement

```coq
Lemma Element_Size_6 : cardinal Element (Full_set Element) 6.
```

The `Element` type has exactly 6 values — `AA I0`, `AA I1`, `AA I2`, `BB I0`, `BB I1`, `BB I2` — so the statement is true.

## Approach: explicit enumeration

Mirrors `MyAntichain_Size` (line 230 of the same file), which proves `cardinal Element MyAntichain 3` by the same two-step pattern.

### Step 1 — rewrite `Full_set Element` as an explicit 6-element `Add`-chain

```coq
assert (Heq : Full_set Element =
  Add Element (Add Element (Add Element (Add Element
    (Add Element (Add Element (Empty_set Element)
      (AA I0)) (AA I1)) (AA I2))
      (BB I0)) (BB I1)) (BB I2)).
{ apply Extensionality_Ensembles; intro e; split.
  - (* e ∈ Full_set → e in explicit list *)
    intros _; destruct e as [i|i]; destruct i;
    (* 6 cases, each closed by Union_introl/Union_intror + In_singleton *)
    repeat first [apply Union_introl | apply Union_intror | apply In_singleton].
  - (* e in explicit list → e ∈ Full_set *)
    intros _; apply Full_intro. }
```

### Step 2 — count with `card_add`/`card_empty`

```coq
rewrite Heq.
apply card_add; [apply card_add; [apply card_add; [apply card_add;
  [apply card_add; [apply card_add |] |] |] |] |].
- apply card_empty.
- solve_not_in_empty.          (* AA I0 ∉ ∅ *)
- intros H; inversion H; subst; (* AA I1 ∉ {AA I0} *)
    [inversion H0 | discriminate].
- (* AA I2 ∉ {AA I0, AA I1} *) ...
- (* BB I0 ∉ {AA I0, AA I1, AA I2} *) ...
- (* BB I1 ∉ {AA I0..BB I0} *) ...
- (* BB I2 ∉ {AA I0..BB I1} *) ...
```

Non-membership goals all close by `inversion` + `discriminate` (AA ≠ BB by constructor mismatch; same-constructor cases use `Index` discriminability).

## Constraints

- Only touch the `Admitted` proof; leave the lemma statement and surrounding file unchanged.
- No new imports, no new lemmas.
- Build check: `mise run build-posets`.

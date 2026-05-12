# Dimension Remaining Admits — Design Spec

## Goal

Close all remaining `Admitted` lemmas in `posets/dimension/`. Nine admits across five files, grouped into five tracks.

---

## Section 1 — Shared Helper Lemmas

Two new helpers needed by multiple downstream proofs. Both are proved by induction on `cardinal`.

### `cardinal_image_le`

```coq
Lemma cardinal_image_le :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n m : nat),
  cardinal U S n ->
  cardinal V (Im U V S f) m ->
  m <= n.
```

Proof: induction on `cardinal U S n`. Base: Im of ∅ is ∅, cardinal 0. Step: Im of (Add S x) = Add (Im S f) (f x); cardinality of the image is ≤ n+1 by induction.

Used by: `subposet_dimension_le` (Section 3b).

### `exists_maximal`

```coq
Lemma exists_maximal :
  forall (A : Type) (rel : A -> A -> Prop) `{IsPoset A rel}
         (S : Ensemble A),
  Finite A S -> Inhabited A S ->
  exists x, In A S x /\ forall y, In A S y -> rel x y -> y = x.
```

Proof: apply `exists_minimal` (already proved in Theorems.v) to the flipped relation `fun a b => rel b a` with the flipped IsPoset instance.

Used by: `incomparable_lifting_to_critical_pair` (Section 4, for the maximal element of T_y).

---

## Section 2 — LinearSum.v (4 admits)

All four admits are in `linear_sum_realizer_lifting`.

### Nonemptiness admits (lines 453, 463, 474)

**Fix**: Add `0 < na` and `0 < nb` as hypotheses to `linear_sum_realizer_lifting`.

**New helper**:
```coq
Lemma cardinal_pos_nonempty :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n -> 0 < n -> exists x, In U S x.
```
Proof: by induction on cardinal; base (n=0) contradicts `0 < n`; step gives the element directly.

At the start of the proof, extract `LA₀ ∈ realizerA` and `LB₀ ∈ realizerB`. Each of the three admits then becomes a one-liner:
- Line 453: `exact (HrA_lin LA HLA (combine_extensions LA LB₀) ...)`
- Line 463: contradiction by instantiating Hall with `combine_extensions LA₀ LB₀`
- Line 474: symmetric to line 453

The `linear_sum_dimension` call site passes `dA` and `dB` as the cardinalities, and both are ≥ 1 for any non-trivial poset, so the new hypotheses hold at all call sites.

### Cardinality admit (line 477)

The current cross-product construction `{ combine_extensions LA LB | LA ∈ rA, LB ∈ rB }` has size up to `na * nb`, not `max(na, nb)`. The construction must be replaced.

**New helper**:
```coq
Lemma cardinal_to_list :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n ->
  exists l : list U,
    length l = n /\
    (forall x, In U S x <-> List.In x l) /\
    List.NoDup l.
```
Proof: induction on cardinal. Base: `l = []`. Step: append the new element.

**Zip-with-padding construction** (WLOG `na ≤ nb`, otherwise swap and handle symmetrically):
1. Obtain `la : list (A→A→Prop)` (length `na`) and `lb : list (B→B→Prop)` (length `nb`)
2. Let `LA₀ = List.hd la` (safe since `0 < na`), `LB₀ = List.hd lb`
3. Define `zip_i : nat → (A+B→A+B→Prop)` as `fun i => combine_extensions (nth i la LA₀) (nth i lb LB₀)`
4. Redefine `realizerSum := Im nat (A+B→A+B→Prop) {i | i < nb} zip_i`

**IsRealizer proof for the new construction:**
- `realizer_linear`: `zip_i i` is a linear extension (uses `combine_extensions_is_linear` already proved)
- `realizer_intersection` inl-inl case: any `LA ∈ rA` equals `la[j]` for some `j < na ≤ nb` (by `cardinal_to_list`); `zip_j` uses that `LA`
- `realizer_intersection` inr-inr case: symmetric using `lb`

**Cardinality = nb = max(na, nb):**

New helper:
```coq
Lemma combine_extensions_injective :
  forall (A B : Type)
         (LA1 LA2 : A -> A -> Prop) (LB1 LB2 : B -> B -> Prop),
  combine_extensions LA1 LB1 = combine_extensions LA2 LB2 ->
  LA1 = LA2 /\ LB1 = LB2.
```
Proof: by `propext` + `funext`; evaluate at `(inl a, inl a')` to extract `LA1 = LA2`, at `(inr b, inr b')` to extract `LB1 = LB2`.

New helper:
```coq
Lemma nth_nodup_inj :
  forall (U : Type) (l : list U) (d : U) (i j : nat),
  List.NoDup l -> i < length l -> j < length l ->
  nth i l d = nth j l d -> i = j.
```
Proof: standard list induction.

New helper:
```coq
Lemma cardinal_Im_injective :
  forall (U V : Type) (S : Ensemble U) (f : U -> V) (n : nat),
  cardinal U S n ->
  (forall x y, In U S x -> In U S y -> f x = f y -> x = y) ->
  cardinal V (Im U V S f) n.
```
Proof: induction on cardinal; use injectivity to show the image element is fresh at each step.

With these: prove `zip_i` injective on `{i | i < nb}` (case-split on whether `i, j < na` or one/both ≥ `na`, using `nth_nodup_inj` on `la` and `lb` and `combine_extensions_injective`). Then `cardinal_Im_injective` gives `cardinal realizerSum nb`.

---

## Section 3 — ProductDimension.v + subposet_dimension_le

### `product_realizer_exists` (fully admitted)

Add `0 < nA` and `0 < nB` hypotheses. Extract `LA₀ ∈ rA` and `LB₀ ∈ rB` via `cardinal_pos_nonempty`.

**Construction:**
```coq
rProd_A := Im (A->A->Prop) _ rA (fun LA => LexOrder LA LB₀)
rProd_B := Im (B->B->Prop) _ rB (fun LB => LexOrder LA₀ LB)
rProd   := Union _ rProd_A rProd_B
```

**IsRealizer proof**: For incomparable pair `((a1,b1),(a2,b2))` in the product — i.e. neither `ProductRel (a1,b1)(a2,b2)` nor `ProductRel (a2,b2)(a1,b1)`:
- Either a1, a2 are RA-incomparable: some `LA ∈ rA` separates them; `LexOrder LA LB₀` separates the product pair via the LA component
- Or b1, b2 are RB-incomparable: some `LB ∈ rB` separates them; `LexOrder LA₀ LB` separates via the LB component

**Cardinality ≤ nA + nB**: use `cardinal_union_le`:
```coq
Lemma cardinal_union_le :
  forall (U : Type) (A B : Ensemble U) (m n : nat),
  cardinal U A m -> cardinal U B n ->
  exists k, cardinal U (Union U A B) k /\ k <= m + n.
```
(From `Finite_sets_facts` or proved by induction on `cardinal A m`.)

Plus `|rProd_A| ≤ nA` and `|rProd_B| ≤ nB` from `cardinal_Im_intro` (already in scope from LinearSum proofs).

### `subposet_dimension_le` — `HrQ_exists`

**Fix**: Restructure the theorem to use the subtype `{x : A | In A S x}` as carrier.

New statement:
```coq
Theorem subposet_dimension_le :
  forall (S : Ensemble A) (d_p : nat),
  PosetDimension R d_p ->
  exists d_q,
    inhabited (@PosetDimension {x : A | In A S x}
                (fun x y => R (proj1_sig x) (proj1_sig y)) _ d_q) /\
    d_q <= d_p.
```

**IsPoset instance** on `{x | In A S x}`: straightforward local declaration inheriting R's reflexivity/antisymmetry/transitivity via `proj1_sig`.

**Construction of rQ**: define `proj_S : (A→A→Prop) → ({x|InSx}→{x|InSx}→Prop)` as `fun LP x y => LP (proj1_sig x) (proj1_sig y)`. Let `rQ := Im (A→A→Prop) _ rP proj_S`.

**IsRealizer proof**:
- `realizer_linear`: `proj_S LP` is a total order on the subtype extending `R|_S` (inherits from LP being a total order on A extending R)
- `realizer_intersection`: `R|_S x y ↔ R (proj1_sig x) (proj1_sig y) ↔ ∀ LP ∈ rP, LP ... ↔ ∀ LP_S ∈ rQ, LP_S x y` — follows because rP realizes R on A

**Cardinality ≤ d_p**: `|rQ| ≤ |rP| = d_p` by `cardinal_image_le` (Section 1 helper).

Since `subposet_dimension_le` is not referenced outside Theorems.v (and the conclusion type changes), update the call site in `hiraguchi_bound` accordingly.

---

## Section 4 — `incomparable_lifting_to_critical_pair`

**The theorem is false for general infinite posets** (counterexample: ℤ×ℤ with coordinatewise order, pair (0,0) and (1,−1) has no critical pair below/above it). `Finite A (Full_set A)` is necessary.

**Add to CriticalPairs section**:
```coq
Context (HfinA : Finite A (Full_set A)).
```

This propagates to `incomparable_lifting_to_critical_pair` and `critical_pair_realizer_iff`. No external file uses either theorem (verified by grep), so no further propagation.

**Re-prove `exists_minimal` locally** in CriticalPairs.v (can't import Theorems.v due to circular dependency: Theorems.v imports CriticalPairs.v). Same proof as in Theorems.v (~20 lines).

**`exists_maximal`** (from Section 1): define in CriticalPairs.v by applying `exists_minimal` to the flipped relation.

**Proof of `incomparable_lifting_to_critical_pair`** given `Incomparable R x y`:

Step 1 — find x':
- `S_x := {a | R a x ∧ ¬R a y}`
- Inhabited: `x ∈ S_x` (R x x; ¬R x y from Incomparable)
- Finite: `Finite_downward_closed` from Stdlib's Finite_sets_facts with `S_x ⊆ Full_set A`
- Apply `exists_minimal` on `(S_x, R)` → x' with `In S_x x'` and `∀ a ∈ S_x, R a x' → a = x'`

Step 2 — find y':
- `T_y := {b | R y b ∧ ¬R x' b}`
- Inhabited: `y ∈ T_y` (R y y; ¬R x' y since x' ∈ S_x means ¬R x' y)
- Finite: same pattern
- Apply `exists_maximal` on `(T_y, R)` → y' with `In T_y y'` and `∀ b ∈ T_y, R y' b → b = y'`

Step 3 — verify witnesses:
- `R x' x`: from x' ∈ S_x ✓
- `R y y'`: from y' ∈ T_y ✓

Step 4 — verify `IsCriticalPair x' y'`:
- `¬R x' y'`: from y' ∈ T_y ✓
- `¬R y' x'`: R y' x' → R y x' (R y y' + transitivity) → R y x (R x' x + transitivity), contradicting Incomparable ✓
- `critical_down` (∀ a, Strict R a x' → R a y): if ¬R a y, then R a x (R a x' + R x' x) so a ∈ S_x; but R a x' with a ≠ x' contradicts minimality of x' in S_x ✓
- `critical_up` (∀ b, Strict R y' b → R x' b): if ¬R x' b, then R y b (R y y' + R y' b) so b ∈ T_y; but R y' b with y' ≠ b contradicts maximality of y' in T_y ✓

---

## Section 5 — `hiraguchi_bound`

### Chain case (`Hd1 : d ≤ 1`)

From `Hchain`: every pair satisfies R x y ∨ R y x.

Construct `IsTotalOrder R`:
- `total_is_poset`: already have `IsPoset A R`
- `total_comparable`: directly from Hchain + classical logic

Show `{R}` is a realizer of cardinal 1:
- `singleton_cardinal : cardinal (A→A→Prop) (Singleton _ R) 1` — proved as `cardinal_add ∅ R (cardinal_empty _) (not_In_empty R)`
- `realizer_linear`: R is a total order that extends R (trivially)
- `realizer_intersection`: R x y ↔ R x y

Apply `dimension_is_minimum (R := R) (d := d) (Singleton _ R) 1` → `d ≤ 1`. Then `lia` closes n/2 ≥ 1 for n ≥ 4.

### Incomparable case (`Hkey : d ≤ n/2`)

**Step 1 — get finite type and critical pair.**

Helper:
```coq
Lemma cardinal_to_finite :
  forall (U : Type) (S : Ensemble U) (n : nat),
  cardinal U S n -> Finite U S.
```
(By induction: `cardinal_empty` → `Finite_Empty`; `cardinal_add` → `Finite_Add`.)

From `Hcard : cardinal A (Full_set A) n`, get `HfinA : Finite A (Full_set A)` via `cardinal_to_finite`. Apply `incomparable_lifting_to_critical_pair HfinA x y Hinc` → critical pair (x', y') with `R x' x`, `R y y'`, `IsCriticalPair x' y'`.

**Step 2 — form subposet P' on A \ {x', y'}.**

```coq
S' := Subtract A (Subtract A (Full_set A) x') y'
```

Cardinal of S' is n−2:
- `cardinal_subtract : cardinal A S n → In A S x → cardinal A (Subtract A S x) (n−1)` (from Finite_sets_facts or small lemma)
- Apply twice: `cardinal A S' (n−2)`

**Step 3 — apply IH.**

Apply `subposet_dimension_le` (Section 3) on S' with `HdP` to get dimension d' of P' with `d' ≤ d`.

Handle small cases n = 4, 5 separately by arithmetic (for n ∈ {4, 5}: n−2 ∈ {2, 3} < 4, so IH bound `d' ≤ (n−2)/2` doesn't follow from `hiraguchi_bound`; instead show `d' ≤ 1` directly since P' has ≤ 3 elements and any poset on ≤ 3 elements has dim ≤ 1).

For n ≥ 6: apply `IH (n−2)` (strong induction, `n−2 < n`) with `Hn : n−2 ≥ 4` (from n ≥ 6) → `d' ≤ (n−2)/2`.

**Step 4 — extension lemma.**

```coq
Lemma extension_through_critical_pair :
  forall (x' y' : A) (S' : Ensemble A) (r' : Ensemble (A→A→Prop)) (d' : nat),
  IsCriticalPair x' y' ->
  ¬ In A S' x' -> ¬ In A S' y' ->
  @IsRealizer A (fun a b => In A S' a ∧ In A S' b ∧ R a b) _ r' ->
  cardinal (A→A→Prop) r' d' ->
  exists r : Ensemble (A→A→Prop),
    IsRealizer R r /\
    cardinal (A→A→Prop) r (d' + 1).
```

**Construction of the extension realizer:**

For each L' ∈ r', build `L̃'` = linear extension of R with x' < y', consistent with L' on S'. Using the critical pair structure:
- `critical_down` ensures all a < x' in P satisfy R a y' → any order that places x' after all strict predecessors and before y' is consistent with R
- `critical_up` symmetrically for y'

The construction uses `add_minimal_to_linear_extension` (already proved in Theorems.v) applied to the pair (x', y') in a specific sequence: first insert y' using L' as base, then insert x' below y'.

Then obtain `L_extra` from `szpilrajn_theorem` applied to R extended with the pair (y', x'): this linear extension reverses x' and y'.

The union `{L̃' | L' ∈ r'} ∪ {L_extra}` has size ≤ d' + 1 (the {L̃'} set has size ≤ d' by cardinal_image_le; adding L_extra increases by at most 1).

**Why it realizes R:**
- Incomparable pair (a, b) with a, b ∈ S': some L' ∈ r' separates them; L̃' agrees with L' on S' ✓
- Any pair involving x' or y': either the L̃' extensions handle it (all put x' < y') or L_extra handles it (puts y' < x' and separates remaining pairs by extending R) ✓

**Step 5 — arithmetic.**
```
d ≤ d' + 1 ≤ (n−2)/2 + 1 = n/2
```
The last equality: `(n−2)/2 + 1 = n/2` holds for all n ≥ 2 in Nat integer division. Proved by `lia` or case split on parity.

---

## Summary of new helpers (all locations)

| Helper | Location | Used by |
|--------|----------|---------|
| `cardinal_image_le` | Theorems.v (or shared Helpers.v) | subposet_dimension_le |
| `exists_maximal` | CriticalPairs.v | incomparable_lifting |
| `cardinal_pos_nonempty` | LinearSum.v | linear_sum_realizer_lifting, product_realizer_exists |
| `cardinal_to_list` | LinearSum.v | linear_sum_realizer_lifting (cardinality) |
| `combine_extensions_injective` | LinearSum.v | linear_sum_realizer_lifting (injectivity) |
| `nth_nodup_inj` | LinearSum.v | linear_sum_realizer_lifting (injectivity) |
| `cardinal_Im_injective` | LinearSum.v | linear_sum_realizer_lifting (cardinality) |
| `cardinal_union_le` | ProductDimension.v | product_realizer_exists |
| `exists_minimal` (re-proved) | CriticalPairs.v | incomparable_lifting |
| `cardinal_to_finite` | Theorems.v | hiraguchi_bound |
| `singleton_cardinal` | Theorems.v | hiraguchi_bound chain case |
| `cardinal_subtract` | Theorems.v | hiraguchi_bound subposet |
| `extension_through_critical_pair` | Theorems.v | hiraguchi_bound incomparable case |

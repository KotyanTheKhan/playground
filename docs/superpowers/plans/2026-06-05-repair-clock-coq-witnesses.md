# Repair-Clock Coq Witnesses — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking. This is research-grade Coq — also consult superpowers:long-running-formalization (decomposition-first, admit-soundness, proof-of-concept before scaling) and use the `rocq_query`/`rocq_check` MCP tools to probe lemma names and types live.

**Goal:** Machine-check, admit-free, that the 2-coordinate clock characterizes happened-before on a minimal fully-synced pairwise execution and on a crown's one-sync repair — i.e. `dim ≤ 2` for the real nomadim PG posets `W_block` (5 events) and `W_repair` (19 events), with `W_crown` (16 events) defined and its `dim 3` narrated via the existing `crown3_dim_ge_3` + z3.

**Architecture:** Represent each witness as a raw finite poset (`Fin.t n` + a boolean order table = reflexive-transitive closure of the PG edges). One reusable bridge lemma turns two nat-valued key functions (the z3 realizer ranks) into `PosetDimension ≤ 2`, with the realizer obligations discharged by a tiny `Fin.t` `forallb` reflection + `vm_compute` (a bounded linear table eval — NOT the exponential pattern-enumeration that caused past blowups). A Python generator emits the Coq data tables from the validated harness so nothing is hand-transcribed.

**Tech Stack:** Coq/Rocq (the project's dune build via `bash .claude/scripts/timed-build.sh`), `posets/dimension` (`PosetDimension`, `IsRealizer`, `IsLinearExtension`), `FrontierCompose.crown3_dim_ge_3`, Python 3 (the `nomadim/data/frontier-sync` harness: `pg_of`, `extract_realizer`).

**Spec:** `docs/superpowers/specs/2026-06-05-repair-clock-coq-witnesses-design.md`. Read §1 (bridge), §2 (witnesses), §4 (build/admit-free) first.

**Build rule (MANDATORY):** never call dune/coqc directly. Every build:
`bash .claude/scripts/timed-build.sh <seconds> <target.vo> 1` (use `-j1`; these files do `vm_compute`). On timeout (exit 124) or memory kill (137), split the file / shrink the computation — do not just retry.

---

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/data/frontier-sync/emit_coq_witness.py` | Generator: emit `WitnessData.v` (edge tables + key functions) from `pg_of`/`extract_realizer`; self-check each emitted realizer with `clock_is_exact` before writing. |
| `execution_clock/witnesses/FinPosetBool.v` | `forallb_finT` reflection helper; the reusable bridge `realizer_keys_dim_le2`; proof-of-concept on a 4-element 2-chain. |
| `execution_clock/witnesses/WitnessData.v` | Generated: `Fin.t`-indexed boolean order tables `Rb_block`/`Rb_repair`/`Rb_crown` and key functions `k1_block,k2_block,k1_repair,k2_repair`. |
| `execution_clock/witnesses/BlockDim2.v` | `W_block` poset + `block_dim_eq_2`. |
| `execution_clock/witnesses/RepairDim2.v` | `W_repair` poset + `repair_dim_le_2`; `W_crown` definition + crown narrative. |

All under a new `execution_clock/witnesses/` dir, mapped into the existing `-R execution_clock ExecClock` library (no new `_CoqProject` stanza needed beyond listing the files; Task 6 wires them in).

**Concrete witness data (already extracted & z3-verified — do not recompute by hand):**
- `W_block`: N=2, syncs `[(0,1)]`, `nv=5`, edges `[(0,2),(1,2),(2,3),(2,4)]`, `key1=[1,0,2,3,4]`, `key2=[0,1,2,4,3]`. Incomparable pair: events `3` and `4` (the two post-sync heads).
- `W_repair`: N=4, syncs `[(0,1),(2,3),(0,3),(0,2),(1,3)]`, `nv=19`, edges `[(0,4),(1,4),(4,5),(4,6),(2,7),(3,7),(7,8),(7,9),(5,10),(9,10),(10,11),(10,12),(11,13),(8,13),(13,14),(13,15),(6,16),(12,16),(16,17),(16,18)]`, `key1=[6,5,0,1,7,8,15,2,3,4,9,10,14,11,12,13,16,17,18]`, `key2=[0,1,6,5,2,4,3,7,15,8,9,14,10,16,18,17,11,13,12]`.
- `W_crown`: N=4, syncs `[(0,1),(2,3),(0,2),(1,3)]` (= `W_repair` minus the inserted `(0,3)` sync), `nv=16`. dim 3 by z3 (not proven in Coq).

---

## Task 1: Generator script for the Coq data tables

**Files:**
- Create: `nomadim/data/frontier-sync/emit_coq_witness.py`

- [ ] **Step 1: Write the generator**

```python
#!/usr/bin/env python3
"""Emit WitnessData.v: Coq boolean order tables + nat key functions for the
repair-clock witnesses, from the validated harness. Each realizer is self-checked
with clock_is_exact before emission so the Coq data cannot drift from the z3 result.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import pg_of, extract_realizer, reachable_closure, clock_of, clock_is_exact

WITNESSES = {
    "block":  (2, [(0, 1)]),
    "repair": (4, [(0, 1), (2, 3), (0, 3), (0, 2), (1, 3)]),
    "crown":  (4, [(0, 1), (2, 3), (0, 2)]),  # placeholder; real crown set below
}
WITNESSES["crown"] = (4, [(0, 1), (2, 3), (0, 2), (1, 3)])


def reach_le(n, syncs):
    nv, edges = pg_of(n, syncs)
    reach = reachable_closure(nv, edges)
    def le(x, y):
        return x == y or y in reach[x]
    return nv, le


def emit_bool_table(name, nv, le):
    # Rb_<name> : Fin.t nv -> Fin.t nv -> bool, as a nested match on fin_to_nat.
    lines = [f"Definition Rb_{name} (x y : Fin.t {nv}) : bool :="]
    lines.append(f"  match fin_to_nat x, fin_to_nat y with")
    for x in range(nv):
        for y in range(nv):
            if le(x, y):
                lines.append(f"  | {x}, {y} => true")
    lines.append("  | _, _ => false")
    lines.append("  end.")
    return "\n".join(lines)


def emit_keys(name, keys):
    out = []
    for ki, key in enumerate(keys, start=1):
        out.append(f"Definition k{ki}_{name} (x : Fin.t {len(key)}) : nat :=")
        out.append(f"  match fin_to_nat x with")
        for i, v in enumerate(key):
            out.append(f"  | {i} => {v}")
        out.append("  | _ => 0")
        out.append("  end.")
    return "\n".join(out)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = os.path.normpath(os.path.join(here, "..", "..", "..",
            "execution_clock", "witnesses", "WitnessData.v"))
    blocks = []
    blocks.append("(* GENERATED by nomadim/data/frontier-sync/emit_coq_witness.py — do not edit. *)")
    blocks.append("From Stdlib Require Import Fin Arith.")
    blocks.append("Definition fin_to_nat {n} (x : Fin.t n) : nat := proj1_sig (Fin.to_nat x).")
    for name in ("block", "repair", "crown"):
        n, syncs = WITNESSES[name]
        nv, le = reach_le(n, syncs)
        blocks.append(f"(* {name}: N={n} syncs={syncs} nv={nv} *)")
        blocks.append(emit_bool_table(name, nv, le))
        if name != "crown":
            rz = extract_realizer(*pg_of(n, syncs))
            assert rz is not None, f"{name} not dim<=2!"
            ok, bad = clock_is_exact(*pg_of(n, syncs), clock_of(*pg_of(n, syncs)))
            assert ok, f"{name} realizer not exact: {bad}"
            blocks.append(emit_keys(name, list(rz)))
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        f.write("\n\n".join(blocks) + "\n")
    print("wrote", out)


if __name__ == "__main__":
    main()
```

- [ ] **Step 2: Run it and inspect**

Run: `cd nomadim/data/frontier-sync && python3 emit_coq_witness.py`
Expected: prints `wrote .../execution_clock/witnesses/WitnessData.v`. No `AssertionError` (the realizers are exact). Open the file and confirm it has `Rb_block`, `k1_block`, `k2_block`, `Rb_repair`, `k1_repair`, `k2_repair`, `Rb_crown`.

- [ ] **Step 3: Commit**

```bash
git add nomadim/data/frontier-sync/emit_coq_witness.py execution_clock/witnesses/WitnessData.v
git commit -m "feat(witness): generator emitting Coq order/key tables from the harness"
```

---

## Task 2: The reflection bridge `realizer_keys_dim_le2` (HIGH RISK — do this on a tiny poset first)

**Files:**
- Create: `execution_clock/witnesses/FinPosetBool.v`

This task is the crux. Build and prove everything against a TRIVIAL 4-element 2-chain poset (`0<1`, `2<3`) FIRST; only when that compiles admit-free do the witnesses (Tasks 4–5) reuse it. Use `rocq_query`/`rocq_check` to confirm exact lemma names (`IsRealizer`, `IsLinearExtension`, `IsTotalOrder`, `PosetDimension`, the finite-carrier dimension-existence lemma, `cardinal`, `card_add`, `card_empty`) — mirror how `execution/families/FrontierCompose.v` builds and discharges its realizer obligations and how `crown3_dim_exists` obtains `exists d, inhabited (PosetDimension ...)`.

- [ ] **Step 1: `forallb_finT` decidable-forall helper + spec**

Write, at the top of `FinPosetBool.v`:

```coq
From Stdlib Require Import Fin List Arith Lia Ensembles Finite_sets Constructive_sets Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
Import ListNotations.

(* all elements of Fin.t n *)
Fixpoint all_finT (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S m => Fin.F1 :: List.map (fun x => Fin.FS x) (all_finT m)
  end.

Lemma all_finT_complete : forall n (x : Fin.t n), List.In x (all_finT n).
Proof.
  induction n; intro x.
  - inversion x.
  - apply (Fin.caseS' x).
    + left; reflexivity.
    + intro p. right. apply List.in_map. apply IHn.
Qed.

Definition forallb_finT {n} (f : Fin.t n -> bool) : bool :=
  List.forallb f (all_finT n).

Lemma forallb_finT_spec {n} (f : Fin.t n -> bool) :
  forallb_finT f = true <-> forall x, f x = true.
Proof.
  unfold forallb_finT. rewrite List.forallb_forall. split.
  - intros H x. apply H. apply all_finT_complete.
  - intros H x _. apply H.
Qed.

Definition forallb_finT2 {n} (f : Fin.t n -> Fin.t n -> bool) : bool :=
  forallb_finT (fun x => forallb_finT (fun y => f x y)).

Lemma forallb_finT2_spec {n} (f : Fin.t n -> Fin.t n -> bool) :
  forallb_finT2 f = true <-> forall x y, f x y = true.
Proof.
  unfold forallb_finT2. rewrite forallb_finT_spec. split.
  - intros H x y. specialize (H x). rewrite forallb_finT_spec in H. apply H.
  - intros H x. apply forallb_finT_spec. intro y. apply H.
Qed.
```

- [ ] **Step 2: Build to verify the helper compiles**

Run: `bash .claude/scripts/timed-build.sh 120 execution_clock/witnesses/FinPosetBool.vo 1`
Expected: exit 0 (the file so far has only the helper; the rest follows). If `caseS'`/`in_map` names differ, fix via `rocq_query`.

- [ ] **Step 3: The bridge lemma**

Append to `FinPosetBool.v`. The order is `Rrel Rb x y := Rb x y = true`. Given key functions and the three reflected facts, produce `dim ≤ 2`:

```coq
Section Bridge.
  Context {n : nat} (Rb : Fin.t n -> Fin.t n -> bool)
          (k1 k2 : Fin.t n -> nat).
  Definition Rrel (x y : Fin.t n) : Prop := Rb x y = true.
  Definition Lk (k : Fin.t n -> nat) (x y : Fin.t n) : Prop := k x <= k y.

  Hypothesis HPoset : IsPoset (Fin.t n) Rrel.
  Hypothesis Hinj1 : forall x y, k1 x = k1 y -> x = y.
  Hypothesis Hinj2 : forall x y, k2 x = k2 y -> x = y.
  (* extends: R x y -> both keys agree *)
  Hypothesis Hext  : forall x y, Rb x y = true -> k1 x <= k1 y /\ k2 x <= k2 y.
  (* intersection closes: both keys agree -> R x y *)
  Hypothesis Hint  : forall x y, k1 x <= k1 y -> k2 x <= k2 y -> Rb x y = true.
  (* the two orders genuinely differ (so the realizer has cardinality 2) *)
  Hypothesis Hdiff : exists x y, k1 x <= k1 y /\ ~ (k2 x <= k2 y).

  (* Each Lk is a linear extension of Rrel. *)
  Lemma Lk_linext : forall k, (forall x y, k x = k y -> x = y) ->
                    (forall x y, Rb x y = true -> k x <= k y) ->
                    IsLinearExtension (R := Rrel) (Lk k).
  Proof.
    intros k Hinj Hkext. constructor.
    - constructor.
      + constructor. (* IsTotalOrder: refl/antisym/trans/total — match the actual field names via rocq_query *)
        * intro x. unfold Lk. lia.
        * intros x y Hxy Hyx. unfold Lk in *. apply Hinj. lia.
        * intros x y z Hxy Hyz. unfold Lk in *. lia.
      + intros x y. unfold Lk. lia. (* totality of nat <= *)
    - intros x y HR. unfold Lk. apply Hkext. exact HR.
  Qed.

  Definition realizer2 : Ensemble (Fin.t n -> Fin.t n -> Prop) :=
    fun L => L = Lk k1 \/ L = Lk k2.

  Lemma realizer2_isrealizer : IsRealizer (R := Rrel) realizer2.
  Proof.
    constructor.
    - intros L [-> | ->].
      + apply Lk_linext; [exact Hinj1 | intros x y H; apply Hext; exact H].
      + apply Lk_linext; [exact Hinj2 | intros x y H; apply Hext; exact H].
    - intros x y. split.
      + intros HR L [-> | ->]; apply Hext; exact HR.
      + intros Hall. apply Hint.
        * apply (Hall (Lk k1)); left; reflexivity.
        * apply (Hall (Lk k2)); right; reflexivity.
  Qed.

  Lemma realizer2_card2 : cardinal _ realizer2 2.
  Proof.
    (* {Lk k1, Lk k2} with Lk k1 <> Lk k2 (from Hdiff). Mirror crown3's card_add chain. *)
    assert (Hne : Lk k1 <> Lk k2).
    { destruct Hdiff as [x [y [H1 H2]]]. intro Heq.
      apply H2. rewrite <- Heq. exact H1. (* Lk k1 x y = Lk k2 x y by Heq *) }
    (* realizer2 = Add (Add Empty (Lk k1)) (Lk k2) — restate and use card_add. *)
    admit. (* TODO: replace with the explicit card_add chain, no axioms *)
  Admitted.

  Theorem realizer_keys_dim_le2 :
    exists d, inhabited (PosetDimension (A := Fin.t n) (R := Rrel) d) /\ d <= 2.
  Proof.
    (* finite carrier -> dimension exists; minimum <= card of realizer2 = 2 *)
    admit. (* TODO: obtain (exists d, inhabited (PosetDimension Rrel d)) like crown3_dim_exists,
              then dimension_is_minimum with realizer2_isrealizer + realizer2_card2 gives d <= 2 *)
  Admitted.
End Bridge.
```

NOTE: the two `admit`s above are PLACEHOLDERS to be eliminated in this same task — they are NOT acceptable in the committed result. Resolve `realizer2_card2` with the explicit `card_add`/`card_empty` chain (copy the shape from `crown3_dim_ge_3`'s `Three`/`card_add` block in `FrontierCompose.v`), and `realizer_keys_dim_le2` by obtaining dimension-existence for the finite `Fin.t n` carrier (mirror `crown3_dim_exists` in `FrontierCompose.v`) then `dimension_is_minimum`. Confirm the exact field names of `IsTotalOrder` with `rocq_query` and adjust the `constructor` block.

- [ ] **Step 4: Proof-of-concept on a 4-element 2-chain**

Append a self-test instantiating the bridge on `0<1`, `2<3`:

```coq
Module TwoChainPOC.
  Definition Rb4 (x y : Fin.t 4) : bool :=
    match proj1_sig (Fin.to_nat x), proj1_sig (Fin.to_nat y) with
    | 0,0|1,1|2,2|3,3|0,1|2,3 => true | _,_ => false end.
  Definition k1 (x : Fin.t 4) : nat :=
    match proj1_sig (Fin.to_nat x) with 0=>0|1=>1|2=>2|3=>3|_=>0 end.
  Definition k2 (x : Fin.t 4) : nat :=
    match proj1_sig (Fin.to_nat x) with 0=>2|1=>3|2=>0|3=>1|_=>0 end.
  (* discharge IsPoset Rrel, Hinj1/2, Hext, Hint, Hdiff by forallb_finT2_spec + vm_compute,
     then: *)
  Theorem poc_dim_le2 :
    exists d, inhabited (PosetDimension (A := Fin.t 4)
       (R := fun x y => Rb4 x y = true) d) /\ d <= 2.
  Proof. (* apply realizer_keys_dim_le2 with the discharged hypotheses *) Admitted.
End TwoChainPOC.
```

Replace the `Admitted` with a real proof. The reflected hypotheses (`Hinj`,`Hext`,`Hint`) are each `apply forallb_finT2_spec; vm_compute; reflexivity`-style. `IsPoset` for `Rrel` similarly. This POC is the gate: it must compile admit-free before proceeding.

- [ ] **Step 5: Build admit-free + check assumptions**

Run: `bash .claude/scripts/timed-build.sh 300 execution_clock/witnesses/FinPosetBool.vo 1`
Expected: exit 0. Then in `rocq_query`/a scratch: `Print Assumptions TwoChainPOC.poc_dim_le2.` — expected to list only standard classical axioms used by the dimension library (e.g. `classic`, `Extensionality_Ensembles`), and crucially **no `admit`/`Admitted` (no `False`-typed axiom)**. If any `admit` remains, the task is not done.

- [ ] **Step 6: Commit**

```bash
git add execution_clock/witnesses/FinPosetBool.v
git commit -m "feat(witness): Fin.t forallb reflection + realizer_keys_dim_le2 bridge (POC: 2-chain dim<=2)"
```

---

## Task 3: Wire `WitnessData.v` into the build

**Files:**
- Modify: `_CoqProject` (add the four witness files)
- Modify: `execution_clock/dune` if needed (the library likely globs; verify)

- [ ] **Step 1: Add the witness files to `_CoqProject`**

After the existing `execution_clock/...` lines (around line 138), add:

```
execution_clock/witnesses/FinPosetBool.v
execution_clock/witnesses/WitnessData.v
execution_clock/witnesses/BlockDim2.v
execution_clock/witnesses/RepairDim2.v
```

- [ ] **Step 2: Build WitnessData alone (it is just Definitions — must typecheck)**

Run: `bash .claude/scripts/timed-build.sh 120 execution_clock/witnesses/WitnessData.vo 1`
Expected: exit 0. If `Fin`/`proj1_sig` names mismatch the generator output, fix the generator (Task 1) and re-emit, then rebuild. (`fin_to_nat` is defined inside `WitnessData.v` itself.)

- [ ] **Step 3: Commit**

```bash
git add _CoqProject execution_clock/dune
git commit -m "build(witness): register witness files in _CoqProject"
```

---

## Task 4: `BlockDim2.v` — the minimal block has dimension 2

**Files:**
- Create: `execution_clock/witnesses/BlockDim2.v`

- [ ] **Step 1: Instantiate the bridge for `W_block`**

```coq
From Stdlib Require Import Fin Arith Lia.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From ExecClock Require Import witnesses.FinPosetBool witnesses.WitnessData.

(* IsPoset for Rb_block via reflection *)
Lemma block_isposet : IsPoset (Fin.t 5) (fun x y => Rb_block x y = true).
Proof.
  constructor.
  - intro x. (* reflexivity: forallb_finT (fun x => Rb_block x x) = true *)
    revert x; apply forallb_finT_spec; vm_compute; reflexivity.
  - intros x y Hxy Hyx. (* antisym *)
    revert x y Hxy Hyx;
    (* turn into a boolean check: forall x y, Rb x y && Rb y x ==> x =? y, by reflection *)
    admit.
  - intros x y z Hxy Hyz. (* trans, reflected *) admit.
Admitted.
```

The antisym/trans reflections need an equality-of-`Fin.t` decision. Resolve both `admit`s using `forallb_finT2`-style boolean checks plus `Fin.eqb`/`Fin.eq_dec` (confirm name via `rocq_query`). This is the same reflection idiom as the POC's `IsPoset`; copy it. Do not leave `admit`.

- [ ] **Step 2: Conclude `dim = 2`**

```coq
Theorem block_dim_le_2 :
  exists d, inhabited (PosetDimension (A := Fin.t 5)
     (R := fun x y => Rb_block x y = true) d) /\ d <= 2.
Proof.
  apply (realizer_keys_dim_le2 Rb_block k1_block k2_block).
  - exact block_isposet.
  - (* Hinj1 *) apply ...reflection on k1_block...
  - (* Hinj2 *) ...
  - (* Hext  *) apply forallb_finT2_spec-backed vm_compute...
  - (* Hint  *) ...
  - (* Hdiff *) exists (events 3 and 4); vm_compute; lia.
Qed.

(* dim >= 2: events 3 and 4 (the post-sync heads) are incomparable *)
Theorem block_dim_ge_2 :
  forall d, inhabited (PosetDimension (A := Fin.t 5)
     (R := fun x y => Rb_block x y = true) d) -> 2 <= d.
Proof.
  (* one incomparable pair forces dim >= 2; mirror the >=2 argument used in the
     dimension library (a single chain has dim 1, an incomparable pair forces 2).
     If a ready lemma `dim_ge_2_of_incomparable` exists (DimBridge), adapt it;
     otherwise prove directly: a 1-element realizer is a single total order, which
     would order the incomparable pair, contradiction. *) admit.
Admitted.
```

Resolve `block_dim_ge_2` (no admit): the incomparable pair is `Fin.t 5` events `3` and `4` (`Rb_block 3 4 = false` and `Rb_block 4 3 = false`, by `vm_compute`). Use the dimension library's incomparable→dim≥2 fact (find via `rocq_query` for `dim_ge_2`/`Incomparable`); if none is directly reusable, a single total order realizer must relate every pair, contradicting incomparability.

- [ ] **Step 3: Build admit-free + assumptions**

Run: `bash .claude/scripts/timed-build.sh 300 execution_clock/witnesses/BlockDim2.vo 1`
Expected: exit 0. `Print Assumptions block_dim_le_2.` → only classical axioms, no `admit`.

- [ ] **Step 4: Commit**

```bash
git add execution_clock/witnesses/BlockDim2.v
git commit -m "feat(witness): minimal fully-synced block has dimension 2 (2-coordinate clock)"
```

---

## Task 5: `RepairDim2.v` — the crown's one-sync repair has dimension ≤ 2

**Files:**
- Create: `execution_clock/witnesses/RepairDim2.v`

- [ ] **Step 1: `IsPoset` + `dim ≤ 2` for `W_repair`** (identical structure to Task 4, with `Rb_repair`, `k1_repair`, `k2_repair`, `Fin.t 19`)

```coq
From Stdlib Require Import Fin Arith Lia.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From ExecClock Require Import witnesses.FinPosetBool witnesses.WitnessData.

Lemma repair_isposet : IsPoset (Fin.t 19) (fun x y => Rb_repair x y = true).
Proof. (* same reflection idiom as block_isposet, now over Fin.t 19 *) Admitted.

Theorem repair_dim_le_2 :
  exists d, inhabited (PosetDimension (A := Fin.t 19)
     (R := fun x y => Rb_repair x y = true) d) /\ d <= 2.
Proof.
  apply (realizer_keys_dim_le2 Rb_repair k1_repair k2_repair).
  (* discharge HPoset/Hinj1/Hinj2/Hext/Hint/Hdiff by the same reflection tactics *)
Admitted.
```

Resolve both `Admitted` (no admit in the committed file). The only difference from Task 4 is size (19 vs 5): the `vm_compute` table evals are `19²`/`19³` — milliseconds. If a single `vm_compute` is slow or the proof term is large, switch that obligation to `vm_compute; reflexivity` inside `forallb_finT2_spec` (reflection keeps the term small). If Qed exceeds the 300s cap, raise to 600 with `-j1` and justify; if still failing, split each obligation into its own `Lemma` (one per hypothesis) so each Qed is independent.

- [ ] **Step 2: Define `W_crown` and narrate its dim 3 (no admit, no proof obligation)**

```coq
(* W_crown = W_repair minus the inserted repairing sync (0,3).
   Its PG poset is Rb_crown : Fin.t 16. By the z3 oracle (see
   nomadim/data/frontier-sync/CLOCK_RESULTS.md) it has dimension 3 — so NO
   2-coordinate clock characterises its happened-before. We do not prove dim>=3
   here (concrete PG crowns contain no induced crown3; the alternating-cycle
   certificate is deferred). The *obstruction type* is the abstract 3-crown,
   already proven dimension >= 3 as FrontierCompose.crown3_dim_ge_3. *)
From Dimension Require Import (* nothing new *) .
Definition W_crown_order (x y : Fin.t 16) : Prop := Rb_crown x y = true.
(* Sanity: W_crown is W_repair with the (0,3) sync removed — recorded as a comment;
   the two share their first two and last two syncs. *)
```

Add a `Lemma crown_obstruction_is_crown3 : True.` placeholder ONLY if you want a build anchor — otherwise the `Definition` + comment suffices. Do NOT add an `Admitted` dim≥3 lemma (that would be a false-ish open obligation the spec explicitly excludes).

- [ ] **Step 3: Build admit-free + assumptions**

Run: `bash .claude/scripts/timed-build.sh 600 execution_clock/witnesses/RepairDim2.vo 1`
Expected: exit 0 (allow up to 600s for the 19-element reflection; if it times out, split per Step 1's guidance). `Print Assumptions repair_dim_le_2.` → only classical axioms, no `admit`.

- [ ] **Step 4: Commit**

```bash
git add execution_clock/witnesses/RepairDim2.v
git commit -m "feat(witness): crown's one-sync repair has dim<=2; W_crown defined (dim3 by z3)"
```

---

## Task 6: Whole-project build, assumptions report, results note

**Files:**
- Create: `execution_clock/witnesses/README.md`
- Modify: `docs/INDEX.md` (add the witness theorems)

- [ ] **Step 1: Whole-project build (catch cross-module breakage)**

Run: `bash .claude/scripts/timed-build.sh 1800 @all 4`
Expected: exit 0. If a cross-import breaks, fix imports; if a witness file OOMs at `-j4`, the per-file builds already passed at `-j1` — rerun `@all` at `-j2`.

- [ ] **Step 2: Record the assumption audit**

In a scratch Coq session (or via `rocq_query`), run and capture:
`Print Assumptions block_dim_le_2.` `Print Assumptions block_dim_ge_2.` `Print Assumptions repair_dim_le_2.`
Confirm each lists only classical axioms (no `admit`, no `False` axiom).

- [ ] **Step 3: Write `execution_clock/witnesses/README.md`**

Record: what each witness is (the exact sync lists + vertex counts), the theorems (`block_dim_le_2`, `block_dim_ge_2`, `repair_dim_le_2`, and the `W_crown` definition), the `Print Assumptions` output from Step 2, the explicit scope note (positive dim-2 side proven; concrete crown dim≥3 deferred, obstruction = abstract `crown3_dim_ge_3`), and a pointer to the spec and `CLOCK_RESULTS.md`.

- [ ] **Step 4: Update `docs/INDEX.md`**

Add entries for `FinPosetBool.realizer_keys_dim_le2`, `BlockDim2.block_dim_le_2`/`block_dim_ge_2`, `RepairDim2.repair_dim_le_2` under a "Repair-clock witnesses" heading.

- [ ] **Step 5: Commit**

```bash
git add execution_clock/witnesses/README.md docs/INDEX.md
git commit -m "docs(witness): assumptions audit + index for the repair-clock Coq witnesses"
```

---

## Self-review notes (for the implementer)

- **Spec coverage:** §1 bridge → Task 2; §2 W_block → Task 4, W_repair/W_crown → Task 5; §3 files → Tasks 1–5; §4 build/admit-free → every build step + Task 6 audit. All covered.
- **The one make-or-break is Task 2.** If the `IsTotalOrder`/`IsRealizer`/`PosetDimension` plumbing or the finite-dimension-existence step resists, STOP and report (do not thrash): the fallback is to hand-prove `W_block` (5 events) directly in the `DimExampleN3` ExecPoset style and re-scope `W_repair`. Surface this to the controller rather than leaving admits.
- **Admits are temporary scaffolding only.** Several skeletons above contain `admit`/`Admitted` as labelled placeholders to be eliminated within the same task. No committed `.vo` may depend on an axiom of type `False`/`admit` — every task's final build step checks `Print Assumptions`.
- **Type consistency:** the bridge is `realizer_keys_dim_le2 (Rb) (k1) (k2)` returning `exists d, inhabited (PosetDimension ... d) /\ d <= 2`; Tasks 4/5 apply it with `Rb_block/k1_block/k2_block` (Fin.t 5) and `Rb_repair/k1_repair/k2_repair` (Fin.t 19). `forallb_finT2_spec` is the shared reflection lemma. `fin_to_nat` is defined in `WitnessData.v`; `FinPosetBool.v` uses `Fin.to_nat` directly.
- **vm_compute safety:** every reflective discharge is a fixed table eval (`≤ 19³` operations). This is categorically different from the exponential pattern-enumeration that caused past OOMs — do not confuse the two, but still build every file at `-j1` with a timeout.
- **Searching first:** before writing the dim≥2 (Task 4) and dimension-existence (Task 2) steps, use `searching-existing-formalizations` / `rocq_query` to find `dim_ge_2_of_incomparable`, the finite-carrier `dimension_exists`, and `IsTotalOrder`'s field names — they exist in the dimension library and `FrontierCompose.v` already uses them.
```

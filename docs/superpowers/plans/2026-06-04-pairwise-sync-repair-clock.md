# Pairwise-Sync Repair-Clock — Validation Harness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a Python harness that constructs the 2-coordinate logical clock (the extracted 2-realizer) for pairwise-sync executions of the form `block A ; repairing-sync connector ; block B`, and empirically validates — against nomadim's poset + z3 oracle — that the clock is exact on threshold/fan-repaired compositions and fails exactly on crowns, for N=4 and N=5..8.

**Architecture:** Three small Python modules in `nomadim/data/frontier-sync/`, reusing the existing `confirm_dim.py` (z3 SMT) and `hunt_n7.py` (`PG` event model). `clock_realizer.py` extracts a 2-realizer from the z3 model and turns it into a clock; `clock_fan.py` decomposes a frontier matching into the repairing-sync fan; `clock_compose.py` builds `A;connector;B` executions and runs the four exactness assertions over the stored corpus. Tests are plain-python assertion files (no pytest in env), run with `python3`.

**Tech Stack:** Python 3 (`/usr/local/bin/python3`), z3 (`/opt/homebrew/bin/z3`, via stdin), existing `confirm_dim.build_smt` / `reachable_closure`, `hunt_n7.PG`. Nomadim binary at `nomadim/build/nomadim` (already built).

**Reference spec:** `docs/superpowers/specs/2026-06-04-pairwise-sync-repair-clock-design.md`. Read §1 (model), §3 (realizer extraction), §4 (connector), §7 (assertions) before starting.

---

## File structure (decomposition)

| File | Responsibility |
|------|----------------|
| `nomadim/data/frontier-sync/clock_realizer.py` | Extract an exact 2-realizer `(L₁,L₂)` from the z3 model for a poset `(nv, edges)`; build `clock[v]=(rankL₁,rankL₂)`; verify `clock(x)≤clock(y) ⟺ y∈reach[x]∪{x}`. The core construction + exactness check. |
| `nomadim/data/frontier-sync/clock_fan.py` | Pure combinatorics: permutation → cycle decomposition → fan of repairing syncs (`N − #cycles` total); `compose_with_connector(A_syncs, B_syncs, perm)`. |
| `nomadim/data/frontier-sync/clock_compose.py` | Load the N=4 blocks, build `A;connector;B` executions, run the four §7 assertions over the corpus; CLI entry that prints a results table. |
| `nomadim/data/frontier-sync/test_clock_realizer.py` | Tests for `clock_realizer.py`. |
| `nomadim/data/frontier-sync/test_clock_fan.py` | Tests for `clock_fan.py`. |
| `nomadim/data/frontier-sync/CLOCK_RESULTS.md` | Final results note: the four assertions' outcomes across the corpus + N=5..8. |

All modules `sys.path.insert(0, dirname)` and import from `confirm_dim` / `hunt_n7`, matching the existing scripts' convention.

---

## Task 1: Realizer extraction from the z3 model

**Files:**
- Create: `nomadim/data/frontier-sync/clock_realizer.py`
- Test: `nomadim/data/frontier-sync/test_clock_realizer.py`

- [ ] **Step 1: Write the failing test**

Create `test_clock_realizer.py`:

```python
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import extract_realizer

def test_realizer_of_two_chains():
    # Two disjoint 2-chains: 0<1, 2<3. Dimension 2. Incomparable pairs:
    # {0,2},{0,3},{1,2},{1,3}. A 2-realizer must exist.
    nv, edges = 4, [(0, 1), (2, 3)]
    L1, L2 = extract_realizer(nv, edges)
    # Each Lk is a list giving each vertex's position (a permutation of 0..nv-1)
    assert sorted(L1) == [0, 1, 2, 3]
    assert sorted(L2) == [0, 1, 2, 3]
    # Both extensions must respect the edges (u before v)
    for (u, v) in edges:
        assert L1[u] < L1[v]
        assert L2[u] < L2[v]

def test_realizer_none_for_crown():
    # Standard 3-crown (S3): a_i < b_j for i != j. Dimension 3 -> no 2-realizer.
    # Vertices 0,1,2 = a0,a1,a2 ; 3,4,5 = b0,b1,b2. Edge a_i -> b_j when i != j.
    nv = 6
    edges = [(i, 3 + j) for i in range(3) for j in range(3) if i != j]
    assert extract_realizer(nv, edges) is None

if __name__ == "__main__":
    test_realizer_of_two_chains(); print("PASS two_chains")
    test_realizer_none_for_crown(); print("PASS crown_none")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: FAIL — `ModuleNotFoundError: No module named 'clock_realizer'`.

- [ ] **Step 3: Write minimal implementation**

Create `clock_realizer.py`:

```python
#!/usr/bin/env python3
"""Extract an exact 2-realizer (two linear extensions whose intersection is the
poset) from the z3 model, and turn it into the 2-coordinate clock. See spec
docs/superpowers/specs/2026-06-04-pairwise-sync-repair-clock-design.md S3/S7.
"""
import os, re, sys, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt


def extract_realizer(nv, edges):
    """Return (L1, L2) position lists if dim<=2, else None.
    L1[v], L2[v] are v's positions in the two linear extensions (a permutation).
    """
    reach = reachable_closure(nv, edges)
    smt = build_smt(nv, edges, reach, 2)
    # build_smt ends with (check-sat); append get-value for the position vars.
    getvals = "(get-value (" + " ".join(
        f"p{e}_{v}" for e in range(2) for v in range(nv)) + "))"
    r = subprocess.run(["z3", "-in"], input=smt + "\n" + getvals,
                       capture_output=True, text=True)
    lines = r.stdout.strip().splitlines()
    if not lines or lines[0] != "sat":
        return None
    model = " ".join(lines[1:])
    vals = dict((k, int(val)) for k, val in
                re.findall(r"\(p(\d+_\d+)\s+(-?\d+)\)", model))
    L1 = [vals[f"0_{v}"] for v in range(nv)]
    L2 = [vals[f"1_{v}"] for v in range(nv)]
    return L1, L2


if __name__ == "__main__":
    print(extract_realizer(4, [(0, 1), (2, 3)]))
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: `PASS two_chains` then `PASS crown_none`.

- [ ] **Step 5: Commit**

```bash
git add nomadim/data/frontier-sync/clock_realizer.py nomadim/data/frontier-sync/test_clock_realizer.py
git commit -m "feat(clock): extract exact 2-realizer from z3 model"
```

---

## Task 2: Clock from realizer + exactness verifier

**Files:**
- Modify: `nomadim/data/frontier-sync/clock_realizer.py` (add `clock_of` and `clock_is_exact`)
- Modify: `nomadim/data/frontier-sync/test_clock_realizer.py` (add tests)

- [ ] **Step 1: Write the failing test**

Append to `test_clock_realizer.py` (before the `__main__` block):

```python
from clock_realizer import clock_of, clock_is_exact

def test_clock_exact_two_chains():
    nv, edges = 4, [(0, 1), (2, 3)]
    clock = clock_of(nv, edges)            # dict v -> (c1, c2)
    assert clock is not None
    ok, bad = clock_is_exact(nv, edges, clock)
    assert ok, f"clock not exact: {bad}"

def test_clock_none_for_crown():
    nv = 6
    edges = [(i, 3 + j) for i in range(3) for j in range(3) if i != j]
    assert clock_of(nv, edges) is None     # dim 3 -> no 2-coord clock
```

And add the calls in `__main__`:

```python
    test_clock_exact_two_chains(); print("PASS clock_exact")
    test_clock_none_for_crown(); print("PASS clock_none")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: FAIL — `ImportError: cannot import name 'clock_of'`.

- [ ] **Step 3: Write minimal implementation**

Add to `clock_realizer.py` (above `__main__`):

```python
def clock_of(nv, edges):
    """The 2-coordinate clock: v -> (rank in L1, rank in L2). None if dim>2."""
    rz = extract_realizer(nv, edges)
    if rz is None:
        return None
    L1, L2 = rz
    return {v: (L1[v], L2[v]) for v in range(nv)}


def clock_is_exact(nv, edges, clock):
    """Check clock(x) <= clock(y) (componentwise) iff x ->hb y (reach+refl).
    Returns (True, None) or (False, (x, y, reason)) for the first violation.
    """
    reach = reachable_closure(nv, edges)
    def hb(x, y):
        return x == y or y in reach[x]
    for x in range(nv):
        cx = clock[x]
        for y in range(nv):
            cy = clock[y]
            le = cx[0] <= cy[0] and cx[1] <= cy[1]
            if le != hb(x, y):
                return False, (x, y, f"clock_le={le} hb={hb(x, y)}")
    return True, None
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: all four PASS lines.

- [ ] **Step 5: Commit**

```bash
git add nomadim/data/frontier-sync/clock_realizer.py nomadim/data/frontier-sync/test_clock_realizer.py
git commit -m "feat(clock): 2-coordinate clock from realizer + exactness verifier"
```

---

## Task 3: Fan connector from a frontier matching

**Files:**
- Create: `nomadim/data/frontier-sync/clock_fan.py`
- Test: `nomadim/data/frontier-sync/test_clock_fan.py`

- [ ] **Step 1: Write the failing test**

Create `test_clock_fan.py`:

```python
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_fan import cycles_of, fan_connector

def test_cycles_identity():
    assert sorted(map(sorted, cycles_of([0, 1, 2, 3]))) == [[0], [1], [2], [3]]

def test_cycles_swap():
    # swap channels 2 and 3: perm[2]=3, perm[3]=2
    cyc = cycles_of([0, 1, 3, 2])
    assert sorted(map(sorted, cyc)) == [[0], [1], [2, 3]]

def test_fan_identity_empty():
    # identity matching: no crossings -> empty (trivial) fan
    assert fan_connector([0, 1, 2, 3]) == []

def test_fan_swap_one_sync():
    # one transposition (2 3) -> exactly one repairing sync on the crossed pair
    assert fan_connector([0, 1, 3, 2]) == [(2, 3)]

def test_fan_3cycle_two_syncs():
    # 3-cycle (1 2 3): perm[1]=2, perm[2]=3, perm[3]=1 -> fan rooted at 1
    fan = fan_connector([0, 2, 3, 1])
    assert len(fan) == 2                       # N - #cycles = 4 - 2 = 2
    assert all(1 in s for s in fan)            # rooted at the cycle's min

if __name__ == "__main__":
    test_cycles_identity(); print("PASS cycles_identity")
    test_cycles_swap(); print("PASS cycles_swap")
    test_fan_identity_empty(); print("PASS fan_identity")
    test_fan_swap_one_sync(); print("PASS fan_swap")
    test_fan_3cycle_two_syncs(); print("PASS fan_3cycle")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_fan.py`
Expected: FAIL — `ModuleNotFoundError: No module named 'clock_fan'`.

- [ ] **Step 3: Write minimal implementation**

Create `clock_fan.py`:

```python
#!/usr/bin/env python3
"""Frontier matching -> repairing-sync fan connector. The matching is a
permutation perm (perm[i] = channel of A's output i wired to B's input). Its
cycle decomposition gives the fan: one repairing sync per transposition,
rooted at each cycle's minimum channel. Recovery length = N - #cycles
(see EXPLAINER_RESCUE.md). See spec S4/S6.
"""


def cycles_of(perm):
    """Cycle decomposition of perm (a list, perm[i] is the image of i)."""
    n = len(perm)
    seen = [False] * n
    cycles = []
    for i in range(n):
        if seen[i]:
            continue
        cyc, j = [], i
        while not seen[j]:
            seen[j] = True
            cyc.append(j)
            j = perm[j]
        cycles.append(cyc)
    return cycles


def fan_connector(perm):
    """List of repairing syncs (root, other) for each non-trivial cycle,
    rooted at the cycle's minimum. Length = sum(len(c)-1) = N - #cycles."""
    fan = []
    for cyc in cycles_of(perm):
        if len(cyc) <= 1:
            continue
        root = min(cyc)
        for c in cyc:
            if c != root:
                fan.append((root, c))
    return fan
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_fan.py`
Expected: all five PASS lines.

- [ ] **Step 5: Commit**

```bash
git add nomadim/data/frontier-sync/clock_fan.py nomadim/data/frontier-sync/test_clock_fan.py
git commit -m "feat(clock): fan connector from frontier matching (N - #cycles repairing syncs)"
```

---

## Task 4: Compose A ; connector ; B into one execution + its PG

**Files:**
- Modify: `nomadim/data/frontier-sync/clock_fan.py` (add `compose_with_connector`)
- Modify: `nomadim/data/frontier-sync/test_clock_fan.py` (add tests)

- [ ] **Step 1: Write the failing test**

Append to `test_clock_fan.py` before `__main__`:

```python
from clock_fan import compose_with_connector

def test_compose_direct_swap():
    # B1 star block; compose with itself, swap channels 2<->3, NO connector.
    A = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]
    perm = [0, 1, 3, 2]
    syncs = compose_with_connector(A, A, perm, use_connector=False)
    # A's 5 syncs, then B's 5 syncs relabeled by perm, no connector in between.
    assert syncs[:5] == A
    assert syncs[5:] == [(perm[i], perm[j]) for (i, j) in A]

def test_compose_with_fan_inserts_connector():
    A = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]
    perm = [0, 1, 3, 2]                        # swap 2<->3 -> fan [(2,3)]
    syncs = compose_with_connector(A, A, perm, use_connector=True)
    assert syncs[:5] == A
    assert syncs[5] == (2, 3)                  # the one repairing sync
    assert syncs[6:] == [(perm[i], perm[j]) for (i, j) in A]
```

And add to `__main__`:

```python
    test_compose_direct_swap(); print("PASS compose_direct")
    test_compose_with_fan_inserts_connector(); print("PASS compose_fan")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_fan.py`
Expected: FAIL — `ImportError: cannot import name 'compose_with_connector'`.

- [ ] **Step 3: Write minimal implementation**

Add to `clock_fan.py`:

```python
def compose_with_connector(a_syncs, b_syncs, perm, use_connector=True):
    """Build the composed sync list A ; [connector fan] ; relabel(B).
    perm relabels B's channels (the frontier matching). When use_connector,
    the repairing-sync fan for perm is inserted between A and B.
    """
    connector = fan_connector(perm) if use_connector else []
    relabelled_b = [(perm[i], perm[j]) for (i, j) in b_syncs]
    return list(a_syncs) + connector + relabelled_b
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_fan.py`
Expected: all seven PASS lines.

- [ ] **Step 5: Commit**

```bash
git add nomadim/data/frontier-sync/clock_fan.py nomadim/data/frontier-sync/test_clock_fan.py
git commit -m "feat(clock): compose A;connector;B sync list with frontier relabel"
```

---

## Task 5: End-to-end clock check on a composed execution

**Files:**
- Modify: `nomadim/data/frontier-sync/clock_realizer.py` (add `clock_check_syncs`)
- Modify: `nomadim/data/frontier-sync/test_clock_realizer.py` (add tests)

- [ ] **Step 1: Write the failing test**

Append to `test_clock_realizer.py` before `__main__`:

```python
import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from hunt_n7 import PG
from clock_fan import compose_with_connector
from clock_realizer import clock_check_syncs

B1 = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]

def test_single_block_exact():
    # A single dim-2 star block: clock exists and is exact.
    ok, dim = clock_check_syncs(4, B1)
    assert dim == 2 and ok is True

def test_crown_fails_at_two_coords():
    # B1 composed with itself, swap 2<->3, NO connector -> crown (dim 3).
    syncs = compose_with_connector(B1, B1, [0, 1, 3, 2], use_connector=False)
    ok, dim = clock_check_syncs(4, syncs)
    assert dim == 3            # no 2-coord clock exists
    assert ok is None          # clock_of returned None -> not exact, by absence

def test_fan_repair_exact_again():
    # Same crown, but with the (2,3) repairing connector -> dim 2, exact.
    syncs = compose_with_connector(B1, B1, [0, 1, 3, 2], use_connector=True)
    ok, dim = clock_check_syncs(4, syncs)
    assert dim == 2 and ok is True
```

And to `__main__`:

```python
    test_single_block_exact(); print("PASS single_block")
    test_crown_fails_at_two_coords(); print("PASS crown_fail")
    test_fan_repair_exact_again(); print("PASS fan_repair")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: FAIL — `ImportError: cannot import name 'clock_check_syncs'`.

- [ ] **Step 3: Write minimal implementation**

Add to `clock_realizer.py` (above `__main__`):

```python
from hunt_n7 import PG  # event-DAG model (mirrors process_graph.cpp)


def pg_of(n, syncs):
    """Build nomadim's event PG for a sync list; return (nv, edges)."""
    g = PG(n)
    for a, b in syncs:
        g.sync(a, b)
    return g.nv, g.edges


def clock_check_syncs(n, syncs):
    """Construct the clock for an execution and check exactness against its PG.
    Returns (exact, dim) where dim in {2, 3} (or higher).
    exact is True/False when a 2-clock exists; None when none exists (dim>2).
    """
    nv, edges = pg_of(n, syncs)
    clock = clock_of(nv, edges)
    if clock is None:
        # No 2-realizer: confirm the dimension for the report.
        from hunt_n7 import z3_dim, PG as _PG
        g = _PG(n)
        for a, b in syncs:
            g.sync(a, b)
        d = z3_dim(g)
        d = 3 if d == ">=4" else int(d)
        return None, d
    ok, _bad = clock_is_exact(nv, edges, clock)
    return ok, 2
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: all PASS lines including `single_block`, `crown_fail`, `fan_repair`.

- [ ] **Step 5: Commit**

```bash
git add nomadim/data/frontier-sync/clock_realizer.py nomadim/data/frontier-sync/test_clock_realizer.py
git commit -m "feat(clock): end-to-end clock construction + exactness check on a sync execution"
```

---

## Task 6: The four corpus assertions (N=4) + CLI

**Files:**
- Create: `nomadim/data/frontier-sync/clock_compose.py`
- Test: `nomadim/data/frontier-sync/test_clock_realizer.py` (one integration test)

- [ ] **Step 1: Write the failing test**

Append to `test_clock_realizer.py` before `__main__`:

```python
from clock_compose import load_blocks, assertion_a_single_blocks

def test_assertion_a_all_blocks_exact():
    blocks = load_blocks()
    assert len(blocks) == 10               # the 10 N=4 S=5 dim-2 blocks
    failures = assertion_a_single_blocks(blocks)
    assert failures == [], f"blocks not exact: {failures}"
```

And to `__main__`:

```python
    test_assertion_a_all_blocks_exact(); print("PASS assertion_a")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: FAIL — `ModuleNotFoundError: No module named 'clock_compose'`.

- [ ] **Step 3: Write minimal implementation**

Create `clock_compose.py`:

```python
#!/usr/bin/env python3
"""The four §7 exactness assertions over the N=4 corpus, plus a CLI report.

(a) the 10 single blocks                 -> clock exact at 2 coords
(b) threshold (non-crossing) compositions -> exact at 2 coords
(c) crown compositions (no connector)     -> NO 2-clock (dim 3)  [negative ctrl]
(d) fan-repaired compositions             -> exact at 2 coords again
"""
import os, sys, glob, re, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import clock_check_syncs
from clock_fan import compose_with_connector

HERE = os.path.dirname(os.path.abspath(__file__))


def load_blocks():
    """The 10 minimum dim-2 fully-synced N=4 blocks (S=5)."""
    blocks = []
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    for f in files:
        body = open(f).read().split("meta:")[0]
        syncs = [(int(a), int(b)) for a, b in
                 re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)]
        blocks.append((os.path.basename(f).replace(".yaml", ""), syncs))
    return blocks


def assertion_a_single_blocks(blocks):
    """Return list of (name) whose single-block clock is NOT exact at dim 2."""
    failures = []
    for name, syncs in blocks:
        ok, dim = clock_check_syncs(4, syncs)
        if not (dim == 2 and ok is True):
            failures.append((name, ok, dim))
    return failures


def assertion_cd_crown_and_repair(blocks, perms=None):
    """For each ordered block pair and each crossing perm, check:
    direct compose has no 2-clock (c) AND fan-repaired compose is exact (d).
    Returns (n_crowns, c_failures, d_failures)."""
    if perms is None:
        # the non-identity perms that actually cross (skip identity)
        perms = [list(p) for p in itertools.permutations(range(4))
                 if list(p) != [0, 1, 2, 3]]
    n_crowns, c_fail, d_fail = 0, [], []
    for (na, A) in blocks:
        for (nb, B) in blocks:
            for perm in perms:
                direct = compose_with_connector(A, B, perm, use_connector=False)
                ok_d, dim_d = clock_check_syncs(4, direct)
                if dim_d != 2:                       # a crown
                    n_crowns += 1
                    if ok_d is not None:             # (c) should have no clock
                        c_fail.append((na, nb, perm))
                    repaired = compose_with_connector(A, B, perm, True)
                    ok_r, dim_r = clock_check_syncs(4, repaired)
                    if not (dim_r == 2 and ok_r is True):   # (d)
                        d_fail.append((na, nb, perm, ok_r, dim_r))
    return n_crowns, c_fail, d_fail


def main():
    blocks = load_blocks()
    print(f"loaded {len(blocks)} blocks")
    fa = assertion_a_single_blocks(blocks)
    print(f"(a) single-block exact: {'PASS' if not fa else 'FAIL ' + str(fa)}")
    n_crowns, c_fail, d_fail = assertion_cd_crown_and_repair(blocks)
    print(f"(c) crowns found: {n_crowns}; "
          f"crown-has-no-2clock: {'PASS' if not c_fail else 'FAIL ' + str(c_fail)}")
    print(f"(d) fan-repaired exact: {'PASS' if not d_fail else 'FAIL ' + str(d_fail)}")


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_realizer.py`
Expected: all PASS lines including `assertion_a`.

- [ ] **Step 5: Commit**

```bash
git add nomadim/data/frontier-sync/clock_compose.py nomadim/data/frontier-sync/test_clock_realizer.py
git commit -m "feat(clock): N=4 corpus assertions (single block / crown / fan-repair)"
```

---

## Task 7: Run the full N=4 sweep and record results

**Files:**
- Create: `nomadim/data/frontier-sync/CLOCK_RESULTS.md`

- [ ] **Step 1: Run the full sweep**

Run: `cd nomadim/data/frontier-sync && python3 clock_compose.py`
Expected (the run takes a few minutes — 10×10×23 z3 calls): prints
```
loaded 10 blocks
(a) single-block exact: PASS
(c) crowns found: <a positive number>; crown-has-no-2clock: PASS
(d) fan-repaired exact: PASS
```
If `(a)` FAILs for any block, STOP — that means a single dim-2 block's
extracted 2-realizer disagrees with its PG `→hb`; investigate the PG vertex
mapping (spec §1) before continuing. If `(d)` FAILs, record which `(A,B,perm)`
and at what dimension the repair landed — that is itself a reportable finding
(the fan did not restore dim 2 for that case).

- [ ] **Step 2: Sanity-check the marquee witness against the stored YAML**

Run:
```bash
cd nomadim/data/frontier-sync && python3 -c "
import clock_realizer as C
# N4_connector1_rescue_dim2.yaml = B1 ; (1,2) ; relabelled B1
syncs=[(0,1),(0,2),(0,3),(0,2),(0,1),(1,2),(0,2),(0,1),(0,3),(0,1),(0,2)]
print('rescue check:', C.clock_check_syncs(4, syncs))
"
```
Expected: `rescue check: (True, 2)` — matching the YAML's `dimension: 2`.

- [ ] **Step 3: Write the results note**

Create `CLOCK_RESULTS.md` recording: the exact printed output of Step 1, the
marquee witness result from Step 2, the crown count, and a one-paragraph
statement of the four assertions' outcomes. Link back to the spec. Template:

```markdown
# 2-coordinate repair-clock — empirical results (N=4)

Harness: `clock_realizer.py`, `clock_fan.py`, `clock_compose.py`.
Spec: `../../docs/superpowers/specs/2026-06-04-pairwise-sync-repair-clock-design.md`.

## N=4 sweep (`python3 clock_compose.py`)

<paste exact output>

- (a) single block exact: <result>
- (c) crowns: <count>; every crown has NO 2-coordinate clock (dim 3): <result>
- (d) every crown is restored to an exact 2-coordinate clock by the
  `N − #cycles` fan connector: <result>

Marquee witness (`N4_connector1_rescue_dim2.yaml`,
B1 ; (1,2) ; B1'): clock_check_syncs -> <result>, matching stored dimension 2.

## Reading

The repairing-sync connector is exactly what buys back the second coordinate:
direct gluing crowns (dim 3, no 2-clock); the fan restores an exact 2-coordinate
clock. <one paragraph>.
```

- [ ] **Step 4: Commit**

```bash
git add nomadim/data/frontier-sync/CLOCK_RESULTS.md
git commit -m "docs(clock): N=4 empirical results — repair restores the 2-coordinate clock"
```

---

## Task 8: Generalize to N = 5..8 (the fan law, N-independence)

**Files:**
- Modify: `nomadim/data/frontier-sync/clock_compose.py` (add `assertion_anyN_fan`)
- Modify: `nomadim/data/frontier-sync/CLOCK_RESULTS.md` (append N=5..8 section)

- [ ] **Step 1: Write the failing test**

Append to `test_clock_fan.py` before `__main__`:

```python
from clock_compose import star_block, assertion_anyN_fan

def test_star_block_is_full_sync_dim2():
    # The star block for N: gather to hub 0, then scatter. Dim 2 for any N.
    import clock_realizer as C
    syncs = star_block(5)
    ok, dim = C.clock_check_syncs(5, syncs)
    assert dim == 2 and ok is True

def test_anyN_3cycle_needs_repair():
    # N=5, a 3-cycle matching: direct crowns, fan of 2 syncs repairs to dim 2.
    res = assertion_anyN_fan(5, perm=[0, 2, 3, 1, 4])
    assert res["direct_dim"] == 3
    assert res["repaired_ok"] is True and res["repaired_dim"] == 2
    assert res["fan_len"] == 2                 # N - #cycles for this perm
```

And to `__main__`:

```python
    test_star_block_is_full_sync_dim2(); print("PASS starN")
    test_anyN_3cycle_needs_repair(); print("PASS anyN_fan")
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_fan.py`
Expected: FAIL — `ImportError: cannot import name 'star_block'`.

- [ ] **Step 3: Write minimal implementation**

Add to `clock_compose.py`:

```python
def star_block(n):
    """Gather-then-scatter star on hub 0: a dim-2 fully-synced block for any N.
    (0,1)(0,2)...(0,n-1)(0,n-2)...(0,1) — fan in to hub, then fan back out."""
    gather = [(0, k) for k in range(1, n)]
    scatter = [(0, k) for k in range(n - 2, 0, -1)]
    return gather + scatter


def assertion_anyN_fan(n, perm):
    """Compose star_block(n) with itself under perm, with and without the fan.
    Returns dims + repaired exactness + fan length."""
    from clock_realizer import clock_check_syncs
    from clock_fan import compose_with_connector, fan_connector
    A = star_block(n)
    direct = compose_with_connector(A, A, perm, use_connector=False)
    ok_d, dim_d = clock_check_syncs(n, direct)
    repaired = compose_with_connector(A, A, perm, use_connector=True)
    ok_r, dim_r = clock_check_syncs(n, repaired)
    return {"direct_dim": dim_d, "repaired_ok": ok_r, "repaired_dim": dim_r,
            "fan_len": len(fan_connector(perm))}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cd nomadim/data/frontier-sync && python3 test_clock_fan.py`
Expected: all PASS lines including `starN`, `anyN_fan`.

- [ ] **Step 5: Run the N=5..8 cycle-type sweep**

Run:
```bash
cd nomadim/data/frontier-sync && python3 -c "
from clock_compose import assertion_anyN_fan
import itertools
def rot(n, d):            # a single d-cycle on channels 1..d, fixing the rest
    p=list(range(n))
    for k in range(1,d): p[k]=k+1
    p[d]=1
    return p
for n in (5,6,7,8):
    for d in range(2, n):
        r = assertion_anyN_fan(n, rot(n,d))
        print(f'N={n} d-cycle={d}: direct_dim={r[\"direct_dim\"]} '
              f'fan_len={r[\"fan_len\"]} repaired_dim={r[\"repaired_dim\"]} '
              f'ok={r[\"repaired_ok\"]}')
"
```
Expected: for every `N` and every cycle length `d`, `fan_len == d-1`,
`repaired_dim == 2`, `ok == True`; `direct_dim == 3` for `d >= 2`. N=8 is the
heaviest (z3 on ~50-vertex posets) — allow a few minutes; if a single z3 call
exceeds ~60s, note it and reduce to N≤7 for the recorded table.

- [ ] **Step 6: Append results + commit**

Append the Step-5 table and a one-line N-independence statement to
`CLOCK_RESULTS.md`, then:

```bash
git add nomadim/data/frontier-sync/clock_compose.py nomadim/data/frontier-sync/test_clock_fan.py nomadim/data/frontier-sync/CLOCK_RESULTS.md
git commit -m "feat(clock): any-N fan law validation (N=5..8) — repair length = N - #cycles"
```

---

## Self-review notes (for the implementer)

- **Spec coverage:** §1 model → `pg_of` (Task 5); §2 clock → `clock_of` (Task 2);
  §3 realizer extraction → Task 1; §4 connector/fan → Task 3–4; §5 N=4 → Task 6–7;
  §6 any-N → Task 8; §7 four assertions → Task 6 (a,c,d) and `assertion_*`.
  Assertion **(b)** (threshold/identity-matching exact) is the
  `use_connector=False, perm=identity` corner — add it explicitly to the Task-6
  CLI report if you want it itemized; it is implied by (a) extended over an
  identity compose and is cheap to print.
- **Type consistency:** `clock_check_syncs` returns `(exact, dim)` with
  `exact ∈ {True, False, None}` (None = no clock); every caller branches on
  exactly that. `clock_of` returns a `dict v->(c1,c2)` or `None`. `fan_connector`
  returns a list of `(a,b)` tuples. Keep these stable across tasks.
- **Performance guard:** every dimension decision is a z3 call. The Task-6 sweep
  is 10×10×23 ≈ 2300 compositions × up to 2 z3 calls — minutes, not seconds. If
  it drags, cache by the composed sync tuple, or restrict the perm set to the 5
  crown representatives from `COMPOSE_N4.md`. Do **not** add the heavy realizer
  enumeration — only `build_smt` at t=2/t=3 is needed.
- **PG mapping caveat (the one real risk):** the clock is checked against
  `PG.edges`/`reach`, i.e. nomadim's own event DAG — so exactness is genuine, not
  circular (the realizer comes from z3 on the same poset, but the `clock_is_exact`
  test independently recomputes `reach` and compares the componentwise clock test
  to it). If Task-7 Step-1 `(a)` fails, the culprit is almost certainly a stale
  `confirm_dim`/`PG` import path, not the math.
```

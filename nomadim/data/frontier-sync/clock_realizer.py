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
    first = lines[0] if lines else ""
    if first == "sat":
        pass  # fall through to model parsing
    elif first == "unsat":
        return None
    else:
        snippet = (r.stderr.strip() or r.stdout.strip())[:200]
        raise RuntimeError(
            f"z3 did not return sat/unsat (rc={r.returncode}): {snippet}")
    model = " ".join(lines[1:])
    vals = {k: int(val) for k, val in
            re.findall(r"\(p(\d+_\d+)\s+(-?\d+)\)", model)}
    L1 = [vals[f"0_{v}"] for v in range(nv)]
    L2 = [vals[f"1_{v}"] for v in range(nv)]
    return L1, L2


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


if __name__ == "__main__":
    result = extract_realizer(4, [(0, 1), (2, 3)])
    print(f"2-chain example realizer: {result}")

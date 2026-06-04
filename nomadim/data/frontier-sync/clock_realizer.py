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


if __name__ == "__main__":
    result = extract_realizer(4, [(0, 1), (2, 3)])
    print(f"2-chain example realizer: {result}")

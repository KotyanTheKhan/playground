#!/usr/bin/env python3
"""Decide `dimension <= t` for an execution poset, exactly, via z3 (SMT).

Dimension <= t  iff  there exist t linear extensions of the poset whose
intersection is the poset itself. We model each extension e as an integer
position vector pos[e][v] (a permutation), constrained to extend the DAG; the
intersection equals the poset iff every incomparable pair is "split" (ordered
one way in some extension and the other way in another). z3 SAT => dim <= t
(with a witness); z3 UNSAT => dim > t, a proof (no time-limited guessing).

Usage: confirm_dim.py <execution.yaml> <t>
"""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
NOMADIM = os.path.normpath(os.path.join(HERE, "..", "..", "build", "nomadim"))


def load_poset(exec_yaml):
    pos_yaml = exec_yaml + ".poset"
    subprocess.run([NOMADIM, "convert", exec_yaml, pos_yaml], check=True,
                   capture_output=True, text=True)
    txt = open(pos_yaml).read()
    os.remove(pos_yaml)
    n = int(re.search(r"n_vertices:\s*(\d+)", txt).group(1))
    edges = [(int(a), int(b)) for a, b in
             re.findall(r"-\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]", txt)]
    return n, edges


def reachable_closure(n, edges):
    # adjacency -> transitive reachability (Floyd-style on bitsets)
    reach = [set() for _ in range(n)]
    for u, v in edges:
        reach[u].add(v)
    changed = True
    while changed:
        changed = False
        for u in range(n):
            add = set()
            for w in list(reach[u]):
                add |= reach[w]
            if not add <= reach[u]:
                reach[u] |= add
                changed = True
    return reach


def build_smt(n, edges, reach, t):
    L = []
    for e in range(t):
        for v in range(n):
            L.append(f"(declare-const p{e}_{v} Int)")
    for e in range(t):
        # permutation of 0..n-1
        L.append("(assert (distinct " + " ".join(f"p{e}_{v}" for v in range(n)) + "))")
        for v in range(n):
            L.append(f"(assert (and (>= p{e}_{v} 0) (< p{e}_{v} {n})))")
        # extend the DAG (transitivity of < gives the full order)
        for (u, w) in edges:
            L.append(f"(assert (< p{e}_{u} p{e}_{w}))")
    # every incomparable pair must be split across the extensions
    for x in range(n):
        for y in range(x + 1, n):
            if y in reach[x] or x in reach[y]:
                continue  # comparable -> all extensions already agree
            lt = " ".join(f"(< p{e}_{x} p{e}_{y})" for e in range(t))
            gt = " ".join(f"(< p{e}_{y} p{e}_{x})" for e in range(t))
            L.append(f"(assert (or {lt}))")
            L.append(f"(assert (or {gt}))")
    L.append("(check-sat)")
    return "\n".join(L)


def decide(exec_yaml, t):
    n, edges = load_poset(exec_yaml)
    reach = reachable_closure(n, edges)
    smt = build_smt(n, edges, reach, t)
    r = subprocess.run(["z3", "-in"], input=smt, capture_output=True, text=True)
    out = r.stdout.strip().splitlines()[0] if r.stdout.strip() else r.stderr.strip()
    return n, out


if __name__ == "__main__":
    exec_yaml = sys.argv[1]
    t = int(sys.argv[2])
    n, verdict = decide(exec_yaml, t)
    concl = {"sat": f"dimension <= {t}", "unsat": f"dimension > {t}"}.get(verdict, verdict)
    print(f"{os.path.basename(exec_yaml)}: n={n}, t={t} -> {verdict}  ({concl})")

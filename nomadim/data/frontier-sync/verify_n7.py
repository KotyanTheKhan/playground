#!/usr/bin/env python3
"""Rigorous, independent double-check of the N=7 dimension results.

Layers of verification (each independent of the others):
  (1) model fidelity   -- the pure-Python execution expansion equals nomadim's
                          own `convert` output (edge sets identical);
  (2) oracle calibration -- the integer-position SMT model returns the correct
                          dimension on canonical posets of known dimension 1..5;
  (3) certificate check -- extract z3's witness (d linear extensions) and verify
                          INDEPENDENTLY (no solver trust) that they realize the
                          poset, proving dimension <= d;
  (4) second encoding  -- a structurally different SMT model (boolean precedence
                          with explicit transitivity) must agree on the t=3
                          UNSAT / t=4 SAT verdicts (the lower bound dim>3).

Run nomadim's own exact algorithm separately for the ultimate cross-check.
"""
import os, re, sys, subprocess, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import PG

NOMADIM = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                        "..", "..", "build", "nomadim"))


def z3run(smt, model=False):
    r = subprocess.run(["z3", "-in"], input=smt, capture_output=True, text=True)
    return r.stdout


# ---------- encoding A: integer positions (from confirm_dim.build_smt) ----------
def encA_sat(n, edges, reach, t, get_model=False):
    smt = build_smt(n, edges, reach, t)
    if get_model:
        smt += "\n(get-model)"
    out = z3run(smt)
    verdict = out.strip().split("\n")[0]
    return verdict, out


def extract_extensions(out, n, t):
    """Parse z3 integer model -> list of t linear orders (vertex sequences)."""
    pos = {}
    for e, v, val in re.findall(r"define-fun p(\d+)_(\d+) \(\) Int\s+\(?\s*(-?\d+)", out):
        pos[(int(e), int(v))] = int(val)
    exts = []
    for e in range(t):
        order = sorted(range(n), key=lambda v: pos[(e, v)])
        exts.append(order)
    return exts


# ---------- encoding B: boolean precedence with explicit transitivity ----------
def encB_sat(n, edges, reach, t):
    L = []
    def b(e, x, y):
        return f"b{e}_{x}_{y}"
    for e in range(t):
        for x in range(n):
            for y in range(n):
                if x != y:
                    L.append(f"(declare-const {b(e,x,y)} Bool)")
    for e in range(t):
        # total + antisymmetric
        for x in range(n):
            for y in range(x + 1, n):
                L.append(f"(assert (xor {b(e,x,y)} {b(e,y,x)}))")
        # transitive
        for x in range(n):
            for y in range(n):
                if y == x:
                    continue
                for z in range(n):
                    if z == x or z == y:
                        continue
                    L.append(f"(assert (=> (and {b(e,x,y)} {b(e,y,z)}) {b(e,x,z)}))")
        # extends the poset (covering edges; transitivity gives the closure)
        for (u, v) in edges:
            L.append(f"(assert {b(e,u,v)})")
    # every incomparable pair split
    for x in range(n):
        for y in range(x + 1, n):
            if y in reach[x] or x in reach[y]:
                continue
            L.append("(assert (or " + " ".join(b(e, x, y) for e in range(t)) + "))")
            L.append("(assert (or " + " ".join(b(e, y, x) for e in range(t)) + "))")
    L.append("(check-sat)")
    return z3run("\n".join(L)).strip().split("\n")[0]


# ---------- independent certificate verification ----------
def verify_realizer(n, reach, exts):
    """True iff the linear orders `exts` realize the poset given by `reach`
    (transitive closure). Pure check, independent of any solver."""
    # each ext must be a permutation
    for ext in exts:
        if sorted(ext) != list(range(n)):
            return False, "not a permutation"
    rank = [{v: i for i, v in enumerate(ext)} for ext in exts]
    # extends poset: u<v in poset => u before v in every ext
    for u in range(n):
        for v in reach[u]:
            if any(rk[u] > rk[v] for rk in rank):
                return False, f"ext violates poset relation {u}<{v}"
    # intersection == poset: incomparable pair must be split
    for x in range(n):
        for y in range(x + 1, n):
            comp = (y in reach[x]) or (x in reach[y])
            if comp:
                continue
            xy = any(rk[x] < rk[y] for rk in rank)
            yx = any(rk[y] < rk[x] for rk in rank)
            if not (xy and yx):
                return False, f"incomparable pair {x},{y} not split (intersection > poset)"
    return True, "valid realizer"


# ---------- helpers ----------
def py_edges(syncs, n):
    g = PG(n)
    for a, b in syncs:
        g.sync(a, b)
    return g


def nomadim_edges(syncs, n):
    tmp = "/tmp/fs/_verify.yaml"
    with open(tmp, "w") as f:
        f.write(f"execution:\n  n_procs: {n}\n  syncs:\n")
        for a, b in syncs:
            f.write(f"    - [{a}, {b}]\n")
    pos = tmp + ".poset"
    subprocess.run([NOMADIM, "convert", tmp, pos], check=True, capture_output=True)
    txt = open(pos).read()
    nv = int(re.search(r"n_vertices:\s*(\d+)", txt).group(1))
    edges = [(int(a), int(b)) for a, b in
             re.findall(r"-\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]", txt)]
    os.remove(tmp); os.remove(pos)
    return nv, edges


def load_syncs(path):
    txt = open(path).read()
    n = int(re.search(r"n_procs:\s*(\d+)", txt).group(1))
    syncs = [(int(a), int(b)) for a, b in
             re.findall(r"-\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]", txt.split("meta:")[0])]
    return n, syncs


def exact_dim(n, edges, reach, hi=6):
    for t in range(1, hi + 1):
        v, _ = encA_sat(n, edges, reach, t)
        if v == "sat":
            return t
    return f">{hi}"


# ---------- calibration on canonical posets ----------
def calibrate():
    print("(2) ORACLE CALIBRATION on posets of known dimension:")
    cases = []
    # chain 0<1<2<3 : dim 1
    cases.append(("chain-4 (dim 1)", 4, [(0, 1), (1, 2), (2, 3)], 1))
    # antichain of 5 : dim 2
    cases.append(("antichain-5 (dim 2)", 5, [], 2))
    for k, d in [(3, 3), (4, 4), (5, 5)]:
        edges = [(i, k + j) for i in range(k) for j in range(k) if i != j]
        cases.append((f"S_{k} (dim {d})", 2 * k, edges, d))
    ok = True
    for name, n, edges, expect in cases:
        reach = reachable_closure(n, edges)
        got = exact_dim(n, edges, reach, hi=expect + 2)
        flag = "OK" if got == expect else "*** MISMATCH ***"
        if got != expect:
            ok = False
        print(f"   {name:24s} z3 dim = {got}   {flag}")
    return ok


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    print("=" * 68)
    cal_ok = calibrate()
    print(f"   calibration {'PASSED' if cal_ok else 'FAILED'}")
    print("=" * 68)

    files = ["N7_S10_dim3_z3_01.yaml", "N7_S11_dim4_z3_01.yaml", "N7_S12_dim4_z3_01.yaml"]
    expected = {"N7_S10_dim3_z3_01.yaml": 3,
                "N7_S11_dim4_z3_01.yaml": 4,
                "N7_S12_dim4_z3_01.yaml": 4}
    for fn in files:
        path = os.path.join(here, fn)
        n, syncs = load_syncs(path)
        exp = expected[fn]
        print(f"\n### {fn}  (claimed dim {exp}, S={len(syncs)}) ###")

        # (1) model fidelity
        g = py_edges(syncs, n)
        nv2, e2 = nomadim_edges(syncs, n)
        same = (g.nv == nv2) and (set(g.edges) == set(e2))
        print(f" (1) model fidelity: python n={g.nv} edges={len(g.edges)} vs "
              f"nomadim n={nv2} edges={len(e2)} -> {'IDENTICAL' if same else '*** DIFFER ***'}")

        reach = reachable_closure(g.nv, g.edges)
        # full-sync sanity
        preds = [0] * g.nv; succ = [0] * g.nv
        for u, v in g.edges:
            succ[u] += 1; preds[v] += 1
        mins = [v for v in range(g.nv) if preds[v] == 0]
        maxs = [v for v in range(g.nv) if succ[v] == 0]
        fs = len(mins) == n and len(maxs) == n and all(M in reach[m] for m in mins for M in maxs)
        print(f"     full-sync: |minimals|={len(mins)} |maximals|={len(maxs)} "
              f"all min<max -> {fs}")

        # (3) encoding A exact dim + certificate for the SAT witness
        dimA = exact_dim(g.nv, g.edges, reach, hi=6)
        v_sat, out = encA_sat(g.nv, g.edges, reach, dimA, get_model=True)
        exts = extract_extensions(out, g.nv, dimA)
        cert_ok, msg = verify_realizer(g.nv, reach, exts)
        print(f" (3) encoding A: dim = {dimA};  {dimA}-extension certificate "
              f"verified -> {cert_ok} ({msg})  => dim <= {dimA}")

        # (4) second independent encoding: verdicts at t=dim-1 and t=dim
        vBm1 = encB_sat(g.nv, g.edges, reach, dimA - 1)
        vB = encB_sat(g.nv, g.edges, reach, dimA)
        agree = (vBm1 == "unsat") and (vB == "sat")
        print(f" (4) encoding B (independent): t={dimA-1} -> {vBm1}, t={dimA} -> {vB}"
              f"  => dim = {dimA}: {'CONFIRMED' if agree else '*** DISAGREE ***'}")

        verdict = "VERIFIED" if (same and fs and dimA == exp and cert_ok and agree) else "*** CHECK ***"
        print(f"  ==> dimension {dimA} {verdict} (expected {exp})")


if __name__ == "__main__":
    main()

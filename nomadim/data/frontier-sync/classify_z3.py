#!/usr/bin/env python3
"""Exact dimension distribution of a batch of executions, via the z3 SMT oracle
(see confirm_dim.py). For each shape: t=3 UNSAT => dimension >= 4 (printed
immediately); else t=2 decides dim 2 vs dim 3. Far faster and more reliable than
the brute-force colorer for the larger N=6+ posets.

Usage: classify_z3.py <multidoc-exec.yaml>
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import load_poset, reachable_closure, build_smt
import subprocess

NOMADIM_DIR = "/tmp/fs"


def z3_sat(n, edges, reach, t):
    smt = build_smt(n, edges, reach, t)
    r = subprocess.run(["z3", "-in"], input=smt, capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0]


def main(infile):
    docs = [d for d in open(infile).read().split("---") if "execution" in d]
    tally = collections.Counter()
    hi = []
    for i, d in enumerate(docs):
        syncs = re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", d.split("meta:")[0])
        nproc = re.search(r"n_procs:\s*(\d+)", d).group(1)
        tmp = f"{NOMADIM_DIR}/_z{i}.yaml"
        with open(tmp, "w") as f:
            f.write(f"execution:\n  n_procs: {nproc}\n  syncs:\n")
            for a, b in syncs:
                f.write(f"    - [{a}, {b}]\n")
        n, edges = load_poset(tmp)
        reach = reachable_closure(n, edges)
        os.remove(tmp)
        if z3_sat(n, edges, reach, 3) == "unsat":
            dim = ">=4"
            hi.append(syncs)
        elif z3_sat(n, edges, reach, 2) == "sat":
            dim = 2
        else:
            dim = 3
        tally[dim] += 1
        if (i + 1) % 25 == 0:
            print(f"  ...{i+1}/{len(docs)}  {dict(tally)}", flush=True)
    print(f"\nExact dimensions of {len(docs)} shapes (z3):")
    for k in sorted(tally, key=str):
        print(f"  dim {k}: {tally[k]}")
    if hi:
        print(f"\n*** DIMENSION >= 4 FOUND ({len(hi)}): ***")
        for s in hi:
            print("  " + " ".join(f"({a},{b})" for a, b in s))
    else:
        print("\nNo dimension >= 4 in this batch.")


if __name__ == "__main__":
    main(sys.argv[1])

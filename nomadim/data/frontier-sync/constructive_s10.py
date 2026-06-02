#!/usr/bin/env python3
"""Does a dimension-4 N=7 execution exist at the gossip MINIMUM S = 10?

We generate genuine optimal (S = 2N-4 = 10) gossip schemes constructively and
diversely: pick 4 of the 7 processes as a "core"; each of the 3 extras deposits
into a random core node (3 syncs); the core runs a random 4-call cross-exchange
so all 4 know everything (4 syncs); each extra is then called back by a random
core node (3 syncs). Every such scheme is fully synchronized at exactly S = 10.
We z3-classify each. A single dim-4 here => the minimum S for an N=7 dimension-4
execution is the gossip minimum 10; otherwise (large diverse all-<=3 sample) the
minimum is most likely 11 (where dim 4 is already confirmed).

Usage: constructive_s10.py [n_samples]
"""
import os, sys, random, itertools, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from min_s_dim4 import G, N, FULL

CROSSES = [
    lambda c: [(c[0], c[1]), (c[2], c[3]), (c[0], c[2]), (c[1], c[3])],
    lambda c: [(c[0], c[1]), (c[2], c[3]), (c[0], c[3]), (c[1], c[2])],
    lambda c: [(c[0], c[2]), (c[1], c[3]), (c[0], c[1]), (c[2], c[3])],
    lambda c: [(c[0], c[1]), (c[2], c[3]), (c[1], c[3]), (c[0], c[2])],
]


def make_scheme(rng):
    procs = list(range(N))
    rng.shuffle(procs)
    core, extras = procs[:4], procs[4:]
    rng.shuffle(core)
    fan_in = [(e, rng.choice(core)) for e in extras]
    cross = rng.choice(CROSSES)(core)
    fan_out = [(rng.choice(core), e) for e in extras]
    return fan_in + cross + fan_out


def build(syncs):
    g = G()
    for a, b in syncs:
        g.sync(a, b)
    return g


def z3_dim(nv, edges):
    reach = reachable_closure(nv, edges)
    def sat(t):
        r = subprocess.run(["z3", "-in"], input=build_smt(nv, edges, reach, t),
                           capture_output=True, text=True)
        return r.stdout.strip().split("\n")[0]
    if sat(3) == "unsat":
        return 4 if sat(4) == "sat" else ">=5"
    return 2 if sat(2) == "sat" else 3


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(99)
    tally = collections.Counter()
    found = []
    classified = 0
    for i in range(n):
        sc = make_scheme(rng)
        g = build(sc)
        if not g.full() or len(g.syncs) != 10:
            tally["bad"] += 1
            continue
        dim = z3_dim(g.nv, g.edges)
        tally[dim] += 1
        classified += 1
        if dim == 4:
            found.append(sc)
            print(f"  *** dim 4 at S=10: {sc}", flush=True)
        if (i + 1) % 500 == 0:
            print(f"  ...{i+1}/{n}  {dict(tally)}", flush=True)
    print(f"\nClassified {classified} optimal S=10 N=7 schemes:")
    for k in sorted(tally, key=str):
        print(f"  dim {k}: {tally[k]}")
    if found:
        print(f"\n*** DIMENSION 4 EXISTS AT THE GOSSIP MINIMUM S=10 ({len(found)} found) ***")
        print("  example: " + " ".join(f"({a},{b})" for a, b in found[0]))
    else:
        print("\nNo dimension-4 optimal (S=10) scheme found in this sample; "
              "minimum S for an N=7 dim-4 execution is most likely 11.")


if __name__ == "__main__":
    main()

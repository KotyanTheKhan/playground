#!/usr/bin/env python3
"""Hunt for a dimension-4 fully frontier-synchronized execution of N=7 processes
without enumerating (which OOMs). Executions are generated in pure Python by
randomized walks that stop at the first full synchronization (like the
enumerator, but with no dedup cache, so memory-light), plus structured
gossip-optimal schemes. Each one's exact dimension is decided by the z3 SMT
oracle (confirm_dim.build_smt): z3 UNSAT at t=3 PROVES dimension >= 4.

The execution -> event-DAG expansion mirrors src/process_graph.cpp exactly:
init() gives N start vertices (0..N-1); sync(a,b) adds a shared join vertex above
both current heads and two new head vertices above the join.
"""
import os, sys, random, itertools, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt


class PG:
    def __init__(self, n):
        self.n_procs = n
        self.nv = n
        self.edges = []
        self.last = list(range(n))      # proc_last_vertex
        self.syncs = []

    def copy(self):
        g = PG(self.n_procs)
        g.nv = self.nv
        g.edges = list(self.edges)
        g.last = list(self.last)
        g.syncs = list(self.syncs)
        return g

    def sync(self, a, b):
        pa, pb = self.last[a], self.last[b]
        join = self.nv; anv = self.nv + 1; bnv = self.nv + 2
        self.nv += 3
        self.edges += [(pa, join), (pb, join), (join, anv), (join, bnv)]
        self.last[a] = anv
        self.last[b] = bnv
        self.syncs.append((a, b))


def full_synced(g):
    reach = reachable_closure(g.nv, g.edges)
    starts = range(g.n_procs)
    return all(L in reach[s] for s in starts for L in g.last), reach


def z3_dim(g, reach=None):
    if reach is None:
        reach = reachable_closure(g.nv, g.edges)
    def sat(t):
        r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, t),
                           capture_output=True, text=True)
        return r.stdout.strip().split("\n")[0]
    if sat(3) == "unsat":
        return ">=4"
    return 2 if sat(2) == "sat" else 3


def random_walk(n, smax, rng, pairs):
    """Return the first fully-synchronized PG along a random sync walk, or None."""
    g = PG(n)
    for _ in range(smax):
        ok, reach = full_synced(g)
        if ok:
            return g, reach
        a, b = rng.choice(pairs)
        g.sync(a, b)
    ok, reach = full_synced(g)
    return (g, reach) if ok else None


def gossip_schemes():
    crosses = [
        [(0, 1), (2, 3), (0, 2), (1, 3)],
        [(0, 1), (2, 3), (0, 3), (1, 2)],
        [(0, 2), (1, 3), (0, 1), (2, 3)],
        [(0, 1), (2, 3), (1, 3), (0, 2)],
    ]
    extras = [4, 5, 6]
    out = []
    for hub in [0, 1, 2, 3]:
        for cross in crosses:
            out.append([(e, hub) for e in extras] + cross +
                       [(hub, e) for e in reversed(extras)])
    for cross in crosses:
        out.append([(4, 0), (5, 1), (6, 2)] + cross + [(0, 4), (1, 5), (2, 6)])
    return out


def build(syncs, n=7):
    g = PG(n)
    for a, b in syncs:
        g.sync(a, b)
    return g


def main():
    N = 7
    n_random = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    smax = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    by_dim = collections.Counter()
    by_S = collections.Counter()
    found = []

    print("== structured gossip-optimal schemes ==")
    for sc in gossip_schemes():
        g = build(sc, N)
        ok, reach = full_synced(g)
        if not ok:
            continue
        dim = z3_dim(g, reach)
        by_dim[(len(g.syncs), dim)] += 1
        if dim == ">=4":
            found.append(g.syncs)
            print("  *** dim>=4:", g.syncs)
    print(f"  {dict(by_dim)}")

    print(f"== {n_random} randomized walks (smax={smax}) ==")
    rng = random.Random(2024)
    pairs = list(itertools.combinations(range(N), 2))
    seen = 0
    for i in range(n_random):
        res = random_walk(N, smax, rng, pairs)
        if res is None:
            continue
        g, reach = res
        seen += 1
        dim = z3_dim(g, reach)
        by_dim[(len(g.syncs), dim)] += 1
        by_S[len(g.syncs)] += 1
        if dim == ">=4":
            found.append(g.syncs)
            print("  *** dim>=4:", g.syncs, flush=True)
        if (i + 1) % 2000 == 0:
            mx = max((d for (_, d) in by_dim if d != ">=4"), default=0)
            print(f"  ...{i+1}/{n_random} full-sync seen={seen} "
                  f"maxdim={'>=4' if found else mx} S-dist={dict(by_S)}", flush=True)

    print(f"\nClassified {seen} full-sync N=7 executions (z3).")
    print("by (S, dim):")
    for k in sorted(by_dim, key=lambda x: (x[0], str(x[1]))):
        print(f"  S={k[0]} dim={k[1]}: {by_dim[k]}")
    min_s4 = min((s for (s, d) in by_dim if d == ">=4"), default=None)
    if min_s4 is not None:
        print(f"smallest S with a dimension>=4 execution in this search: {min_s4}")
    if found:
        print(f"\n*** DIMENSION >= 4 FOUND ({len(found)}): ***")
        for sc in found:
            print("  " + " ".join(f"({a},{b})" for a, b in sc))
    else:
        print("\nNo dimension >= 4 found.")


if __name__ == "__main__":
    main()

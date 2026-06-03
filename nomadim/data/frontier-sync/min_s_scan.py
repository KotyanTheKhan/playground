#!/usr/bin/env python3
"""Unified exact-dimension scan for fully frontier-synchronized executions of N
processes (N too large to enumerate). For each generated execution we compute
the EXACT order dimension with the z3 oracle, then aggregate: the dimension
distribution by S, the minimum S per dimension, the maximum dimension, and an
example of each (S, dim). This answers both "min S for dim 2/3/4/..." and "does
a higher dimension appear" in one pass.

Generation mixes (a) constructive gossip-OPTIMAL schemes at S = 2N-4 (random
4-core + fan-in / 4-cross / fan-out) so the minimal layer is sampled, and (b)
efficiency-biased knowledge-mask walks at a spread of S values.

Parallel-friendly: pass a seed; run several copies and merge the printed
`MINS`/`TALLY` lines.

Usage: min_s_scan.py N [n_samples] [cap_S] [seed]
"""
import os, sys, random, itertools, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt

N = int(sys.argv[1])
FULL = (1 << N) - 1
GOSSIP = 2 * N - 4
PAIRS = list(itertools.combinations(range(N), 2))

CROSS = [
    lambda c: [(c[0], c[1]), (c[2], c[3]), (c[0], c[2]), (c[1], c[3])],
    lambda c: [(c[0], c[1]), (c[2], c[3]), (c[0], c[3]), (c[1], c[2])],
    lambda c: [(c[0], c[2]), (c[1], c[3]), (c[0], c[1]), (c[2], c[3])],
]


class G:
    def __init__(self):
        self.know = [1 << p for p in range(N)]
        self.last = list(range(N))
        self.nv = N
        self.edges = []
        self.syncs = []

    def sync(self, a, b):
        pa, pb = self.last[a], self.last[b]
        j, anv, bnv = self.nv, self.nv + 1, self.nv + 2
        self.nv += 3
        self.edges += [(pa, j), (pb, j), (j, anv), (j, bnv)]
        self.last[a], self.last[b] = anv, bnv
        u = self.know[a] | self.know[b]
        self.know[a] = self.know[b] = u
        self.syncs.append((a, b))

    def full(self):
        return all(k == FULL for k in self.know)


def from_syncs(syncs):
    g = G()
    for a, b in syncs:
        g.sync(a, b)
    return g


def greedy_walk(rng, cap, greedy_p):
    g = G()
    while not g.full() and len(g.syncs) < cap:
        prod = [(a, b) for (a, b) in PAIRS if g.know[a] != g.know[b]]
        if not prod:
            break
        if rng.random() < greedy_p:
            def gain(ab):
                a, b = ab
                return (bin(g.know[a] | g.know[b]).count("1")
                        - max(bin(g.know[a]).count("1"), bin(g.know[b]).count("1")))
            best = max(gain(ab) for ab in prod)
            prod = [ab for ab in prod if gain(ab) == best]
        g.sync(*rng.choice(prod))
    return g if g.full() else None


def constructive(rng):
    procs = list(range(N)); rng.shuffle(procs)
    core, extras = procs[:4], procs[4:]
    rng.shuffle(core)
    sc = [(e, rng.choice(core)) for e in extras]
    sc += rng.choice(CROSS)(core)
    sc += [(rng.choice(core), e) for e in extras]
    g = from_syncs(sc)
    return g if g.full() and len(g.syncs) == GOSSIP else None


def exact_dim(g, hi=None):
    hi = hi or N
    reach = reachable_closure(g.nv, g.edges)
    for t in range(2, hi + 1):
        r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, t),
                           capture_output=True, text=True)
        if r.stdout.strip().split("\n")[0] == "sat":
            return t
    return hi + 99


def main():
    n_samples = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else GOSSIP + 6
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)
    by = collections.defaultdict(collections.Counter)
    mins = {}
    examples = {}
    seen = 0
    for i in range(n_samples):
        # 1/3 constructive optimal (S=gossip), 2/3 greedy walks of varied greediness
        if i % 3 == 0:
            g = constructive(rng)
        else:
            g = greedy_walk(rng, cap + 4, [0.97, 0.8, 0.55][i % 3])
        if g is None:
            continue
        S = len(g.syncs)
        if S > cap:
            continue
        seen += 1
        d = exact_dim(g)
        by[S][d] += 1
        if d not in mins or S < mins[d]:
            mins[d] = S
            examples[d] = list(g.syncs)
        if d >= 5:
            print(f"DIMGE5 S={S} {g.syncs}", flush=True)
        if (i + 1) % 500 == 0:
            print(f"  ...{i+1}/{n_samples} seen={seen} mins={dict(sorted(mins.items()))}",
                  flush=True)
    # machine-readable aggregates for merging
    for S in sorted(by):
        print(f"TALLY S={S} " + " ".join(f"{d}:{by[S][d]}" for d in sorted(by[S])))
    print("MINS " + " ".join(f"{d}:{mins[d]}" for d in sorted(mins)))
    print("MAXDIM " + str(max(mins) if mins else 0))
    for d in sorted(mins):
        print(f"EXAMPLE dim{d} S={mins[d]}: " +
              " ".join(f"({a},{b})" for a, b in examples[d]))


if __name__ == "__main__":
    main()

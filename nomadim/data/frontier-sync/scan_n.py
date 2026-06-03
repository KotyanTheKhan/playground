#!/usr/bin/env python3
"""Scan the order dimensions of fully frontier-synchronized executions of N
processes, for N too large to enumerate (N >= 7 OOMs the enumerator).

Executions are generated in pure Python by efficiency-biased random walks: each
process carries a knowledge bitmask (which starts are in the causal past of its
current head), a sync unions the two masks, and full synchronization is "every
mask full". Biasing toward maximum-gain productive syncs reaches full sync near
the optimal S = 2N-4, so we sample the minimal / near-minimal (highest-
dimensional) executions. Each is classified by the z3 SMT oracle
(confirm_dim.build_smt). Reports the dimension distribution by S, the maximum
dimension found (with an example), and the minimum S per dimension.

Usage: scan_n.py N [n_samples] [cap_S]
"""
import os, sys, random, itertools, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt

N = int(sys.argv[1])
FULL = (1 << N) - 1
GOSSIP = 2 * N - 4
PAIRS = list(itertools.combinations(range(N), 2))


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


def generate(rng, cap, greedy_p):
    g = G()
    while not g.full() and len(g.syncs) < cap:
        prod = [(a, b) for (a, b) in PAIRS if g.know[a] != g.know[b]]
        if not prod:
            break
        if rng.random() < greedy_p:
            def gain(ab):
                a, b = ab
                u = bin(g.know[a] | g.know[b]).count("1")
                return u - max(bin(g.know[a]).count("1"), bin(g.know[b]).count("1"))
            best = max(gain(ab) for ab in prod)
            prod = [ab for ab in prod if gain(ab) == best]
        a, b = rng.choice(prod)
        g.sync(a, b)
    return g if g.full() else None


def z3_dim(nv, edges, hi=None):
    hi = hi or N
    reach = reachable_closure(nv, edges)
    for t in range(2, hi + 1):
        r = subprocess.run(["z3", "-in"], input=build_smt(nv, edges, reach, t),
                           capture_output=True, text=True)
        if r.stdout.strip().split("\n")[0] == "sat":
            return t
    return f">{hi}"


def main():
    n_samples = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else GOSSIP + 4
    rng = random.Random(31)
    by = collections.defaultdict(collections.Counter)   # S -> {dim: n}
    sdist = collections.Counter()
    examples = {}
    max_dim = 0
    seen = 0
    print(f"N={N}, gossip minimum S={GOSSIP}, classify S<= {cap}")
    for i in range(n_samples):
        g = generate(rng, cap + 3, greedy_p=0.95 if i % 3 else 0.6)
        if g is None:
            continue
        S = len(g.syncs)
        sdist[S] += 1
        if S > cap:
            continue
        seen += 1
        d = z3_dim(g.nv, g.edges)
        di = d if isinstance(d, int) else 99
        by[S][d] += 1
        if (S, d) not in examples:
            examples[(S, d)] = list(g.syncs)
        if di > max_dim:
            max_dim = di
            print(f"  new max dim {d} at S={S}: {g.syncs}", flush=True)
        if (i + 1) % 500 == 0:
            print(f"  ...{i+1}/{n_samples} seen={seen} maxdim={max_dim} "
                  f"S-dist={dict(sorted(sdist.items()))}", flush=True)

    print(f"\nClassified {seen} full-sync N={N} executions (z3).")
    print("dimension distribution by S:")
    for S in sorted(by):
        print(f"  S={S}: {dict(sorted(by[S].items(), key=lambda kv: str(kv[0])))}")
    print(f"maximum dimension found: {max_dim}")
    # minimum S per dimension
    mins = {}
    for S in by:
        for d in by[S]:
            if isinstance(d, int):
                mins[d] = min(mins.get(d, 1 << 30), S)
    for d in sorted(mins):
        print(f"  dim {d}: first at S={mins[d]}")
    if isinstance(max_dim, int) and max_dim >= 1:
        key = (mins[max_dim], max_dim)
        print(f"\nexample of the max dimension {max_dim} (S={mins[max_dim]}):")
        print("  " + " ".join(f"({a},{b})" for a, b in examples[key]))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Find the minimum number of synchronizations S at which an N=7 fully
frontier-synchronized execution attains order dimension 4.

Generation is biased toward *efficient* gossip: each process carries a knowledge
bitmask (which starts are in the causal past of its current head); a sync unions
the two masks, and full synchronization is "every mask is full". Choosing
productive / maximum-gain syncs reaches full sync in close to the optimal S =
2N-4 = 10, so we actually sample the minimal and near-minimal executions (which
fully random walks almost never produce). Each full-sync execution at S <= cap
is classified by the z3 oracle; we report, per S, the dimension distribution and
the smallest S that yields a dimension-4 execution.

Usage: min_s_dim4.py [n_samples] [cap_S]
"""
import os, sys, random, itertools, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt

N = 7
FULL = (1 << N) - 1


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


PAIRS = list(itertools.combinations(range(N), 2))


def generate(rng, cap, greedy_p=0.7):
    g = G()
    while not g.full() and len(g.syncs) < cap:
        prod = [(a, b) for (a, b) in PAIRS if g.know[a] != g.know[b]]
        if not prod:
            break
        if rng.random() < greedy_p:
            best = max(bin(g.know[a] | g.know[b]).count("1")
                       - max(bin(g.know[a]).count("1"), bin(g.know[b]).count("1"))
                       for (a, b) in prod)
            cand = [(a, b) for (a, b) in prod
                    if bin(g.know[a] | g.know[b]).count("1")
                    - max(bin(g.know[a]).count("1"), bin(g.know[b]).count("1")) == best]
            a, b = rng.choice(cand)
        else:
            a, b = rng.choice(prod)
        g.sync(a, b)
    return g if g.full() else None


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
    n_samples = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    rng = random.Random(7)
    by = collections.defaultdict(collections.Counter)   # S -> {dim: count}
    examples = {}                                        # (S,dim) -> syncs
    sdist = collections.Counter()
    for i in range(n_samples):
        g = generate(rng, cap, greedy_p=0.6 if i % 2 else 0.95)
        if g is None:
            continue
        S = len(g.syncs)
        sdist[S] += 1
        # only classify the minimal / near-minimal ones (dim 4 at S>=12 is known)
        if S > 11:
            continue
        dim = z3_dim(g.nv, g.edges)
        by[S][dim] += 1
        if (S, dim) not in examples:
            examples[(S, dim)] = list(g.syncs)
        if dim == 4 and S <= 11:
            print(f"  *** dim 4 at S={S}: {g.syncs}", flush=True)
        if (i + 1) % 1000 == 0:
            print(f"  ...{i+1}/{n_samples}  S-dist={dict(sdist)}  "
                  f"S10={dict(by[10])} S11={dict(by[11])}", flush=True)

    print(f"\nGenerated full-sync samples by S: {dict(sorted(sdist.items()))}")
    print("dimension distribution at the minimal S values:")
    for S in sorted(by):
        print(f"  S={S}: {dict(by[S])}")
    s4 = [S for S in sorted(by) if by[S].get(4)]
    if s4:
        S = s4[0]
        print(f"\nMinimum S with a dimension-4 N=7 execution (this search): {S}")
        print("  example: " + " ".join(f"({a},{b})" for a, b in examples[(S, 4)]))
    else:
        print("\nNo dimension-4 execution at S<=11 in this search "
              "(dim 4 known to occur at S=12).")


if __name__ == "__main__":
    main()

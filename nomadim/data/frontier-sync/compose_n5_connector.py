#!/usr/bin/env python3
"""N=5 analog of the connector rescue: compose two minimum dim-2 N=5 executions
(S=7) over all 120 frontier matchings, find the dim-3 crowns, and find the
recovery connector syncs (single sync from the 10 possible N=5 pairs) that pull
each crown back to dimension 2.
"""
import os, sys, glob, re, subprocess, itertools, collections
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build

HERE = os.path.dirname(os.path.abspath(__file__))
N = 5
PAIRS = list(itertools.combinations(range(N), 2))   # 10 possible N=5 syncs
POOL = ThreadPoolExecutor(max_workers=6)


def is_dim2(syncs):
    g = build(syncs, N)
    reach = reachable_closure(g.nv, g.edges)
    r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def wl_sig(syncs):
    g = build(syncs, N); reach = reachable_closure(g.nv, g.edges); nv = g.nv
    up = [set(reach[v]) for v in range(nv)]
    down = [set() for _ in range(nv)]
    for v in range(nv):
        for w in reach[v]:
            down[w].add(v)
    def ren(cs):
        o = {c: i for i, c in enumerate(sorted(set(cs)))}; return [o[c] for c in cs]
    color = ren([(len(down[v]), len(up[v])) for v in range(nv)])
    for _ in range(4):
        color = ren([(color[v], tuple(sorted(color[u] for u in down[v])),
                      tuple(sorted(color[w] for w in up[v]))) for v in range(nv)])
    return tuple(sorted(color))


def load_blocks():
    files = sorted(glob.glob(os.path.join(HERE, "N5_S7_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    blocks = []
    for f in files:
        body = open(f).read().split("meta:")[0]
        blocks.append([(int(a), int(b)) for a, b in
                       re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)])
    return blocks


def main():
    blocks = load_blocks()
    # a representative spread of 6 of the 40 blocks (star is real4_01 = index 0)
    idx = [0, 6, 13, 20, 32, 39]
    use = [(i, blocks[i]) for i in idx]
    perms = list(itertools.permutations(range(N)))    # 120 matchings
    print(f"using {len(use)} of {len(blocks)} dim-2 N=5 blocks: indices {idx}")
    print(f"star (block 0) = {blocks[0]}")

    # classify all (A,B) x 120 matchings
    jobs = []
    for ai, A in use:
        for bi, B in use:
            for pi in perms:
                base = list(A) + [(pi[a], pi[b]) for (a, b) in B]
                jobs.append((ai, bi, pi, base))
    print(f"classifying {len(jobs)} compositions...", flush=True)
    results = list(POOL.map(lambda j: is_dim2(j[3]), jobs))

    dim2 = sum(results)
    crowns = {}     # sig -> (base, a_len, ai, bi, pi)
    for (ai, bi, pi, base), ok in zip(jobs, results):
        if not ok:
            crowns.setdefault(wl_sig(base), (base, 7, ai, bi, pi))
    print(f"\ndirect: {dim2}/{len(jobs)} dim-2 ({dim2/len(jobs)*100:.0f}%); "
          f"{len(jobs)-dim2} crowns in {len(crowns)} non-isomorphic classes.")

    # recovery syncs: which single connector rescues each crown class
    print("\nrecovery connector sync (single) per crown class:")
    rescued = 0
    for k, (sig, (base, a, ai, bi, pi)) in enumerate(sorted(
            crowns.items(), key=lambda kv: kv[1][2]), 1):
        head, tail = base[:a], base[a:]
        moved = tuple(x for x in range(N) if pi[x] != x)
        good = [p for p in PAIRS if is_dim2(head + [p] + tail)]
        # also try length-2 if no single sync rescues
        two = None
        if not good:
            for c in itertools.product(PAIRS, repeat=2):
                if is_dim2(head + list(c) + tail):
                    two = c; break
        if good or two:
            rescued += 1
        tag = f"len-1: {good}" if good else f"len-1: none; len-2: {two}"
        print(f"  crown #{k} (blk{ai};blk{bi}, pi={pi}, moved={moved}):  {tag}")

    print(f"\n{rescued}/{len(crowns)} crown classes recovered by a connector "
          f"(<=2 syncs).")
    POOL.shutdown()


if __name__ == "__main__":
    main()

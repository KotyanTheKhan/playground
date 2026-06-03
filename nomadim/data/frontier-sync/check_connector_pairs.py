#!/usr/bin/env python3
"""For each crown (dim-3 direct composition), which of the 6 possible single
connector syncs rescue it back to dimension 2 -- any pair, or only certain ones?
"""
import os, sys, glob, re, subprocess, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build, full_synced

HERE = os.path.dirname(os.path.abspath(__file__))
PAIRS = list(itertools.combinations(range(4), 2))   # (0,1)(0,2)(0,3)(1,2)(1,3)(2,3)


def is_dim2(syncs):
    g = build(syncs, 4)
    reach = reachable_closure(g.nv, g.edges)
    r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def wl_sig(syncs):
    g = build(syncs, 4); reach = reachable_closure(g.nv, g.edges); nv = g.nv
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
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    return [[(int(a), int(b)) for a, b in
             re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", open(f).read().split("meta:")[0])]
            for f in files]


def main():
    blocks = load_blocks()
    perms = list(itertools.permutations(range(4)))
    crowns = {}     # sig -> representative (base syncs, a_len)
    for i in range(len(blocks)):
        for j in range(len(blocks)):
            for pi in perms:
                base = list(blocks[i]) + [(pi[a], pi[b]) for (a, b) in blocks[j]]
                if not is_dim2(base):
                    sig = wl_sig(base)
                    crowns.setdefault(sig, (base, len(blocks[i]), i + 1, j + 1, pi))
        print(f"  ...scanned A=B{i+1} ({len(crowns)} crown classes)", flush=True)

    print(f"\n{len(crowns)} crown classes. Which single connector sync rescues each?\n")
    for k, (sig, (base, a, bi, bj, pi)) in enumerate(crowns.items(), 1):
        head, tail = base[:a], base[a:]
        good = [p for p in PAIRS if is_dim2(head + [p] + tail)]
        print(f"crown #{k}  (B{bi};B{bj}, pi={pi})")
        print(f"   rescuing connector syncs ({len(good)}/6): {good}")
    # union/intersection summary
    print("\nlegend: pairs are (0,1)(0,2)(0,3)(1,2)(1,3)(2,3)")


if __name__ == "__main__":
    main()

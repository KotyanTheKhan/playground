#!/usr/bin/env python3
"""For each crown, which connectors of length 1 and length 2 rescue it to dim 2,
and do the length-2 rescuers still have to involve the 'crossed pair' (the pair
of channels the frontier matching transposes)?
"""
import os, sys, glob, re, subprocess, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build, full_synced

HERE = os.path.dirname(os.path.abspath(__file__))
PAIRS = list(itertools.combinations(range(4), 2))


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


def crossed_pair(pi):
    sw = [k for k in range(4) if pi[k] != k]
    return tuple(sorted(sw)) if len(sw) == 2 else None


def load_blocks():
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    return [[(int(a), int(b)) for a, b in
             re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", open(f).read().split("meta:")[0])]
            for f in files]


def main():
    blocks = load_blocks()
    perms = list(itertools.permutations(range(4)))
    crowns = {}
    for i in range(len(blocks)):
        for j in range(len(blocks)):
            for pi in perms:
                base = list(blocks[i]) + [(pi[a], pi[b]) for (a, b) in blocks[j]]
                if not is_dim2(base):
                    crowns.setdefault(wl_sig(base), (base, len(blocks[i]), i+1, j+1, pi))
        print(f"  ...scanned A=B{i+1} ({len(crowns)} crown classes)", flush=True)

    print(f"\n{len(crowns)} crown classes. Rescuing connectors of length 1 and 2:\n")
    for k, (sig, (base, a, bi, bj, pi)) in enumerate(crowns.items(), 1):
        head, tail = base[:a], base[a:]
        cp = crossed_pair(pi)
        one = [p for p in PAIRS if is_dim2(head + [p] + tail)]
        two = [c for c in itertools.product(PAIRS, repeat=2)
               if is_dim2(head + list(c) + tail)]
        two_with_cp = [c for c in two if cp in c]
        two_without_cp = [c for c in two if cp not in c]
        print(f"crown #{k}  (B{bi};B{bj}, pi={pi}, crossed pair={cp})")
        print(f"   length 1: {len(one)}/6 rescue -> {one}")
        print(f"   length 2: {len(two)}/36 rescue; {len(two_with_cp)} contain the "
              f"crossed pair, {len(two_without_cp)} do NOT")
        if two_without_cp:
            print(f"      length-2 rescuers NOT using the crossed pair: {two_without_cp[:8]}"
                  + (" ..." if len(two_without_cp) > 8 else ""))


if __name__ == "__main__":
    main()

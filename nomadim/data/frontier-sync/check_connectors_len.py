#!/usr/bin/env python3
"""Rescue counts for connectors of length 1..4, per crown class. Does the number
of rescuing connectors keep growing, and can a longer connector ever rescue a
crown WITHOUT touching the crossed pair (the channels the matching transposes)?
"""
import os, sys, subprocess, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build

PAIRS = list(itertools.combinations(range(4), 2))
MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 4

B1 = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]          # star
B9 = [(0, 1), (2, 3), (0, 2), (0, 1), (2, 3)]          # two-pairs


def perm(syncs, pi):
    return [(pi[a], pi[b]) for (a, b) in syncs]


def is_dim2(syncs):
    g = build(syncs, 4)
    reach = reachable_closure(g.nv, g.edges)
    r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def crossed(pi):
    sw = [k for k in range(4) if pi[k] != k]
    return tuple(sorted(sw))


# the 5 crown classes (A, B, pi)
CROWNS = [
    ("B1;B1", B1, B1, (0, 1, 3, 2)),
    ("B1;B1", B1, B1, (0, 2, 1, 3)),
    ("B1;B9", B1, B9, (0, 2, 1, 3)),
    ("B9;B1", B9, B1, (0, 2, 1, 3)),
    ("B9;B9", B9, B9, (0, 2, 1, 3)),
]


def main():
    for k, (name, A, B, pi) in enumerate(CROWNS, 1):
        head = list(A)
        tail = perm(B, pi)
        cp = crossed(pi)
        # sanity: direct is a crown
        assert not is_dim2(head + tail), f"crown #{k} is not actually a crown"
        print(f"crown #{k}  {name}  pi={pi}  crossed pair={cp}", flush=True)
        for c in range(1, MAXLEN + 1):
            total = 6 ** c
            resc = 0
            without = 0
            ex_without = None
            for conn in itertools.product(PAIRS, repeat=c):
                if is_dim2(head + list(conn) + tail):
                    resc += 1
                    if cp not in conn:
                        without += 1
                        if ex_without is None:
                            ex_without = conn
            note = ""
            if without:
                note = f"; {without} avoid the crossed pair (e.g. {ex_without})"
            else:
                note = "; ALL contain the crossed pair"
            print(f"   length {c}: {resc}/{total} rescue ({resc/total*100:.1f}%){note}",
                  flush=True)


if __name__ == "__main__":
    main()

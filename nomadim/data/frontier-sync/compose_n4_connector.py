#!/usr/bin/env python3
"""Composition of dim-2 N=4 executions with a CONNECTOR (1..4 syncs) in between.

Like compose_n4.py, but instead of gluing A's output frontier directly to B's
input frontier we insert a short connector of c syncs:

    composed = A.syncs  +  connector(c syncs)  +  pi(B.syncs)

The direct case (c=0) preserves dimension 2 on only 28% of the 2400 (A,B,pi)
variants; the other 72% form a crown (dimension 3). Hypothesis: a short connector
re-mixes the frontier and rescues many crowns back to dimension 2. We deduplicate
the crowns by poset isomorphism (Weisfeiler-Leman) and, for each crown class,
find the MINIMUM connector length (1..4) that restores dimension 2.
"""
import os, sys, glob, re, subprocess, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build, full_synced

HERE = os.path.dirname(os.path.abspath(__file__))
PAIRS = list(itertools.combinations(range(4), 2))   # 6 possible N=4 syncs


def is_dim2(syncs):
    g = build(syncs, 4)
    reach = reachable_closure(g.nv, g.edges)
    r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def wl_sig(syncs):
    g = build(syncs, 4)
    reach = reachable_closure(g.nv, g.edges)
    nv = g.nv
    up = [set(reach[v]) for v in range(nv)]
    down = [set() for _ in range(nv)]
    for v in range(nv):
        for w in reach[v]:
            down[w].add(v)
    color = _ren([(len(down[v]), len(up[v])) for v in range(nv)])
    for _ in range(4):
        color = _ren([(color[v], tuple(sorted(color[u] for u in down[v])),
                       tuple(sorted(color[w] for w in up[v]))) for v in range(nv)])
    return tuple(sorted(color))


def _ren(cs):
    o = {c: i for i, c in enumerate(sorted(set(cs)))}
    return [o[c] for c in cs]


def load_blocks():
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    blocks = []
    for f in files:
        body = open(f).read().split("meta:")[0]
        blocks.append([(int(a), int(b)) for a, b in
                       re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)])
    return blocks


def rescue(base_syncs, a_len, max_c=4):
    """Smallest connector length c in 1..max_c such that inserting c syncs after
    the first a_len syncs makes the whole thing dim 2. Returns (c, connector) or
    (None, None). a_len = number of A's syncs (connector goes right after A)."""
    head, tail = base_syncs[:a_len], base_syncs[a_len:]
    for c in range(1, max_c + 1):
        for conn in itertools.product(PAIRS, repeat=c):
            if is_dim2(head + list(conn) + tail):
                return c, list(conn)
    return None, None


def main():
    blocks = load_blocks()
    n = len(blocks)
    perms = list(itertools.permutations(range(4)))

    # classify the 2400 direct compositions; bucket crowns by poset class
    crown_classes = {}          # sig -> (size, representative base_syncs, a_len)
    dim2_direct = 0
    for i in range(n):
        for j in range(n):
            for pi in perms:
                base = list(blocks[i]) + [(pi[a], pi[b]) for (a, b) in blocks[j]]
                if is_dim2(base):
                    dim2_direct += 1
                else:
                    sig = wl_sig(base)
                    if sig not in crown_classes:
                        crown_classes[sig] = [0, base, len(blocks[i])]
                    crown_classes[sig][0] += 1
        print(f"  ...classified A=B{i+1}", flush=True)

    crown_total = sum(v[0] for v in crown_classes.values())
    print(f"\ndirect (c=0): {dim2_direct}/2400 dim-2; {crown_total}/2400 crowns "
          f"in {len(crown_classes)} non-isomorphic crown classes.")

    # rescue each crown class with the shortest connector
    print("\nrescuing crown classes with a connector (1..4 syncs):")
    rescued_size = collections.Counter()   # min connector length -> #variants
    examples = {}
    for k, (sig, (size, base, a_len)) in enumerate(sorted(
            crown_classes.items(), key=lambda kv: -kv[1][0]), 1):
        c, conn = rescue(base, a_len, max_c=4)
        if c is None:
            rescued_size["none"] += size
            print(f"  crown class #{k} (x{size}): NOT rescued by connector <=4")
        else:
            rescued_size[c] += size
            print(f"  crown class #{k} (x{size}): rescued by connector length {c}  conn={conn}")
            if c not in examples:
                examples[c] = base[:a_len] + conn + base[a_len:]

    # aggregate: dim-2-achievable variants vs connector budget
    print("\n=== dim-2 reachable variants vs connector budget ===")
    cum = dim2_direct
    print(f"  connector <=0 (direct): {cum}/2400 = {cum/2400*100:.0f}% dim-2")
    for c in [1, 2, 3, 4]:
        cum += rescued_size.get(c, 0)
        print(f"  connector <={c}:          {cum}/2400 = {cum/2400*100:.0f}% dim-2")
    if rescued_size.get("none"):
        print(f"  still crown after connector<=4: {rescued_size['none']}/2400")

    # save one rescued example per connector length
    for c, syncs in sorted(examples.items()):
        path = os.path.join(HERE, f"N4_connector{c}_rescue_dim2.yaml")
        with open(path, "w") as f:
            f.write("execution:\n  n_procs: 4\n  syncs:\n")
            for a, b in syncs:
                f.write(f"    - [{a}, {b}]\n")
            f.write("meta:\n")
            f.write(f"  notes: \"A crown (dim-3 direct composition of two dim-2 N=4 "
                    f"blocks) rescued to DIMENSION 2 by inserting a connector of {c} "
                    f"sync(s) between the two blocks. Total S=10+{c}. z3-verified dim 2.\"\n")
            f.write("  dimension: 2\n")
    print(f"\nsaved rescued examples for connector lengths {sorted(examples)}")


if __name__ == "__main__":
    main()

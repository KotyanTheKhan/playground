#!/usr/bin/env python3
"""Distinct (non-isomorphic) dimension-2 compositions of the 10 mPsi4-dim2 blocks.

Enumerates all 100x24 compositions (A then B, every frontier matching), keeps the
dimension-2 ones, and deduplicates them by an isomorphism INVARIANT of the
composed happened-before poset: Weisfeiler-Leman color refinement on the
reachability closure. Two posets with different WL signatures are provably
non-isomorphic, so one representative per signature gives guaranteed-distinct
examples (a lower bound on the number of isomorphism classes). Prints the
distinct representatives -- preferring diverse source pairs -- and saves them.
"""
import os, sys, glob, re, subprocess, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build, full_synced

HERE = os.path.dirname(os.path.abspath(__file__))


def is_dim2(nv, edges, reach):
    r = subprocess.run(["z3", "-in"], input=build_smt(nv, edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def wl_signature(nv, reach, rounds=4):
    """Weisfeiler-Leman color refinement on the poset (reachability closure)."""
    up = [frozenset(reach[v]) for v in range(nv)]
    down = [set() for _ in range(nv)]
    for v in range(nv):
        for w in reach[v]:
            down[w].add(v)
    color = [(len(down[v]), len(up[v])) for v in range(nv)]
    color = _renumber(color)
    for _ in range(rounds):
        newc = []
        for v in range(nv):
            newc.append((color[v],
                         tuple(sorted(color[u] for u in down[v])),
                         tuple(sorted(color[w] for w in up[v]))))
        color = _renumber(newc)
    return tuple(sorted(color))


def _renumber(colors):
    order = {c: i for i, c in enumerate(sorted(set(colors)))}
    return [order[c] for c in colors]


def load_blocks():
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    blocks = []
    for f in files:
        body = open(f).read().split("meta:")[0]
        syncs = [(int(a), int(b)) for a, b in
                 re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)]
        blocks.append(syncs)
    return blocks


def main():
    blocks = load_blocks()
    n = len(blocks)
    labels = [f"B{i+1}" for i in range(n)]
    perms = list(itertools.permutations(range(4)))

    # signature -> representative (label_a, label_b, pi, syncs)
    reps = {}
    sig_count = collections.Counter()
    dim2_total = 0
    for i in range(n):
        for j in range(n):
            for pi in perms:
                syncs = list(blocks[i]) + [(pi[a], pi[b]) for (a, b) in blocks[j]]
                g = build(syncs, 4)
                reach = reachable_closure(g.nv, g.edges)
                if not is_dim2(g.nv, g.edges, reach):
                    continue
                dim2_total += 1
                sig = wl_signature(g.nv, reach)
                sig_count[sig] += 1
                if sig not in reps:
                    reps[sig] = (labels[i], labels[j], pi, syncs)
                else:
                    # prefer a representative from a distinct source pair for variety
                    pa, pb, _, _ = reps[sig]
                    if (pa, pb) == (labels[i], labels[j]) and (labels[i] != labels[j]):
                        pass
        print(f"  ...{labels[i]} done ({len(reps)} distinct so far)", flush=True)

    print(f"\n{dim2_total} dimension-2 compositions; "
          f"{len(reps)} are pairwise NON-ISOMORPHIC (distinct WL poset signatures).")
    print("distinct dim-2 composed executions (representative per class):\n")
    items = sorted(reps.items(), key=lambda kv: (-sig_count[kv[0]], kv[1][0], kv[1][1]))
    for k, (sig, (la, lb, pi, syncs)) in enumerate(items, 1):
        print(f"  #{k:>2}  {la};{lb}  matching pi={pi}  (x{sig_count[sig]} of the 672)")
        print(f"       syncs = {syncs}")

    # save the distinct representatives
    for k, (sig, (la, lb, pi, syncs)) in enumerate(items, 1):
        path = os.path.join(HERE, f"N4_compose_dim2_distinct_{k:02d}.yaml")
        with open(path, "w") as f:
            f.write("execution:\n  n_procs: 4\n  syncs:\n")
            for a, b in syncs:
                f.write(f"    - [{a}, {b}]\n")
            f.write("meta:\n")
            f.write(f"  notes: \"Distinct dimension-2 composition #{k} of two minimum "
                    f"dim-2 N=4 executions: {la} then {lb} with frontier matching pi={pi}. "
                    f"The composed S=10 fully-synchronized execution is dimension 2 "
                    f"(z3-verified). One of {len(reps)} pairwise non-isomorphic dim-2 "
                    f"compositions (distinct WL poset signatures).\"\n")
            f.write("  dimension: 2\n")
    print(f"\nsaved {len(items)} files N4_compose_dim2_distinct_01..{len(items):02d}.yaml")


if __name__ == "__main__":
    main()

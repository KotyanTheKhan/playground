#!/usr/bin/env python3
"""Connector recovery scan for N = 5..8 (the star block is the canonical dim-2
block; for N>=6 the full dim-2 block set cannot be enumerated). For each N we
compose star;pi(star) for a curated set of frontier matchings of increasing
displacement d (number of moved channels), classify crown vs dim-2, and find the
minimum connector (syncs among the moved channels) that recovers dimension 2.
Crown and recovered example executions are saved per (N, matching).
"""
import os, sys, subprocess, itertools
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build, full_synced

HERE = os.path.dirname(os.path.abspath(__file__))
EXDIR = os.path.join(HERE, "connector_examples")
os.makedirs(EXDIR, exist_ok=True)
POOL = ThreadPoolExecutor(max_workers=6)


def star(N):
    return [(0, k) for k in range(1, N)] + [(0, k) for k in range(N - 2, 0, -1)]


def is_dim2(syncs, N):
    g = build(syncs, N)
    reach = reachable_closure(g.nv, g.edges)
    r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def matchings(N):
    """Curated matchings labelled by structure. Returns list of (label, pi)."""
    out = [("identity", tuple(range(N)))]
    # single d-cycle on leaves 1..d (hub fixed), d = 2..N-1
    for d in range(2, N):
        pi = list(range(N))
        cyc = list(range(1, d + 1))
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            pi[a] = b
        out.append((f"leaf-{d}cycle", tuple(pi)))
    # full N-cycle (hub moved)
    pi = list(range(N))
    cyc = list(range(N))
    for a, b in zip(cyc, cyc[1:] + cyc[:1]):
        pi[a] = b
    out.append((f"full-{N}cycle", tuple(pi)))
    # double transposition (1 2)(3 4)
    if N >= 5:
        pi = list(range(N)); pi[1], pi[2] = 2, 1; pi[3], pi[4] = 4, 3
        out.append(("double-transp", tuple(pi)))
    # hub transposition (0 1)
    pi = list(range(N)); pi[0], pi[1] = 1, 0
    out.append(("hub-transp", tuple(pi)))
    return out


def moved(pi):
    return [x for x in range(len(pi)) if pi[x] != x]


def recover(head, tail, mv, N, maxlen=2):
    """Smallest connector (syncs among moved channels) restoring dim 2."""
    cand = list(itertools.combinations(mv, 2))   # pairs among moved channels
    if not cand:
        cand = list(itertools.combinations(range(N), 2))
    for c in range(1, maxlen + 1):
        conns = list(itertools.product(cand, repeat=c))
        oks = list(POOL.map(lambda conn: is_dim2(head + list(conn) + tail, N), conns))
        for conn, ok in zip(conns, oks):
            if ok:
                return c, list(conn)
    return None, None


def save(path, syncs, N, dim, note):
    with open(path, "w") as f:
        f.write(f"execution:\n  n_procs: {N}\n  syncs:\n")
        for a, b in syncs:
            f.write(f"    - [{a}, {b}]\n")
        f.write(f"meta:\n  notes: \"{note}\"\n  dimension: {dim}\n")


def main():
    Ns = [int(x) for x in sys.argv[1:]] or [5, 6, 7, 8]
    print(f"{'N':>2} {'matching':>14} {'d':>2} {'direct':>7} {'recover':>8}  connector")
    for N in Ns:
        s = star(N)
        for label, pi in matchings(N):
            base = list(s) + [(pi[a], pi[b]) for (a, b) in s]
            d2 = is_dim2(base, N)
            mv = moved(pi)
            if d2:
                print(f"{N:>2} {label:>14} {len(mv):>2} {'dim2':>7} {'-':>8}")
                continue
            head, tail = base[:len(s)], base[len(s):]
            c, conn = recover(head, tail, mv, N, maxlen=2)
            rec = f"len {c}" if c else ">2"
            print(f"{N:>2} {label:>14} {len(mv):>2} {'CROWN':>7} {rec:>8}  {conn}",
                  flush=True)
            # save crown + recovered examples
            tag = f"N{N}_{label}"
            save(os.path.join(EXDIR, tag + "_crown_dim3.yaml"), base, N, 3,
                 f"Crown: star;star composition of dim-2 N={N} executions with frontier "
                 f"matching {label} (pi={pi}); dimension 3.")
            if c:
                rsync = head + conn + tail
                save(os.path.join(EXDIR, tag + f"_recovered_conn{c}_dim2.yaml"), rsync, N, 2,
                     f"Recovered: the {label} crown rescued to dimension 2 by a connector of "
                     f"{c} sync(s) {conn} among the moved channels {mv}. z3-verified dim 2.")
    POOL.shutdown()


if __name__ == "__main__":
    main()

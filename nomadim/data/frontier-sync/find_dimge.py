#!/usr/bin/env python3
"""Fast hunt for a fully frontier-synchronized execution of N processes with
order dimension >= TARGET. For each generated execution we ask z3 a SINGLE
question: is it (TARGET-1)-realizable? SAT => dim < TARGET (cheap: z3 just finds
one realizer); UNSAT => dim >= TARGET (the find, and the expensive case, which is
rare). This is far cheaper than computing the exact dimension, so we can sample
many executions. Generation is the efficiency-biased knowledge-mask walk from
scan_n.py, over a spread of S values.

Usage: find_dimge.py N TARGET [n_samples] [cap_S]
"""
import os, sys, random, itertools, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from scan_n import G  # uses N from scan_n? no -- G uses module-level N there

# Re-bind N locally (scan_n.G closes over scan_n.N); define our own G to be safe.
import importlib
import scan_n


def main():
    N = int(sys.argv[1]); TARGET = int(sys.argv[2])
    n_samples = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 2 * N + 4
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 101
    # reconfigure scan_n for this N
    scan_n.N = N
    scan_n.FULL = (1 << N) - 1
    scan_n.GOSSIP = 2 * N - 4
    scan_n.PAIRS = list(itertools.combinations(range(N), 2))
    gen = scan_n.generate

    rng = random.Random(seed)
    t = TARGET - 1
    found = []
    by_S = collections.Counter()
    ge_by_S = collections.Counter()
    seen = 0
    print(f"N={N}: hunting dimension >= {TARGET} (z3 test: is t={t} UNSAT?), "
          f"gossip min S={2*N-4}, cap S={cap}")
    for i in range(n_samples):
        # vary greediness to spread S across the near-minimal band
        gp = [0.97, 0.85, 0.6][i % 3]
        g = gen(rng, cap, gp)
        if g is None:
            continue
        S = len(g.syncs)
        seen += 1
        by_S[S] += 1
        reach = reachable_closure(g.nv, g.edges)
        r = subprocess.run(["z3", "-in"], input=build_smt(g.nv, g.edges, reach, t),
                           capture_output=True, text=True)
        if r.stdout.strip().split("\n")[0] == "unsat":
            ge_by_S[S] += 1
            found.append((S, list(g.syncs)))
            print(f"  *** dim >= {TARGET} at S={S}: {g.syncs}", flush=True)
        if (i + 1) % 1000 == 0:
            print(f"  ...{i+1}/{n_samples} seen={seen} dim>={TARGET}_found={len(found)} "
                  f"S-dist={dict(sorted(by_S.items()))}", flush=True)

    print(f"\nTested {seen} full-sync N={N} executions for dim >= {TARGET}.")
    print(f"S distribution: {dict(sorted(by_S.items()))}")
    if found:
        print(f"\n*** dim >= {TARGET} FOUND: {len(found)} (by S: {dict(sorted(ge_by_S.items()))}) ***")
        smin = min(S for S, _ in found)
        ex = next(sc for S, sc in found if S == smin)
        print(f"smallest S with dim>={TARGET}: {smin}")
        print("  example: " + " ".join(f"({a},{b})" for a, b in ex))
    else:
        print(f"\nNo dim >= {TARGET} found in {seen} executions "
              f"(so N={N} appears to max out below dimension {TARGET} in this sample).")


if __name__ == "__main__":
    main()

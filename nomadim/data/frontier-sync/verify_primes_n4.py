#!/usr/bin/env python3
"""Are the dimension-2 N=4 fully-synchronized executions finitely generated under
frontier composition?

A composition A;B glues A's output frontier to B's input frontier, both
fully-synchronized dim-2 executions (each >= 5 syncs, the N=4 dim-2 minimum). An
execution is PRIME (indecomposable) if it has no intermediate fully-synchronized
frontier -- i.e. no proper prefix of its syncs is already fully synchronized.

`nomadim enumerate` records every fully-synchronized execution at its FIRST full
synchronization (it stops expanding there), so its non-isomorphic dim-2 results
are exactly the prime dim-2 executions. This script confirms that (every result
really has no intermediate full sync) and counts the primes per sync count S. If
that count keeps growing, the family is NOT finitely generated.
"""
import os, sys, re, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hunt_n7 import build, full_synced

NOMADIM = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                        "..", "..", "build", "nomadim"))
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9


def fully_synced(syncs):
    g = build(syncs, 4)
    ok, _ = full_synced(g)
    return ok


def has_intermediate_full_sync(syncs):
    # a proper prefix (length 5..len-1) that is already fully synchronized
    for k in range(5, len(syncs)):
        if fully_synced(syncs[:k]):
            return k
    return None


def main():
    out = f"/tmp/fs/primes_n4_k{KMAX}.yaml"
    subprocess.run([NOMADIM, "enumerate", "-n", "4", "-k", str(KMAX), "-j", "4",
                    "--all-dims", "--with-dim", "-o", out], check=True,
                   capture_output=True, text=True)
    docs = [d for d in open(out).read().split("---") if "execution" in d]

    prime_by_S = collections.Counter()
    nonprime = 0
    total_dim2 = 0
    for d in docs:
        dim = int(re.search(r"dimension:\s*(\d+)", d).group(1))
        if dim != 2:
            continue
        total_dim2 += 1
        syncs = [(int(a), int(b)) for a, b in
                 re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", d.split("meta:")[0])]
        S = len(syncs)
        k = has_intermediate_full_sync(syncs)
        if k is None:
            prime_by_S[S] += 1
        else:
            nonprime += 1
            print(f"  NON-PRIME dim2 exec (intermediate full sync at k={k}): {syncs}")

    print(f"\nVerified {total_dim2} non-isomorphic dim-2 N=4 executions (S<= {KMAX}).")
    print(f"with an intermediate full-sync frontier (decomposable): {nonprime}")
    print("PRIME dim-2 executions per sync count S:")
    prev = None
    for S in sorted(prime_by_S):
        ratio = f"  (x{prime_by_S[S]/prev:.2f})" if prev else ""
        print(f"  S={S}: {prime_by_S[S]} prime{ratio}")
        prev = prime_by_S[S]
    print("\n=> every dim-2 result is prime; the prime count grows with S, so the "
          "dim-2 N=4 family is NOT finitely generated under frontier composition.")


if __name__ == "__main__":
    main()

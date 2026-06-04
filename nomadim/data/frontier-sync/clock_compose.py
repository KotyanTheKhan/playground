#!/usr/bin/env python3
"""The four §7 exactness assertions over the N=4 corpus, plus a CLI report.

(a) the 10 single blocks                 -> clock exact at 2 coords
(b) threshold (non-crossing) compositions -> exact at 2 coords
(c) crown compositions (no connector)     -> NO 2-clock (dim 3)  [negative ctrl]
(d) fan-repaired compositions             -> exact at 2 coords again
"""
import os, sys, glob, re, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import clock_check_syncs
from clock_fan import compose_with_connector

HERE = os.path.dirname(os.path.abspath(__file__))


def load_blocks():
    """The 10 minimum dim-2 fully-synced N=4 blocks (S=5)."""
    blocks = []
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    for f in files:
        body = open(f).read().split("meta:")[0]
        syncs = [(int(a), int(b)) for a, b in
                 re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)]
        blocks.append((os.path.basename(f).replace(".yaml", ""), syncs))
    return blocks


def assertion_a_single_blocks(blocks):
    """Return list of (name, ok, dim) triples whose single-block clock is NOT exact at dim 2."""
    failures = []
    for name, syncs in blocks:
        ok, dim = clock_check_syncs(4, syncs)
        if not (dim == 2 and ok is True):
            failures.append((name, ok, dim))
    return failures


def assertion_b_threshold(blocks):
    """Return list of (nameA, nameB, ok, dim) for identity-perm compositions NOT exact at dim 2.

    Assertion (b): threshold (non-crossing) compositions stay exact at dim 2.
    The simplest non-crossing matching is the identity permutation [0,1,2,3]
    composed WITHOUT a connector.  For each ordered block pair (A, B) we build
    compose_with_connector(A, B, [0,1,2,3], use_connector=False) and assert
    clock_check_syncs(4, ...) == (True, 2).  Any pair that fails is returned as
    a failure tuple; an empty list means all pairs pass.
    """
    identity = [0, 1, 2, 3]
    failures = []
    for (na, A) in blocks:
        for (nb, B) in blocks:
            composed = compose_with_connector(A, B, identity, use_connector=False)
            ok, dim = clock_check_syncs(4, composed)
            if not (dim == 2 and ok is True):
                failures.append((na, nb, ok, dim))
    return failures


def assertion_cd_crown_and_repair(blocks, perms=None):
    """For each ordered block pair and each crossing perm, check:
    direct compose has no 2-clock (c) AND fan-repaired compose is exact (d).
    Returns (n_crowns, c_failures, d_failures)."""
    if perms is None:
        # the non-identity perms that actually cross (skip identity)
        perms = [list(p) for p in itertools.permutations(range(4))
                 if list(p) != [0, 1, 2, 3]]
    n_crowns, c_fail, d_fail = 0, [], []
    for (na, A) in blocks:
        for (nb, B) in blocks:
            for perm in perms:
                direct = compose_with_connector(A, B, perm, use_connector=False)
                ok_d, dim_d = clock_check_syncs(4, direct)
                if dim_d != 2:                       # a crown
                    n_crowns += 1
                    if ok_d is not None:             # (c) should have no clock
                        c_fail.append((na, nb, perm))
                    repaired = compose_with_connector(A, B, perm, True)
                    ok_r, dim_r = clock_check_syncs(4, repaired)
                    if not (dim_r == 2 and ok_r is True):   # (d)
                        d_fail.append((na, nb, perm, ok_r, dim_r))
    return n_crowns, c_fail, d_fail


def main():
    blocks = load_blocks()
    print(f"loaded {len(blocks)} blocks")
    fa = assertion_a_single_blocks(blocks)
    print(f"(a) single-block exact: {'PASS' if not fa else 'FAIL ' + str(fa)}")
    fb = assertion_b_threshold(blocks)
    print(f"(b) threshold (identity) exact: {'PASS' if not fb else 'FAIL ' + str(fb)}")
    n_crowns, c_fail, d_fail = assertion_cd_crown_and_repair(blocks)
    print(f"(c) crowns found: {n_crowns}; "
          f"crown-has-no-2clock: {'PASS' if not c_fail else 'FAIL ' + str(c_fail)}")
    print(f"(d) fan-repaired exact: {'PASS' if not d_fail else 'FAIL ' + str(d_fail)}")


if __name__ == "__main__":
    main()

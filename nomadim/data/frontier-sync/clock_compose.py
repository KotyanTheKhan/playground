#!/usr/bin/env python3
"""§7 exactness assertions over the N=4 corpus, plus a CLI report.

SCOPE: The clean "crown ⟺ matching crossing; fan = N−#cycles" law is validated
on the HOMOGENEOUS star-to-itself family (B1 ⟹ B1 over all 24 matchings).
Heterogeneous identity compositions (two DIFFERENT dim-2 blocks under the
identity matching) can also crown (dim 3); those crowns are NOT repaired by the
perm-derived fan and are documented as a separate finding.  They may be
repaired by a structure-determined single connector sync.

(a) the 10 single blocks                           -> clock exact at 2 coords
(b/c/d) star-self over all 24 matchings            -> crown iff crossing; fan repairs every crown
finding: heterogeneous identity crowns             -> documented; brute-force single-sync rescue attempted

(b) threshold (identity) check over all pairs is retained for regression use.
(c/d) full 10×10 × non-identity sweep is retained for regression use.
"""
import os, sys, glob, re, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import clock_check_syncs
from clock_fan import compose_with_connector

HERE = os.path.dirname(os.path.abspath(__file__))


def star_block_b1():
    """Return the star-block syncs for B1 (N4_S5_dim2_real4_01).

    B1 is the canonical star block: process 0 is the hub and syncs with each
    leaf in both directions.  This is the block whose self-composition is the
    headline of the crown/fan law.
    """
    return [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]


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


def assertion_cd_star_self(perms=None):
    """Homogeneous headline: compose star block B1 with itself over every matching.

    For each of the 24 permutations of range(4) (identity included):
      - direct compose (no connector): crown iff dim != 2 (c-check)
      - if crown: fan-repaired compose must be (True, 2) (d-check)

    Returns (n_crowns, c_fail, d_fail):
      n_crowns  -- number of matchings that produced a crown
      c_fail    -- list of perms where a crown nonetheless had a 2-clock (should be [])
      d_fail    -- list of (perm, ok_r, dim_r) where the fan repair failed (should be [])
    """
    if perms is None:
        perms = [list(p) for p in itertools.permutations(range(4))]
    B1 = star_block_b1()
    n_crowns, c_fail, d_fail = 0, [], []
    for perm in perms:
        direct = compose_with_connector(B1, B1, perm, use_connector=False)
        ok_d, dim_d = clock_check_syncs(4, direct)
        if dim_d != 2:                           # a crown
            n_crowns += 1
            if ok_d is not None:                 # (c) crown should have no 2-clock
                c_fail.append(perm)
            repaired = compose_with_connector(B1, B1, perm, use_connector=True)
            ok_r, dim_r = clock_check_syncs(4, repaired)
            if not (dim_r == 2 and ok_r is True):
                d_fail.append((perm, ok_r, dim_r))
    return n_crowns, c_fail, d_fail


def heterogeneous_identity_crowns(blocks):
    """Document heterogeneous identity crowns: DISTINCT-block pairs that crown under identity.

    For each ordered pair (A, B) with nameA != nameB, compose under the identity
    permutation WITHOUT a connector.  If clock_check_syncs returns dim != 2, the
    pair is a heterogeneous identity crown.

    For every such crown, brute-force whether some SINGLE connector sync p=(i,j)
    (0 <= i < j < 4) restores dim 2: build list(A) + [p] + list(B) and check.

    Returns a list of (nameA, nameB, rescuers) where rescuers is the list of
    single-sync (i,j) pairs that individually restore (True, 2).  An empty
    rescuers list means no single-sync connector was found.
    """
    identity = [0, 1, 2, 3]
    candidate_syncs = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    result = []
    for (na, A) in blocks:
        for (nb, B) in blocks:
            if na == nb:
                continue
            direct = compose_with_connector(A, B, identity, use_connector=False)
            ok_d, dim_d = clock_check_syncs(4, direct)
            if dim_d != 2:                       # heterogeneous identity crown
                rescuers = []
                for p in candidate_syncs:
                    patched = list(A) + [p] + list(B)
                    ok_p, dim_p = clock_check_syncs(4, patched)
                    if dim_p == 2 and ok_p is True:
                        rescuers.append(p)
                result.append((na, nb, rescuers))
    return result


def main():
    blocks = load_blocks()
    print(f"loaded {len(blocks)} blocks")

    fa = assertion_a_single_blocks(blocks)
    print(f"(a) single-block exact: {'PASS' if not fa else 'FAIL ' + str(fa)}")

    n_crowns, c_fail, d_fail = assertion_cd_star_self()
    print(f"(b/c/d) star;star over 24 matchings: crowns={n_crowns}; "
          f"crown-has-no-2clock: {'PASS' if not c_fail else 'FAIL ' + str(c_fail)}; "
          f"fan-repaired: {'PASS' if not d_fail else 'FAIL ' + str(d_fail)}")

    crowns = heterogeneous_identity_crowns(blocks)
    m = len(crowns)
    k = sum(1 for (_, _, rescuers) in crowns if rescuers)
    print(f"finding: heterogeneous identity crowns: {m} distinct-block pairs crown under identity; "
          f"single-sync-repairable: {k}/{m}")


if __name__ == "__main__":
    main()

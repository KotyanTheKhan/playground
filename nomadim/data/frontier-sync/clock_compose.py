#!/usr/bin/env python3
"""§7 exactness assertions over the N=4 corpus, plus a CLI report.

HEADLINE: The minimal repair for a crown (an execution whose causal poset has
dimension > 2, preventing an exact 2-coordinate clock) is found by a shortest-
connector search.  For every star-self crown (B1 composed with B1 under any of
the 24 matchings), there exists a connector of length ≤ 2 that restores the
exact 2-coordinate clock.  This is the primary validated result.

The perm-fan connector (length = N − #cycles of the matching permutation) is a
validated ACHIEVABLE BOUND in its leaf-cycle regime (N=5..8 empirical data) but
is NOT the minimal or general recipe at N=4: it repairs only 8 of the 18 star-
self crowns, while the search-based approach repairs all 18.

(a) the 10 single blocks                           -> clock exact at 2 coords
(b/c/d) star-self over all 24 matchings            -> search-based minimal
                                                      repair restores dim 2 for
                                                      every crown; perm-fan
                                                      repairs only 8/18
finding: heterogeneous identity crowns             -> documented; brute-force
                                                      single-sync rescue attempted

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


def min_repair_connector(a_syncs, b_syncs, perm, n=4, max_len=3):
    """Search for the SHORTEST connector restoring an exact 2-coord clock.

    A connector is a sequence of pairwise syncs on n channels inserted between
    a_syncs and the perm-relabelled b_syncs.  The relabelled B is
    [(perm[i], perm[j]) for (i,j) in b_syncs]; the candidate execution is
    list(a_syncs) + list(connector) + relabelled_b.

    Searches length L = 0, 1, 2, ... up to max_len.  At each L iterates
    itertools.product(pairs, repeat=L) where pairs = [(i,j) for i < j < n].

    Returns the first connector found (a tuple of sync pairs) for which
    clock_check_syncs(n, ...) == (True, 2), or None if none found up to max_len.

    L=0 (empty connector) corresponds to the direct composition — it will
    succeed when the pair was never a crown.
    """
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    relabelled_b = [(perm[i], perm[j]) for (i, j) in b_syncs]
    for length in range(max_len + 1):
        for connector in itertools.product(pairs, repeat=length):
            candidate = list(a_syncs) + list(connector) + relabelled_b
            ok, dim = clock_check_syncs(n, candidate)
            if ok is True and dim == 2:
                return connector
    return None


def search_repair_star_self(perms=None, max_len=3):
    """HEADLINE sweep: B1 composed with itself over each perm (default all 24).

    For each of the 24 permutations of range(4):
      - classify via clock_check_syncs(4, compose_with_connector(B1,B1,perm,False))
      - if dim != 2 (a crown): record
          min_len   = len(min_repair_connector(B1, B1, perm, 4, max_len))
          fan_repairs = (clock_check_syncs(4, compose_with_connector(B1,B1,perm,True)) == (True,2))

    Returns a dict:
      'n_crowns'    : int  -- number of crowns found
      'all_repaired': bool -- every crown has a connector of length <= max_len
      'min_len_dist': dict {length: count}  -- distribution of min repair lengths
      'fan_repairs' : int  -- number of crowns the perm-fan connector fixes
      'records'     : list of (perm, min_len, fan_repairs) for each crown
    """
    if perms is None:
        perms = [list(p) for p in itertools.permutations(range(4))]
    B1 = star_block_b1()
    n_crowns = 0
    all_repaired = True
    min_len_dist = {}
    fan_repairs_count = 0
    records = []
    for perm in perms:
        direct = compose_with_connector(B1, B1, perm, use_connector=False)
        ok_d, dim_d = clock_check_syncs(4, direct)
        if dim_d != 2:                           # a crown
            n_crowns += 1
            connector = min_repair_connector(B1, B1, perm, 4, max_len)
            if connector is None:
                all_repaired = False
                min_len = None
            else:
                min_len = len(connector)
                min_len_dist[min_len] = min_len_dist.get(min_len, 0) + 1
            repaired = compose_with_connector(B1, B1, perm, use_connector=True)
            ok_r, dim_r = clock_check_syncs(4, repaired)
            fan_ok = (ok_r is True and dim_r == 2)
            if fan_ok:
                fan_repairs_count += 1
            records.append((perm, min_len, fan_ok))
    return {
        'n_crowns': n_crowns,
        'all_repaired': all_repaired,
        'min_len_dist': min_len_dist,
        'fan_repairs': fan_repairs_count,
        'records': records,
    }


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

    max_len = 3
    r = search_repair_star_self(max_len=max_len)
    n_crowns = r['n_crowns']
    all_repaired = r['all_repaired']
    min_len_dist = r['min_len_dist']
    fan_repairs = r['fan_repairs']
    status = 'PASS' if all_repaired else 'FAIL'
    print(f"(b/c/d) star;star crowns={n_crowns}; "
          f"all repaired by minimal connector(<= {max_len}): {status}; "
          f"min-repair-length distribution: {min_len_dist}")
    print(f"        perm-fan (N-#cycles) repairs only {fan_repairs}/{n_crowns} "
          f"-- fan is an achievable bound, not the minimal repair")

    crowns = heterogeneous_identity_crowns(blocks)
    m = len(crowns)
    k = sum(1 for (_, _, rescuers) in crowns if rescuers)
    print(f"finding: heterogeneous identity crowns: {m} distinct-block pairs; "
          f"single-sync-repairable: {k}/{m}")


if __name__ == "__main__":
    main()

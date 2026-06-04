import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import extract_realizer

def test_realizer_of_two_chains():
    # Two disjoint 2-chains: 0<1, 2<3. Dimension 2. Incomparable pairs:
    # {0,2},{0,3},{1,2},{1,3}. A 2-realizer must exist.
    nv, edges = 4, [(0, 1), (2, 3)]
    L1, L2 = extract_realizer(nv, edges)
    # Each Lk is a list giving each vertex's position (a permutation of 0..nv-1)
    assert sorted(L1) == [0, 1, 2, 3]
    assert sorted(L2) == [0, 1, 2, 3]
    # Both extensions must respect the edges (u before v)
    for (u, v) in edges:
        assert L1[u] < L1[v]
        assert L2[u] < L2[v]

def test_realizer_none_for_crown():
    # Standard 3-crown (S3): a_i < b_j for i != j. Dimension 3 -> no 2-realizer.
    # Vertices 0,1,2 = a0,a1,a2 ; 3,4,5 = b0,b1,b2. Edge a_i -> b_j when i != j.
    nv = 6
    edges = [(i, 3 + j) for i in range(3) for j in range(3) if i != j]
    assert extract_realizer(nv, edges) is None

from clock_realizer import clock_of, clock_is_exact

def test_clock_exact_two_chains():
    nv, edges = 4, [(0, 1), (2, 3)]
    clock = clock_of(nv, edges)            # dict v -> (c1, c2)
    assert clock is not None
    ok, bad = clock_is_exact(nv, edges, clock)
    assert ok, f"clock not exact: {bad}"

def test_clock_none_for_crown():
    nv = 6
    edges = [(i, 3 + j) for i in range(3) for j in range(3) if i != j]
    assert clock_of(nv, edges) is None     # dim 3 -> no 2-coord clock

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from hunt_n7 import PG
from clock_fan import compose_with_connector
from clock_realizer import clock_check_syncs

B1 = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]

def test_single_block_exact():
    # A single dim-2 star block: clock exists and is exact.
    ok, dim = clock_check_syncs(4, B1)
    assert dim == 2 and ok is True

def test_crown_fails_at_two_coords():
    # B1 composed with itself, swap 2<->3, NO connector -> crown (dim 3).
    syncs = compose_with_connector(B1, B1, [0, 1, 3, 2], use_connector=False)
    ok, dim = clock_check_syncs(4, syncs)
    assert dim == 3            # no 2-coord clock exists
    assert ok is None          # clock_of returned None -> not exact, by absence

def test_fan_repair_exact_again():
    # Same crown, but with the (2,3) repairing connector -> dim 2, exact.
    syncs = compose_with_connector(B1, B1, [0, 1, 3, 2], use_connector=True)
    ok, dim = clock_check_syncs(4, syncs)
    assert dim == 2 and ok is True

from clock_compose import load_blocks, assertion_a_single_blocks

def test_assertion_a_all_blocks_exact():
    blocks = load_blocks()
    assert len(blocks) == 10               # the 10 N=4 S=5 dim-2 blocks
    failures = assertion_a_single_blocks(blocks)
    assert failures == [], f"blocks not exact: {failures}"

if __name__ == "__main__":
    test_realizer_of_two_chains(); print("PASS two_chains")
    test_realizer_none_for_crown(); print("PASS crown_none")
    test_clock_exact_two_chains(); print("PASS clock_exact")
    test_clock_none_for_crown(); print("PASS clock_none")
    test_single_block_exact(); print("PASS single_block")
    test_crown_fails_at_two_coords(); print("PASS crown_fail")
    test_fan_repair_exact_again(); print("PASS fan_repair")
    test_assertion_a_all_blocks_exact(); print("PASS assertion_a")

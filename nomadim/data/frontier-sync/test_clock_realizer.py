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

if __name__ == "__main__":
    test_realizer_of_two_chains(); print("PASS two_chains")
    test_realizer_none_for_crown(); print("PASS crown_none")

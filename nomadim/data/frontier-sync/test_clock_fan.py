import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_fan import cycles_of, fan_connector
from clock_fan import compose_with_connector

def test_cycles_identity():
    assert sorted(map(sorted, cycles_of([0, 1, 2, 3]))) == [[0], [1], [2], [3]]

def test_cycles_swap():
    # swap channels 2 and 3: perm[2]=3, perm[3]=2
    cyc = cycles_of([0, 1, 3, 2])
    assert sorted(map(sorted, cyc)) == [[0], [1], [2, 3]]

def test_fan_identity_empty():
    # identity matching: no crossings -> empty (trivial) fan
    assert fan_connector([0, 1, 2, 3]) == []

def test_fan_swap_one_sync():
    # one transposition (2 3) -> exactly one repairing sync on the crossed pair
    assert fan_connector([0, 1, 3, 2]) == [(2, 3)]

def test_fan_3cycle_two_syncs():
    # 3-cycle (1 2 3): perm[1]=2, perm[2]=3, perm[3]=1 -> fan rooted at 1
    fan = fan_connector([0, 2, 3, 1])
    assert len(fan) == 2                       # N - #cycles = 4 - 2 = 2
    assert all(1 in s for s in fan)            # rooted at the cycle's min

def test_compose_direct_swap():
    # B1 star block; compose with itself, swap channels 2<->3, NO connector.
    A = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]
    perm = [0, 1, 3, 2]
    syncs = compose_with_connector(A, A, perm, use_connector=False)
    # A's 5 syncs, then B's 5 syncs relabeled by perm, no connector in between.
    assert syncs[:5] == A
    assert syncs[5:] == [(perm[i], perm[j]) for (i, j) in A]

def test_compose_with_fan_inserts_connector():
    A = [(0, 1), (0, 2), (0, 3), (0, 2), (0, 1)]
    perm = [0, 1, 3, 2]                        # swap 2<->3 -> fan [(2,3)]
    syncs = compose_with_connector(A, A, perm, use_connector=True)
    assert syncs[:5] == A
    assert syncs[5] == (2, 3)                  # the one repairing sync
    assert syncs[6:] == [(perm[i], perm[j]) for (i, j) in A]

if __name__ == "__main__":
    test_cycles_identity(); print("PASS cycles_identity")
    test_cycles_swap(); print("PASS cycles_swap")
    test_fan_identity_empty(); print("PASS fan_identity")
    test_fan_swap_one_sync(); print("PASS fan_swap")
    test_fan_3cycle_two_syncs(); print("PASS fan_3cycle")
    test_compose_direct_swap(); print("PASS compose_direct")
    test_compose_with_fan_inserts_connector(); print("PASS compose_fan")

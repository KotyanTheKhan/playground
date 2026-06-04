import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_fan import cycles_of, fan_connector

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

if __name__ == "__main__":
    test_cycles_identity(); print("PASS cycles_identity")
    test_cycles_swap(); print("PASS cycles_swap")
    test_fan_identity_empty(); print("PASS fan_identity")
    test_fan_swap_one_sync(); print("PASS fan_swap")
    test_fan_3cycle_two_syncs(); print("PASS fan_3cycle")

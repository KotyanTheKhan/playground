#!/usr/bin/env python3
"""Generate several LONG-RUNNING N=4 dimension-2 executions, by the repair-clock
theory: stack fully-synced dim-2 blocks joined by repairing-sync connectors, so
the whole (arbitrarily long) execution keeps an exact 2-coordinate clock. Every
emitted execution is verified dim 2 by the z3 oracle (clock_check_syncs) before
it is written. Output: long_examples/*.yaml + long_examples/INDEX.md.
"""
import os, sys, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from clock_realizer import clock_check_syncs, pg_of, extract_realizer
from clock_fan import compose_with_connector

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "long_examples")
B1 = [(0,1),(0,2),(0,3),(0,2),(0,1)]   # star (hub 0)
B9 = [(0,1),(2,3),(0,2),(0,1),(2,3)]   # two-pairs
PAIRS = [(i,j) for i in range(4) for j in range(i+1,4)]

def min_conn(prefix, block, perm, max_len=2):
    rel = [(perm[i],perm[j]) for (i,j) in block]
    for L in range(0, max_len+1):
        for combo in itertools.product(PAIRS, repeat=L):
            if clock_check_syncs(4, list(prefix)+list(combo)+rel) == (True,2):
                return list(combo), rel
    return None, None

def build_chain(blocks, perms, max_len=2):
    s = list(blocks[0]); conns = []
    for blk, perm in zip(blocks[1:], perms):
        conn, rel = min_conn(s, blk, perm, max_len)
        if conn is None:
            raise RuntimeError("seam not repairable within max_len")
        s = s + conn + rel; conns.append(conn)
    return s, conns

def write_yaml(name, syncs, note):
    ok, dim = clock_check_syncs(4, syncs)
    assert dim == 2 and ok is True, f"{name} NOT dim2 (got {(ok,dim)})"
    nv = pg_of(4, syncs)[0]
    path = os.path.join(OUT, name + ".yaml")
    with open(path, "w") as f:
        f.write("execution:\n  n_procs: 4\n  syncs:\n")
        for a,b in syncs:
            f.write(f"    - [{a}, {b}]\n")
        f.write("meta:\n")
        f.write(f'  notes: "{note} S={len(syncs)} events={nv}. z3-verified dim 2 -> exact 2-coordinate clock."\n')
        f.write("  dimension: 2\n")
    return len(syncs), nv

def repeat(block, k):
    s = []
    for _ in range(k): s += block
    return s

ROT = [0,2,3,1]   # leaf 3-cycle (a crossing)
SWAP = [0,1,3,2]  # leaf transposition (a crossing)

def main():
    os.makedirs(OUT, exist_ok=True)
    rows = []
    t0 = time.time()
    # A: repeated star, identity seams (homogeneous, stays dim2)
    for k, tag in [(3,"01"),(6,"02"),(10,"03")]:
        n,nv = write_yaml(f"N4_long_repeatstar_x{k}_{tag}", repeat(B1,k),
            f"Repeated star block B1 x{k} (identity seams).")
        rows.append((f"N4_long_repeatstar_x{k}_{tag}", n, nv, "repeated star, identity seams"))
    # B: heterogeneous B1/B9 alternating chain, repaired
    blocksB = [B1,B9]*4; permsB=[[0,1,2,3]]*7
    sB,_ = build_chain(blocksB, permsB)
    n,nv = write_yaml("N4_long_hetchain_b1b9_01", sB,
        "Alternating B1;B9 chain (8 blocks), minimal repairing connectors per seam.")
    rows.append(("N4_long_hetchain_b1b9_01", n, nv, "B1/B9 alternating, repaired"))
    # C: rotating-star chains, every seam a CROSSING repaired to dim2 (the showcase)
    for k, tag in [(5,"01"),(8,"02")]:
        blocks=[B1]*k; perms=[ROT,SWAP]*((k-1)//2+1)
        sC, conns = build_chain(blocks, perms[:k-1])
        n,nv = write_yaml(f"N4_long_rotstar_x{k}_{tag}", sC,
            f"Rotating-star chain B1 x{k}: each seam applies a CROSSING (3-cycle/swap) "
            f"repaired by a minimal connector ({sum(len(c) for c in conns)} repair syncs total).")
        rows.append((f"N4_long_rotstar_x{k}_{tag}", n, nv, "rotating-star, crossings repaired"))
    # INDEX
    with open(os.path.join(OUT,"INDEX.md"),"w") as f:
        f.write("# Long-running N=4 dimension-2 executions\n\n")
        f.write("Built by the repair-clock theory: fully-synced dim-2 blocks (star `B1`, "
                "two-pairs `B9`) stacked through repairing-sync connectors so the whole "
                "execution keeps an exact **2-coordinate clock** no matter how long it runs. "
                "Every file is **z3-verified dim 2**. Generator: `gen_long_examples.py`.\n\n")
        f.write("| file | syncs | events | construction |\n|---|---|---|---|\n")
        for name,n,nv,desc in rows:
            f.write(f"| `{name}.yaml` | {n} | {nv} | {desc} |\n")
        f.write(f"\nAll verified in {time.time()-t0:.1f}s by `clock_check_syncs` "
                "(z3: poset = intersection of two linear extensions, AND the rank-pair "
                "clock reproduces happened-before exactly).\n")
    print("wrote", len(rows), "examples to", OUT)
    for r in rows: print("  ", r)

if __name__ == "__main__":
    main()

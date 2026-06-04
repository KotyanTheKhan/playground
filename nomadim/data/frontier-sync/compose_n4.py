#!/usr/bin/env python3
"""Composition of minimum dimension-2 fully-synchronized N=4 executions.

Building blocks (mPsi4 dim2): the 10 minimum (S=5) dimension-2 fully frontier-
synchronized executions of N=4 processes. We COMPOSE two of them, A then B, by
gluing A's output frontier (its 4 end events) to B's input frontier (its 4 start
events). In the sync model this is just: run A's 5 syncs, then B's 5 syncs on the
same 4 processes -- a 10-sync execution that is automatically fully synchronized
(A already fully syncs; B continues). The frontier is an unordered set of 4
channels, so we try all 4! ways to wire A's outputs to B's inputs (relabel B's
processes by a permutation pi); A->B is "dim-2 composable" if ANY matching keeps
the composition dimension 2. (For N=4 the dimension is always 2 or 3, so dim 3 is
the "crown" case that breaks dim-2 closure.)

Output: the dim-2-preserving composition relation (for every A, which B compose
to dim 2), the overall distribution, and saved example compositions.
"""
import os, sys, glob, re, subprocess, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from confirm_dim import reachable_closure, build_smt
from hunt_n7 import build, full_synced

HERE = os.path.dirname(os.path.abspath(__file__))


def is_dim2(nv, edges):
    reach = reachable_closure(nv, edges)
    r = subprocess.run(["z3", "-in"], input=build_smt(nv, edges, reach, 2),
                       capture_output=True, text=True)
    return r.stdout.strip().split("\n")[0] == "sat"


def load_blocks():
    blocks = []
    # canonical order: real4_01..08 then real16_09,10
    files = sorted(glob.glob(os.path.join(HERE, "N4_S5_dim2_*.yaml")),
                   key=lambda f: (0 if "real4" in f else 1, f))
    for f in files:
        body = open(f).read().split("meta:")[0]
        syncs = [(int(a), int(b)) for a, b in
                 re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)]
        blocks.append((os.path.basename(f).replace(".yaml", ""), syncs))
    return blocks


def compose(a_syncs, b_syncs, perm):
    return list(a_syncs) + [(perm[i], perm[j]) for (i, j) in b_syncs]


def write_example(path, syncs, dim, note):
    with open(path, "w") as f:
        f.write("execution:\n  n_procs: 4\n  syncs:\n")
        for a, b in syncs:
            f.write(f"    - [{a}, {b}]\n")
        f.write("meta:\n")
        f.write(f"  notes: \"{note}\"\n")
        f.write(f"  dimension: {dim}\n")


def main():
    blocks = load_blocks()
    n = len(blocks)
    labels = [f"B{i+1}" for i in range(n)]
    print(f"{n} building blocks (mPsi4 dim2): " +
          ", ".join(f"{labels[i]}={blocks[i][0]}" for i in range(n)))

    perms = list(itertools.permutations(range(4)))
    # relation[i][j] = number of matchings (out of 24) whose composition is dim 2
    dim2_matchings = [[0] * n for _ in range(n)]
    total_compositions = 0
    dim2_total = 0
    example_good = None
    example_crown = None

    for i in range(n):
        for j in range(n):
            for pi in perms:
                syncs = compose(blocks[i][1], blocks[j][1], pi)
                g = build(syncs, 4)
                ok, _ = full_synced(g)
                assert ok, f"composition {labels[i]};{labels[j]} not fully synced!"
                total_compositions += 1
                if is_dim2(g.nv, g.edges):
                    dim2_matchings[i][j] += 1
                    dim2_total += 1
                    if example_good is None:
                        example_good = (i, j, pi, syncs)
                else:
                    if example_crown is None:
                        example_crown = (i, j, pi, syncs)
        print(f"  ...{labels[i]} done", flush=True)

    # dim-2-composable relation (some matching keeps dim 2)
    composable = [[dim2_matchings[i][j] > 0 for j in range(n)] for i in range(n)]

    print("\n================ RESULTS ================")
    print(f"composition: A then B, all 24 frontier matchings; "
          f"{total_compositions} compositions total "
          f"({dim2_total} dim 2, {total_compositions-dim2_total} dim 3).")

    print("\ndim-2-composable relation  (row A -> which B keep dim 2 via some matching):")
    header = "      " + " ".join(f"{labels[j]:>3}" for j in range(n))
    print(header)
    for i in range(n):
        cells = " ".join(("  2" if composable[i][j] else "  .") for j in range(n))
        print(f"  {labels[i]:>3} {cells}")

    print("\nfor every A, the B's that compose (A then B) to dimension 2:")
    for i in range(n):
        good = [labels[j] for j in range(n) if composable[i][j]]
        print(f"  {labels[i]}: {{{', '.join(good)}}}  ({len(good)}/{n})")

    # how many ORDERED pairs are dim-2 composable, and always/never
    pairs_some = sum(composable[i][j] for i in range(n) for j in range(n))
    pairs_all = sum(dim2_matchings[i][j] == 24 for i in range(n) for j in range(n))
    pairs_none = sum(dim2_matchings[i][j] == 0 for i in range(n) for j in range(n))
    print(f"\nordered pairs (100): dim-2 via some matching = {pairs_some}; "
          f"via ALL 24 matchings = {pairs_all}; never (always crown) = {pairs_none}.")

    # save examples
    if example_good:
        i, j, pi, syncs = example_good
        write_example(os.path.join(HERE, "N4_compose_dim2_example.yaml"), syncs, 2,
            f"Composition {labels[i]} then {labels[j]} (frontier matching pi={pi}) of two "
            f"minimum dim-2 N=4 executions; the composed S=10 fully-synchronized execution "
            f"stays DIMENSION 2 -- a dim-2-preserving (Ferrers/threshold-type) composition.")
        print(f"\nsaved dim-2 example: {labels[i]};{labels[j]} pi={pi} -> N4_compose_dim2_example.yaml")
    if example_crown:
        i, j, pi, syncs = example_crown
        write_example(os.path.join(HERE, "N4_compose_dim3_crown_example.yaml"), syncs, 3,
            f"Composition {labels[i]} then {labels[j]} (frontier matching pi={pi}) of two "
            f"minimum dim-2 N=4 executions whose composed S=10 fully-synchronized execution "
            f"is DIMENSION 3 -- the gluing creates a crown that raises the dimension, so "
            f"dim-2 is NOT preserved by this composition.")
        print(f"saved dim-3 'crown' example: {labels[i]};{labels[j]} pi={pi} -> N4_compose_dim3_crown_example.yaml")


if __name__ == "__main__":
    main()

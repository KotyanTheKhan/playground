#!/usr/bin/env python3
"""Enumerate all 63 unlabeled posets on 5 elements (OEIS A000112).

Phase A1 of the dimension_finish completion plan.  Builds:
 - Canonical iso classes for every non-antichain non-chain poset on 5 elements
   (expected count: 61).
 - Coverage report against the dispatcher cascade in
   posets/dimension/N5Realizers.v.
 - The list of iso classes still missing from the dispatcher (Phase A2 input).

This module uses only the Python 3 standard library (no networkx) because the
environment lacks third-party packages.  Iso-canonicalization is brute force
over the 5! = 120 permutations of {0,1,2,3,4}: well below performance limits.
"""

from __future__ import annotations

import re
import sys
from itertools import combinations, permutations, product
from pathlib import Path

N = 5
NODES = tuple(range(N))
PAIRS = tuple(combinations(NODES, 2))  # 10 unordered pairs
ALL_PERMS = tuple(permutations(NODES))


# -----------------------------------------------------------------------------
# Poset utilities (no networkx).
# -----------------------------------------------------------------------------


def is_transitively_closed(edges: frozenset[tuple[int, int]]) -> bool:
    """Return True if `edges` is closed under transitivity."""
    succ: dict[int, set[int]] = {v: set() for v in NODES}
    for a, b in edges:
        succ[a].add(b)
    for a in NODES:
        # BFS/DFS from a.
        reachable: set[int] = set()
        stack = list(succ[a])
        while stack:
            v = stack.pop()
            if v in reachable:
                continue
            reachable.add(v)
            stack.extend(succ[v])
        # Every reachable node must already be a direct successor of a.
        if not reachable.issubset(succ[a]):
            return False
    return True


def is_acyclic(edges: frozenset[tuple[int, int]]) -> bool:
    """Return True if the directed graph has no cycles.

    Sufficient for posets where edges are strict (no self-loops).
    """
    succ: dict[int, set[int]] = {v: set() for v in NODES}
    for a, b in edges:
        if a == b:
            return False
        succ[a].add(b)
    # Tarjan-free topological check: iterative Kahn.
    indeg = {v: 0 for v in NODES}
    for a, b in edges:
        indeg[b] += 1
    queue = [v for v in NODES if indeg[v] == 0]
    visited = 0
    while queue:
        v = queue.pop()
        visited += 1
        for w in succ[v]:
            indeg[w] -= 1
            if indeg[w] == 0:
                queue.append(w)
    return visited == N


def permute_edges(edges: frozenset[tuple[int, int]],
                  perm: tuple[int, ...]) -> frozenset[tuple[int, int]]:
    return frozenset((perm[a], perm[b]) for a, b in edges)


def canonical_form(edges: frozenset[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
    """Pick the lexicographically smallest sorted edge tuple over all
    relabelings of the carrier {0..4}."""
    best: tuple[tuple[int, int], ...] | None = None
    for perm in ALL_PERMS:
        candidate = tuple(sorted(permute_edges(edges, perm)))
        if best is None or candidate < best:
            best = candidate
    assert best is not None
    return best


# -----------------------------------------------------------------------------
# Step 1: enumerate all n=5 posets.
# -----------------------------------------------------------------------------


def enumerate_n5_posets() -> list[frozenset[tuple[int, int]]]:
    """Generate one representative (canonical form) per iso class."""
    seen: set[tuple[tuple[int, int], ...]] = set()
    reps: list[frozenset[tuple[int, int]]] = []
    # For each unordered pair {a,b} with a < b: 3 choices (a→b, b→a, neither).
    for assignment in product((0, 1, 2), repeat=len(PAIRS)):
        edges: set[tuple[int, int]] = set()
        for (a, b), opt in zip(PAIRS, assignment):
            if opt == 0:
                edges.add((a, b))
            elif opt == 1:
                edges.add((b, a))
            # opt == 2: no relation between a and b.
        edges_fs = frozenset(edges)
        if not is_acyclic(edges_fs):
            continue
        if not is_transitively_closed(edges_fs):
            continue
        canon = canonical_form(edges_fs)
        if canon in seen:
            continue
        seen.add(canon)
        reps.append(frozenset(canon))
    return reps


def is_antichain(edges: frozenset[tuple[int, int]]) -> bool:
    return len(edges) == 0


def is_chain(edges: frozenset[tuple[int, int]]) -> bool:
    # 5-chain transitive closure has C(5,2) = 10 edges.
    return len(edges) == N * (N - 1) // 2


# -----------------------------------------------------------------------------
# Step 2: parse N5Realizers.v dispatcher branches.
# -----------------------------------------------------------------------------


# Match each `destruct (classic (exists a b c d e : B, ... )) as [Hx | HnX].`
# block.  The predicate body lies between `exists a b c d e : B,` and the
# trailing `(forall x y : B,` clause.  We extract the `R2 ? ?` edge atoms only
# from the conjunction-of-direct-edges section that precedes the `forall`.
EXISTS_OPENER = re.compile(
    r"destruct \(classic\s*"
    r"\(exists a b c d e : B,\s*"
    r"(?P<body>.*?)"
    r"\(forall x y : B,",
    re.DOTALL,
)
# Pull the dispatcher lemma name from the next `apply (@<name>` after the
# matched `destruct`.
APPLY_RE = re.compile(r"apply\s*\(@\s*(?P<lemma>[A-Za-z0-9_]+)\b")
R2_EDGE_RE = re.compile(r"R2\s+([abcde])\s+([abcde])")

NAME_TO_IDX = {"a": 0, "b": 1, "c": 2, "d": 3, "e": 4}


def parse_dispatcher(path: Path) -> list[dict]:
    text = path.read_text()
    branches: list[dict] = []
    for m in EXISTS_OPENER.finditer(text):
        body = m.group("body")
        # Collect raw R2 edges from this branch's conjunction.
        edges_named = R2_EDGE_RE.findall(body)
        if not edges_named:
            continue
        edges: set[tuple[int, int]] = set()
        for x, y in edges_named:
            edges.add((NAME_TO_IDX[x], NAME_TO_IDX[y]))
        edges_fs = frozenset(edges)
        # Find the lemma name applied right after this destruct (search forward
        # within ~2000 characters; dispatcher branches are typically very
        # short).
        end = m.end()
        window = text[end:end + 2000]
        lemma_match = APPLY_RE.search(window)
        lemma = lemma_match.group("lemma") if lemma_match else "<unknown>"
        branches.append({
            "raw_edges": edges_fs,
            "lemma": lemma,
            "offset": m.start(),
        })
    return branches


def transitive_closure(edges: frozenset[tuple[int, int]]) -> frozenset[tuple[int, int]]:
    """Compute the reflexive-irreflexive transitive closure."""
    succ: dict[int, set[int]] = {v: set() for v in NODES}
    for a, b in edges:
        succ[a].add(b)
    changed = True
    while changed:
        changed = False
        for a in NODES:
            new = set()
            for b in succ[a]:
                new |= succ[b]
            for v in new:
                if v != a and v not in succ[a]:
                    succ[a].add(v)
                    changed = True
    return frozenset((a, b) for a in NODES for b in succ[a])


# -----------------------------------------------------------------------------
# Main: produce coverage report.
# -----------------------------------------------------------------------------


def main() -> None:
    repo_root = Path("/Users/maxstarling/code/research/playground")
    scripts_dir = repo_root / "scripts"
    n5_path = repo_root / "posets" / "dimension" / "N5Realizers.v"

    posets = enumerate_n5_posets()
    print(f"Total n=5 posets: {len(posets)}")

    non_trivial = [p for p in posets if not is_antichain(p) and not is_chain(p)]
    print(f"Non-antichain non-chain: {len(non_trivial)}")

    # Sort the canonical reps by (edge count, edges) for stable output.
    non_trivial_sorted = sorted(
        non_trivial, key=lambda e: (len(e), tuple(sorted(e)))
    )
    # Build canonical form -> stable class id (1..N).
    class_by_canon: dict[tuple[tuple[int, int], ...], int] = {}
    canon_for: dict[int, tuple[tuple[int, int], ...]] = {}
    for i, edges in enumerate(non_trivial_sorted, start=1):
        canon = canonical_form(edges)
        class_by_canon[canon] = i
        canon_for[i] = canon

    # Dump all 61 classes.
    all_path = scripts_dir / "iso_classes_all.txt"
    with all_path.open("w") as f:
        f.write(f"# All non-antichain non-chain iso classes on n=5 (count={len(non_trivial_sorted)})\n")
        f.write("# Format: Class <id> | edges = <canonical-direct-edges>\n")
        for i, edges in enumerate(non_trivial_sorted, start=1):
            canon = canon_for[i]
            f.write(f"Class {i:3d} | |E|={len(canon):2d} | edges = {list(canon)}\n")
    print(f"Wrote {all_path}")

    # Parse dispatcher.
    branches = parse_dispatcher(n5_path)
    print(f"Parsed dispatcher branches: {len(branches)}")

    covered_classes: dict[int, list[str]] = {}
    unknown_branches: list[dict] = []
    for br in branches:
        # Each branch's raw_edges are the "direct" edges asserted by the
        # predicate; the iso class is determined by the transitive closure of
        # those edges.  In all dispatcher branches the direct conjunction is
        # already the transitive closure, but we close defensively in case a
        # future branch lists only the cover relation.
        closed = transitive_closure(br["raw_edges"])
        canon = canonical_form(closed)
        cid = class_by_canon.get(canon)
        if cid is None:
            unknown_branches.append({**br, "canon": canon, "closed": closed})
            continue
        covered_classes.setdefault(cid, []).append(br["lemma"])

    # Class 1 (single edge) is handled outside the destruct cascade by
    # [n5_one_edge_two_realizer], reached via the explicit fall-through at the
    # bottom of the dispatcher (after [Honly]).  Mark it as covered.
    one_edge_canon = canonical_form(frozenset({(0, 1)}))
    one_edge_cid = class_by_canon.get(one_edge_canon)
    if one_edge_cid is not None and one_edge_cid not in covered_classes:
        covered_classes[one_edge_cid] = ["n5_one_edge_two_realizer (fall-through)"]

    covered_path = scripts_dir / "iso_classes_covered.txt"
    with covered_path.open("w") as f:
        f.write(f"# Iso classes covered by N5Realizers.v dispatcher\n")
        f.write(f"# (count={len(covered_classes)} of {len(non_trivial_sorted)})\n")
        f.write("# Format: Class <id> | |E|=<count> | edges = ... | lemmas = [<names>]\n")
        for cid in sorted(covered_classes):
            edges = canon_for[cid]
            f.write(
                f"Class {cid:3d} | |E|={len(edges):2d} | edges = {list(edges)} "
                f"| lemmas = {covered_classes[cid]}\n"
            )
    print(f"Wrote {covered_path}")

    missing_ids = sorted(set(canon_for.keys()) - set(covered_classes.keys()))
    missing_path = scripts_dir / "iso_classes_missing.txt"
    with missing_path.open("w") as f:
        f.write(f"# Iso classes MISSING from N5Realizers.v dispatcher\n")
        f.write(f"# (count={len(missing_ids)})\n")
        f.write("# These are the iso classes that fall through to\n")
        f.write("# [n5_residual_classes_two_realizer] (Admitted), so they are the\n")
        f.write("# concrete targets for Phase A2.\n")
        f.write("# Format: Class <id> | |E|=<count> | edges = <canonical-direct-edges>\n")
        for cid in missing_ids:
            edges = canon_for[cid]
            f.write(f"Class {cid:3d} | |E|={len(edges):2d} | edges = {list(edges)}\n")
    print(f"Wrote {missing_path}")

    print()
    print(f"Total non-trivial n=5 iso classes: {len(non_trivial_sorted)}")
    print(f"Covered by N5Realizers.v dispatcher (incl. fall-through one_edge):"
          f" {len(covered_classes)}")
    print(f"Missing (route to n5_residual_classes_two_realizer admit):"
          f" {len(non_trivial_sorted)} - {len(covered_classes)} = {len(missing_ids)}")
    if unknown_branches:
        print()
        print(f"WARNING: {len(unknown_branches)} dispatcher branches did not match "
              "any enumerated iso class — likely due to typos, antichain branches, "
              "or out-of-canonical-form predicates.  See unknown_branches list "
              "below for inspection.")
        for br in unknown_branches:
            print(f"  - lemma={br['lemma']!r} raw_edges={sorted(br['raw_edges'])}")

    if missing_ids:
        print()
        print("Missing iso classes:")
        for cid in missing_ids:
            edges = canon_for[cid]
            print(f"  - Class {cid}: edges = {list(edges)}")


if __name__ == "__main__":
    main()

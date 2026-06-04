#!/usr/bin/env python3
"""Frontier matching -> repairing-sync fan connector. The matching is a
permutation perm (perm[i] = channel of A's output i wired to B's input). Its
cycle decomposition gives the fan: one repairing sync per transposition,
rooted at each cycle's minimum channel. Recovery length = N - #cycles
(see EXPLAINER_RESCUE.md). See spec S4/S6.
"""


def cycles_of(perm):
    """Cycle decomposition of perm (a list, perm[i] is the image of i)."""
    n = len(perm)
    seen = [False] * n
    cycles = []
    for i in range(n):
        if seen[i]:
            continue
        cyc, j = [], i
        while not seen[j]:
            seen[j] = True
            cyc.append(j)
            j = perm[j]
        cycles.append(cyc)
    return cycles


def fan_connector(perm):
    """List of repairing syncs (root, other) for each non-trivial cycle,
    rooted at the cycle's minimum. Length = sum(len(c)-1) = N - #cycles."""
    fan = []
    for cyc in cycles_of(perm):
        if len(cyc) <= 1:
            continue
        root = min(cyc)
        for c in cyc:
            if c != root:
                fan.append((root, c))
    return fan


def compose_with_connector(a_syncs, b_syncs, perm, use_connector=True):
    """Build the composed sync list A ; [connector fan] ; relabel(B).
    perm relabels B's channels (the frontier matching). When use_connector,
    the repairing-sync fan for perm is inserted between A and B.
    """
    connector = fan_connector(perm) if use_connector else []
    relabelled_b = [(perm[i], perm[j]) for (i, j) in b_syncs]
    return list(a_syncs) + connector + relabelled_b

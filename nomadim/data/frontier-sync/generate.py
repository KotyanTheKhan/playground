#!/usr/bin/env python3
"""Minimum-synchronization fully-frontier-synchronized executions for N = 2..5
processes, grouped by order dimension (dimensions are bounded by N).

"Fully frontier synchronized" means every process' *start* event is seen by
every process' *last* event (`is_full_synchronized` in src/enumerate.cpp): the
opening frontier is causally below the closing frontier in its entirety.

Method
------
For each N we run `nomadim enumerate --all-dims --with-dim -j 4` up to a sync
budget K. `--all-dims` keeps executions of every dimension; `--with-dim`
computes each shape's order dimension in-process (fast path: dimension only, no
realizer enumeration) and writes it to `meta.dimension`. Because the enumerator
stops expanding a branch as soon as it becomes fully synchronized, each shape's
`len(syncs)` is the number of syncs at which that branch first fully
synchronized.

We bucket the shapes by dimension and, for each dimension d that occurs, keep
the shapes at d's MINIMUM sync count -- the fewest syncs that fully synchronize
N processes into an order of dimension d. The budget K per N is chosen to reach
the dimension-2 minimum (dimension 2 is the lowest, and empirically the
costliest in syncs), which also captures every higher dimension (those occur at
fewer syncs). The realizer count (`nomadim dimension --all`, capped at 1000) is
computed only for the kept shapes.

One YAML file is written per kept shape, name encoding the statistics:

    N{n}_S{s}_dim{d}_real{r}_{idx}.yaml      (r = exact realizer count)
    N{n}_S{s}_dim{d}_real{r}cap_{idx}.yaml   (realizer count hit the 1000 cap)

Run from anywhere; paths are resolved relative to this file.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NOMADIM = os.path.normpath(os.path.join(HERE, "..", "..", "build", "nomadim"))
JOBS = "4"               # use only 4 cores, as requested
REALIZER_CAP = 1000      # Caps.max_results in hypergraph.hpp
MAX_VERTICES = "64"      # N=5,S=8 -> 5 + 2*8 = 21 vertices; head-room

# Sync budget per N: reaches the dimension-2 minimum, which also covers every
# higher dimension (they fully synchronize with fewer syncs). Empirically the
# only dimensions that occur for N<=5 are 2 and 3.
PER_N_BUDGET = {2: 2, 3: 3, 4: 5, 5: 7}


def run(args):
    return subprocess.run([NOMADIM, *args], capture_output=True, text=True, check=True)


def split_docs(text):
    """The enumerator joins docs with a glued '---' separator."""
    return [d.strip() for d in text.split("---") if d.strip()]


def parse_syncs(doc):
    body = doc.split("meta:")[0]            # syncs live in the execution block
    return re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", body)


def enumerate_with_dim(n, k):
    """Return [{syncs, s, dim}] for every non-iso fully-synced shape, S<=k."""
    combined = os.path.join(HERE, f"_n{n}k{k}.tmp.yaml")
    run(["enumerate", "-n", str(n), "-k", str(k), "-j", JOBS,
         "--all-dims", "--with-dim", "--max-vertices", MAX_VERTICES, "-o", combined])
    with open(combined) as f:
        docs = split_docs(f.read())
    os.remove(combined)
    shapes = []
    for d in docs:
        syncs = parse_syncs(d)
        dim = int(re.search(r"dimension:\s*(\d+)", d).group(1))
        shapes.append({"syncs": syncs, "s": len(syncs), "dim": dim})
    return shapes


def analyze_realizers(n, syncs):
    """Return (dimension, n_colorings, first_realizer, source_hash) via the full
    (coloring-enumerating) dimension analysis."""
    tmp = os.path.join(HERE, "_shape.tmp.yaml")
    with open(tmp, "w") as f:
        f.write(f"execution:\n  n_procs: {n}\n  syncs:\n")
        for a, b in syncs:
            f.write(f"    - [{a}, {b}]\n")
    out = run(["dimension", tmp, "--all", "--max-vertices", MAX_VERTICES]).stdout
    dim = int(re.search(r"Dimension:\s*(\d+)", out).group(1))
    ncol = int(re.search(r"Minimum colorings:\s*(\d+)", out).group(1))
    realizer = []
    in_first = False
    for line in out.splitlines():
        if re.match(r"\s*coloring 0:", line):
            in_first = True
            continue
        if in_first:
            m = re.match(r"\s*L\d+:\s*\[(.*)\]", line)
            if m:
                realizer.append([int(x) for x in m.group(1).split(",")])
            elif re.match(r"\s*coloring \d+:", line):
                break
    tmp_out = tmp + ".meta"
    run(["dimension", tmp, "--max-vertices", MAX_VERTICES, "-o", tmp_out])
    shash = ""
    with open(tmp_out) as f:
        for line in f:
            m = re.match(r"\s*source_hash:\s*\"?([0-9a-fx]+)\"?", line)
            if m:
                shash = m.group(1)
                break
    os.remove(tmp_out)
    os.remove(tmp)
    return dim, ncol, realizer, shash


def write_doc(path, n, s, syncs, dim, ncol, capped, realizer, shash, summary_note):
    notes = (
        f"Fully frontier-synchronized execution (every process start is seen by "
        f"every process last event), minimal for its dimension. N={n} processes, "
        f"S={s} synchronizations = the minimum number of syncs that fully "
        f"synchronizes {n} processes into an order of dimension {dim}. "
        f"Number of minimum realizers (colorings) = "
        f"{'>=' + str(REALIZER_CAP) + ' (cap reached)' if capped else str(ncol)}. "
        f"One example realizer is recorded below; {summary_note}"
    )
    with open(path, "w") as f:
        f.write("execution:\n")
        f.write(f"  n_procs: {n}\n")
        f.write("  syncs:\n")
        for a, b in syncs:
            f.write(f"    - [{a}, {b}]\n")
        f.write("meta:\n")
        f.write(f"  notes: \"{notes}\"\n")
        f.write(f"  dimension: {dim}\n")
        if shash:
            f.write(f"  source_hash: \"{shash}\"\n")
        f.write("  realizers:\n")
        f.write("    -\n")          # one example realizer (a list of `dim` extensions)
        for ext in realizer:
            f.write("      - [" + ", ".join(str(x) for x in ext) + "]\n")


def main():
    if not os.path.exists(NOMADIM):
        sys.exit(f"nomadim binary not found at {NOMADIM}; run `mise run nomadim-build` first")
    for old in os.listdir(HERE):
        if re.match(r"N\d+_S\d+_dim\d+_real.*\.yaml$", old):
            os.remove(os.path.join(HERE, old))

    rows = []
    for n in sorted(PER_N_BUDGET):
        k = PER_N_BUDGET[n]
        shapes = enumerate_with_dim(n, k)
        min_s = {}
        for a in shapes:
            min_s[a["dim"]] = min(min_s.get(a["dim"], 1 << 30), a["s"])
        kept = sorted((a for a in shapes if a["s"] == min_s[a["dim"]]),
                      key=lambda a: (a["dim"], tuple(a["syncs"])))
        dims = sorted(min_s)
        print(f"N={n} (budget K={k}): dimensions {dims}; "
              + ", ".join(f"dim{d} min S={min_s[d]}" for d in dims))
        idx_by_dim = {}
        for a in kept:
            dim, s, syncs = a["dim"], a["s"], a["syncs"]
            rdim, ncol, realizer, shash = analyze_realizers(n, syncs)
            assert rdim == dim, f"dimension mismatch {rdim} != {dim} for {syncs}"
            idx = idx_by_dim.get(dim, 0) + 1
            idx_by_dim[dim] = idx
            capped = ncol >= REALIZER_CAP
            rtag = f"{ncol}cap" if capped else str(ncol)
            fname = f"N{n}_S{s}_dim{dim}_real{rtag}_{idx:02d}.yaml"
            note = (
                "the full realizer set is large and capped at 1000 by the tool."
                if capped else
                f"all {ncol} minimum realizer(s) share this dimension."
            )
            write_doc(os.path.join(HERE, fname), n, s, syncs, dim, ncol, capped,
                      realizer, shash, note)
            rcell = ">=1000 (cap)" if capped else str(ncol)
            rows.append((n, dim, s, idx, rcell, fname, syncs))
        for dim in dims:
            tot = sum(1 for a in kept if a["dim"] == dim)
            print(f"  dim{dim} @ S={min_s[dim]}: {tot} shape(s)")
    write_summary(rows)


def write_summary(rows):
    # totals per (N, dim)
    totals = {}
    for n, dim, s, idx, rcell, fname, syncs in rows:
        totals[(n, dim)] = totals.get((n, dim), 0) + 1
    path = os.path.join(HERE, "SUMMARY.md")
    with open(path, "w") as f:
        f.write("# Minimum-synchronization fully frontier-synchronized executions\n\n")
        f.write(
            "An *execution* is `N` processes plus an ordered list of pairwise "
            "synchronizations. It is **fully frontier synchronized** when every "
            "process' start event is causally below every process' last event "
            "(`is_full_synchronized`): the whole opening frontier is seen by the "
            "whole closing frontier.\n\n"
            "Grouped by **order dimension** (dimensions are bounded by `N`). For "
            "each `N` and each dimension `d` that a fully-synchronized execution of "
            "`N` processes can have, `S` is the **minimum** number of "
            "synchronizations achieving dimension `d`; the rows are the distinct "
            "(non-isomorphic) executions at that `(d, S)`. Found with "
            "`nomadim enumerate --all-dims --with-dim -j 4`; realizer counts from "
            "`nomadim dimension --all` (capped at 1000).\n\n"
            "**Headline:** a higher dimension is *cheaper* in syncs. The minimum "
            "full synchronization of N processes is the highest-dimensional one; "
            "spending extra syncs lowers the dimension. Within `N <= 5` only "
            "dimensions 2 and 3 occur.\n\n"
        )
        f.write("| N | dimension | min S | # shapes | shape | # realizers | syncs | file |\n")
        f.write("|---|-----------|-------|----------|-------|-------------|-------|------|\n")
        for n, dim, s, idx, rcell, fname, syncs in rows:
            syncs_str = " ".join(f"({a},{b})" for a, b in syncs)
            f.write(f"| {n} | {dim} | {s} | {totals[(n,dim)]} | {idx} | {rcell} | "
                    f"{syncs_str} | `{fname}` |\n")
        f.write(
            "\nNotes:\n\n"
            "- Within `N <= 5` (and the sync budgets scanned) the only dimensions "
            "that occur are **2** and **3**; `N=2` and `N=3` are always dimension 2 "
            "(no dimension-3 execution of <=3 processes was found), and dimension 3 "
            "first appears at `N=4`.\n"
            "- A higher dimension needs *fewer* syncs: dim 3 fully synchronizes "
            "N=4 in 4 syncs / N=5 in 6 syncs, but dim 2 needs 5 / 7 respectively.\n"
            "- The default enumerator keeps only dimension <= 2, so it never sees "
            "the dimension-3 minimum shapes and over-reports the minimum S.\n"
            "- '# realizers' counts minimum colorings of the critical-pair "
            "hypergraph; `>=1000 (cap)` means the count reached the tool's 1000 cap.\n"
        )
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()

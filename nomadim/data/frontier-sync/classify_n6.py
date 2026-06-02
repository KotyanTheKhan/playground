#!/usr/bin/env python3
"""Decide "dimension <= K?" per shape, for posets whose exact dimension blows up
(N=6: 65+ critical pairs). Reads a multi-doc execution YAML (from `enumerate
-o`) and runs `nomadim dimension --le K` on each: that test early-exits on the
first valid K-coloring, so dim<=K shapes are cheap; only a genuine dim>K shape
is slow (it must exhaust the K-coloring search to prove none exists).

Outcome per shape: "yes" (dim<=K), "no" (dim>K -> a dimension>K shape is FOUND),
or "slow" (no K-coloring found within the timeout -> a dim>K *candidate*, since
proving non-K-colorability is the expensive case).

Usage: classify_n6.py <infile> <K> <timeout_s> <max_cpairs>
"""
import os, re, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
NOMADIM = os.path.normpath(os.path.join(HERE, "..", "..", "build", "nomadim"))
INFILE = sys.argv[1] if len(sys.argv) > 1 else "/tmp/fs/n6.yaml"
K = sys.argv[2] if len(sys.argv) > 2 else "3"
TIMEOUT = float(sys.argv[3]) if len(sys.argv) > 3 else 60.0
MAXCP = sys.argv[4] if len(sys.argv) > 4 else "8192"

docs = [d for d in open(INFILE).read().split("---") if "execution" in d]
tally = collections.Counter()
over = []     # dim > K (definitively)
slow = []     # could not prove dim <= K within timeout (dim > K candidate)
for i, d in enumerate(docs):
    syncs = re.findall(r"\[\s*(\d+)\s*,\s*(\d+)\s*\]", d.split("meta:")[0])
    nproc = re.search(r"n_procs:\s*(\d+)", d).group(1)
    tmp = f"/tmp/fs/_c{i}.yaml"
    with open(tmp, "w") as f:
        f.write(f"execution:\n  n_procs: {nproc}\n  syncs:\n")
        for a, b in syncs:
            f.write(f"    - [{a}, {b}]\n")
    try:
        out = subprocess.run([NOMADIM, "dimension", tmp, "--le", K,
                              "--max-vertices", "64", "--max-cpairs", MAXCP],
                             capture_output=True, text=True, timeout=TIMEOUT)
        m = re.search(rf"Dimension <= {K}:\s*(yes|no)", out.stdout)
        if m and m.group(1) == "yes":
            tally["dim<=" + K] += 1
        elif m and m.group(1) == "no":
            tally["dim>" + K] += 1
            over.append(syncs)
        else:
            tally["error"] += 1
    except subprocess.TimeoutExpired:
        tally["slow"] += 1
        slow.append(syncs)
    finally:
        os.remove(tmp)
    if (i + 1) % 20 == 0:
        print(f"  ...{i+1}/{len(docs)} done  (so far: {dict(tally)})", flush=True)

print(f"\nTested {len(docs)} shapes for dimension <= {K} (timeout {TIMEOUT}s, max-cpairs {MAXCP}):")
for k in sorted(tally, key=str):
    print(f"  {k}: {tally[k]}")
if over:
    print(f"\nDIMENSION > {K} FOUND ({len(over)} shape(s)):")
    for syncs in over:
        print("  " + " ".join(f"({a},{b})" for a, b in syncs))
else:
    print(f"\nNo shape proven to exceed dimension {K}.")
if slow:
    print(f"\n{len(slow)} shape(s) could not be proven dim<={K} within {TIMEOUT}s "
          f"(dimension > {K} candidates):")
    for syncs in slow[:20]:
        print("  slow: " + " ".join(f"({a},{b})" for a, b in syncs))

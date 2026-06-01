#!/usr/bin/env python3
"""Compare two Google Benchmark JSON outputs and gate on regression.

Usage: compare.py BASELINE.json CURRENT.json [--threshold 0.25] [--metric real_time]

Matches benchmarks by run_name using the median aggregate (produced by
--benchmark_repetitions=N --benchmark_report_aggregates_only=true). Exits 1 if any
benchmark's current metric exceeds baseline by more than the threshold fraction.
"""
import sys
import json
import argparse


def load_medians(path, metric):
    with open(path) as f:
        data = json.load(f)
    out = {}
    for b in data.get("benchmarks", []):
        if b.get("aggregate_name") == "median":
            out[b["run_name"]] = float(b[metric])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline")
    ap.add_argument("current")
    ap.add_argument("--threshold", type=float, default=0.25,
                    help="max allowed slowdown as a fraction (default 0.25 = 25%%)")
    ap.add_argument("--metric", default="real_time")
    args = ap.parse_args()

    base = load_medians(args.baseline, args.metric)
    cur = load_medians(args.current, args.metric)
    names = sorted(set(base) | set(cur))

    print("{:<28} {:>14} {:>14} {:>9}  {}".format(
        "benchmark", "baseline", "current", "delta", "verdict"))
    regressions = []
    missing = []
    for n in names:
        if n not in base:
            # New benchmark not in the baseline — informational, not a failure.
            print("{:<28} {:>14} {:>14.1f} {:>9}  warn".format(n, "-", cur[n], "NEW"))
            continue
        if n not in cur:
            # A baseline benchmark has no median in the current run. This happens
            # when a benchmark errored out (e.g. an enumerate count assertion via
            # SkipWithError suppresses its aggregates) — treat it as a failure so
            # a correctness regression cannot slip through the gate.
            print("{:<28} {:>14.1f} {:>14} {:>9}  FAIL".format(n, base[n], "-", "MISSING"))
            missing.append(n)
            continue
        b, c = base[n], cur[n]
        delta = (c - b) / b if b else 0.0
        verdict = "ok"
        if delta > args.threshold:
            verdict = "REGRESSION"
            regressions.append(n)
        elif delta < -args.threshold:
            verdict = "faster"
        print("{:<28} {:>14.1f} {:>14.1f} {:>+8.1f}%  {}".format(n, b, c, delta * 100, verdict))

    if regressions or missing:
        if regressions:
            print("\nFAIL: {} regression(s) over {:.0f}%: {}".format(
                len(regressions), args.threshold * 100, ", ".join(regressions)))
        if missing:
            print("FAIL: {} baseline benchmark(s) missing/errored in current run: {}".format(
                len(missing), ", ".join(missing)))
        return 1
    print("\nOK: no regression over {:.0f}% threshold".format(args.threshold * 100))
    return 0


if __name__ == "__main__":
    sys.exit(main())

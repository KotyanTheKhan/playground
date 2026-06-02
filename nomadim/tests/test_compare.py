import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

COMPARE = Path(__file__).resolve().parent.parent / "bench" / "compare.py"


def write_json(path, medians):
    """medians: dict name -> real_time. Writes a minimal Google Benchmark JSON."""
    data = {"benchmarks": [
        {"run_name": name, "aggregate_name": "median", "real_time": rt}
        for name, rt in medians.items()
    ]}
    with open(path, "w") as f:
        json.dump(data, f)


def run_compare(baseline, current, *extra):
    return subprocess.run(
        [sys.executable, str(COMPARE), baseline, current, *extra],
        capture_output=True, text=True)


class CompareTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.base = os.path.join(self.dir, "base.json")
        self.cur = os.path.join(self.dir, "cur.json")

    def test_identical_passes(self):
        write_json(self.base, {"a": 100.0, "b": 200.0})
        write_json(self.cur, {"a": 100.0, "b": 200.0})
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("OK", r.stdout)

    def test_regression_fails(self):
        write_json(self.base, {"a": 100.0})
        write_json(self.cur, {"a": 200.0})
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 1)
        self.assertIn("REGRESSION", r.stdout)

    def test_within_threshold_passes(self):
        write_json(self.base, {"a": 100.0})
        write_json(self.cur, {"a": 110.0})
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_missing_benchmark_fails(self):
        write_json(self.base, {"a": 100.0, "b": 200.0})
        write_json(self.cur, {"a": 100.0})
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 1)
        self.assertIn("MISSING", r.stdout)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env bash
# Run mise build with a hard timeout and bounded parallelism.
# Usage: timed-build.sh <seconds> <target> [jobs]
# [jobs] caps dune -j to bound memory (default 2). Memory-heavy proofs
#   (large cartesian destruct cascades) can each use several GB; the default
#   dune -j = ncpu launches one such worker per core and OOMs the machine.
# On timeout: kills mise, dune, coqc, rocqworker children + clears _build/.lock.
# Exit codes: 0 = success, 124 = timeout, other = build failure.
set +e
SECS="${1:-300}"
TARGET="${2:-}"
JOBS="${3:-2}"
if [[ -z "$TARGET" ]]; then
  echo "usage: timed-build.sh <seconds> <target> [jobs]" >&2
  exit 2
fi
DUNE_JOBS="$JOBS" mise run build "$TARGET" 2>&1 &
BP=$!
( sleep "$SECS"
  kill -9 "$BP" 2>/dev/null
  pkill -9 -f "rocqworker|coqc" 2>/dev/null
  pkill -P "$BP" 2>/dev/null
  rm -f _build/.lock
  echo "===KILLED at ${SECS}s===" >&2
  exit 124
) &
WP=$!
wait "$BP" 2>/dev/null
STATUS=$?
kill -9 "$WP" 2>/dev/null
exit $STATUS

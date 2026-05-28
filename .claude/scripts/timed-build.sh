#!/usr/bin/env bash
# Run mise build with a hard timeout.
# Usage: timed-build.sh <seconds> <target>
# On timeout: kills mise, dune, coqc, rocqworker children + clears _build/.lock.
# Exit codes: 0 = success, 124 = timeout, other = build failure.
set +e
SECS="${1:-300}"
TARGET="${2:-}"
if [[ -z "$TARGET" ]]; then
  echo "usage: timed-build.sh <seconds> <target>" >&2
  exit 2
fi
mise run build "$TARGET" 2>&1 &
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

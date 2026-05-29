#!/usr/bin/env bash
# Canonical build wrapper for this Coq project.
# EVERY build — single .v file, submodule dir, or the whole project — must go
# through this script. It enforces three safety limits:
#   1. a hard wall-clock timeout (build killed if exceeded),
#   2. bounded parallelism (dune -j), and
#   3. a memory watchdog (build killed if total worker RSS exceeds a cap).
#
# Why: dune's default -j = ncpu launches one rocqworker per core. Memory-heavy
# proofs (large cartesian destruct cascades) use several GB each, so the
# default fan-out exhausts RAM and crashes the machine. Low -j prevents it;
# the memory watchdog is the hard safety net when an estimate is wrong.
#
# Usage: timed-build.sh <seconds> <target> [jobs] [mem_mb]
#   <seconds>  hard wall-clock cap (required; per project rule, single files
#              that need >300s must be justified — see coq-fast-compile skill)
#   <target>   dune target: a path/to/File.vo, a submodule dir, or @all
#   [jobs]     dune -j parallelism (default 2; use 1 for memory-heavy cascades,
#              raise for many small light files)
#   [mem_mb]   kill build if total rocqworker+coqc RSS exceeds this MB
#              (default 20000 ~= 20 GB, leaving headroom on a 32 GB machine)
#
# Exit codes: 0 success, 124 timeout, 137 memory-limit kill, 2 usage,
#             other = underlying build failure.
set +e
SECS="${1:-}"
TARGET="${2:-}"
JOBS="${3:-2}"
MEM_MB="${4:-20000}"
if [[ -z "$SECS" || -z "$TARGET" ]]; then
  echo "usage: timed-build.sh <seconds> <target> [jobs] [mem_mb]" >&2
  exit 2
fi

MARKER="$(mktemp -t timed-build.XXXXXX)"

cleanup_children() {
  pkill -9 -P "$BP" 2>/dev/null
  # Also reap detached dune RPC servers + Coq workers: the watchdog's kill -9
  # of the build leaves a dune server running, which then forwards/poisons the
  # next build ("forwarded to a running Dune instance").
  pkill -9 -f "rocqworker|coqc|dune build|dune-build|_build/.dune" 2>/dev/null
  pkill -9 -x dune 2>/dev/null
  rm -f _build/.lock
}

DUNE_JOBS="$JOBS" mise run build "$TARGET" 2>&1 &
BP=$!

# Wall-clock watchdog.
( sleep "$SECS"
  echo "timeout" >"$MARKER"
  kill -9 "$BP" 2>/dev/null
  cleanup_children
  echo "===TIMEOUT: killed at ${SECS}s===" >&2
) &
TWD=$!

# Memory watchdog: poll total worker RSS every 3s; kill if over the cap.
( while kill -0 "$BP" 2>/dev/null; do
    used="$(ps -axo rss,comm 2>/dev/null \
            | grep -Ei 'rocqworker|coqc' | grep -v grep \
            | awk '{s+=$1} END{print int(s/1024)}')"
    if [[ -n "$used" && "$used" -gt "$MEM_MB" ]]; then
      echo "memory" >"$MARKER"
      kill -9 "$BP" 2>/dev/null
      cleanup_children
      echo "===MEMORY LIMIT: worker RSS ${used}MB > ${MEM_MB}MB, killed===" >&2
      break
    fi
    sleep 3
  done ) &
MWD=$!

wait "$BP" 2>/dev/null
STATUS=$?
kill -9 "$TWD" "$MWD" 2>/dev/null

REASON="$(cat "$MARKER" 2>/dev/null)"
rm -f "$MARKER"
case "$REASON" in
  timeout) exit 124 ;;
  memory)  exit 137 ;;
  *)       exit "$STATUS" ;;
esac

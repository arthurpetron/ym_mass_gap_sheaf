#!/usr/bin/env bash
set -euo pipefail

# Start the repository runner in the foreground.  Ctrl-C takes it offline.
# The workflow repeats these checks before it starts Lean.

readonly runner_dir="${YMGAP_RUNNER_DIR:-$HOME/.local/share/ymgap-actions-runner}"
check_only=false

if [[ "${1:-}" == "--check" ]]; then
  check_only=true
elif [[ "$#" -ne 0 ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

if [[ ! -x "$runner_dir/run.sh" || ! -f "$runner_dir/.runner" ]]; then
  echo "error: run scripts/setup_macos_ci_runner.sh first" >&2
  exit 1
fi

if ! /usr/bin/pmset -g batt | head -n 1 | grep -q "AC Power"; then
  echo "error: connect the Mac to AC power before accepting a CI build" >&2
  exit 1
fi

total_bytes="$(/usr/sbin/sysctl -n hw.memsize)"
free_percent="$(
  /usr/bin/memory_pressure -Q |
    awk '/System-wide memory free percentage:/ {
      gsub(/%/, "", $5); print $5
    }'
)"
min_available_bytes=$((24 * 1024 * 1024 * 1024))
if [[ -z "$free_percent" ||
      $((total_bytes * free_percent / 100)) -lt "$min_available_bytes" ]]; then
  echo "error: at least approximately 24 GiB RAM must currently be available" >&2
  exit 1
fi

if pgrep -ifl '(^|/)(lean|lake|pytest)( |$)'; then
  echo "error: Lean/Lake/pytest is already active; refusing competing compilation" >&2
  exit 1
fi

if [[ "$check_only" == "true" ]]; then
  echo "Mac CI runner preflight passed; no runner was started."
  exit 0
fi

echo "Starting the YMGap runner for exactly one foreground job."
exec "$runner_dir/run.sh" --once

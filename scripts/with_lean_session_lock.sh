#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=host_load_patterns.sh
source "$script_dir/host_load_patterns.sh"

# Serialize repository-managed Lean/Lake entry points on this host.  A JIT CI
# launcher holds the same lock for its entire foreground session and exports
# YMGAP_LEAN_SESSION_LOCK_HELD=1 to the job it starts.

if [[ "$#" -lt 2 ]]; then
  echo "usage: $0 <working-directory> <command> [args ...]" >&2
  exit 2
fi

workdir="$1"
shift

readonly default_lock_dir="/tmp/ymgap-lean-session-${UID}.lock"

if [[ "${YMGAP_LEAN_SESSION_LOCK_HELD:-}" == "1" ]]; then
  if [[ -z "${YMGAP_LEAN_LOCK_DIR:-}" ||
        "$YMGAP_LEAN_LOCK_DIR" != "$default_lock_dir" ||
        ! -d "$YMGAP_LEAN_LOCK_DIR" ||
        -L "$YMGAP_LEAN_LOCK_DIR" ||
        ! -O "$YMGAP_LEAN_LOCK_DIR" ]]; then
    echo "error: inherited repository session does not hold the canonical real account-owned lock: $default_lock_dir" >&2
    exit 1
  fi
  cd "$workdir"
  # A foreground runner is expected in inherited CI mode, so recheck only the
  # high-load tools immediately before exec.  The start-anchored shared ERE
  # cannot match this wrapper merely because its later argv names Lean/Lake or
  # pytest.  Treat pgrep failure and a competing build alike as fail-closed.
  inherited_process_status=0
  pgrep -if "$YMGAP_HIGH_LOAD_PROCESS_PATTERN" \
    >/dev/null 2>&1 || inherited_process_status=$?
  case "$inherited_process_status" in
    0)
      echo "error: Lean/Lake/pytest is already active inside the inherited repository session; refusing a competing command" >&2
      exit 1
      ;;
    1) exec "$@" ;;
    *)
      echo "error: could not inspect the host process list immediately before the inherited command; refusing to run fail-open" >&2
      exit 1
      ;;
  esac
fi

# Independent top-level callers must rendezvous on one fixed per-user path.
# Permitting an arbitrary override here would let two callers win different
# mkdir races and defeat exact serialization.  A verified inherited CI session
# may bypass mkdir above only while reusing this same canonical path.
if [[ -n "${YMGAP_LEAN_LOCK_DIR:-}" &&
      "$YMGAP_LEAN_LOCK_DIR" != "$default_lock_dir" ]]; then
  echo "error: top-level repository sessions must use the fixed host lock: $default_lock_dir" >&2
  exit 1
fi

readonly conflict_pattern="$YMGAP_CONFLICT_PROCESS_PATTERN"

# Print matching process IDs. Return the same three-way status as pgrep:
# 0 = conflict, 1 = conclusively clear, and 2 = inspection failure.  The
# shared ERE is anchored at the actual executable prefix, so neither this
# supervising wrapper nor pgrep's own later pattern argument self-matches;
# this remains valid on stock macOS Bash 3.2, which has no BASHPID.
conflicting_processes() {
  local matches=""
  local pgrep_status=0
  local pid=""
  local found=false

  matches="$(pgrep -if "$conflict_pattern" 2>/dev/null)" || pgrep_status=$?
  case "$pgrep_status" in
    0) ;;
    1) return 1 ;;
    *) return 2 ;;
  esac

  while IFS= read -r pid; do
    [[ -z "$pid" ]] && continue
    [[ "$pid" =~ ^[0-9]+$ ]] || return 2
    printf '%s\n' "$pid"
    found=true
  done <<< "$matches"

  [[ "$found" == "true" ]] && return 0
  return 1
}

require_clear_process_list() {
  local context="$1"
  local matches=""
  local inspection_status=0

  matches="$(conflicting_processes)" || inspection_status=$?
  case "$inspection_status" in
    0)
      echo "error: a GitHub runner supervisor/worker or Lean/Lake/pytest is already active ${context}; refusing a competing repository session (PID(s): ${matches//$'\n'/, })" >&2
      return 1
      ;;
    1) return 0 ;;
    *)
      echo "error: could not inspect the host process list ${context}; refusing to run fail-open" >&2
      return 1
      ;;
  esac
}

require_clear_process_list "before acquiring the host lock"

readonly lock_dir="$default_lock_dir"
previous_umask="$(umask)"
umask 077
if ! mkdir "$lock_dir" 2>/dev/null; then
  umask "$previous_umask"
  echo "error: another repository-managed Lean/CI session holds $lock_dir" >&2
  echo "error: if no GitHub runner supervisor/worker, Lean, Lake, or pytest process exists, remove the stale empty directory with: rmdir '$lock_dir'" >&2
  exit 1
fi
umask "$previous_umask"
if [[ ! -d "$lock_dir" || -L "$lock_dir" || ! -O "$lock_dir" ]]; then
  echo "error: the newly acquired host lock is not a real account-owned directory: $lock_dir" >&2
  echo "error: retaining the suspicious lock path for operator inspection" >&2
  exit 1
fi

# Remove the lock only after a conclusive post-command process inspection.  In
# particular, retain it if an interrupt leaves a descendant alive or if pgrep
# itself fails: a stale lock is recoverable, while fail-open concurrency can
# crash this host.
release_lock_if_safe() {
  local original_status="$1"
  local matches=""
  local inspection_status=0

  trap - EXIT
  matches="$(conflicting_processes)" || inspection_status=$?
  case "$inspection_status" in
    0)
      echo "warning: runner/Lean/Lake/pytest process(es) remain (PID(s): ${matches//$'\n'/, }); retaining $lock_dir" >&2
      ;;
    1)
      if ! rmdir "$lock_dir" 2>/dev/null && [[ -e "$lock_dir" ]]; then
        echo "warning: could not remove the repository session lock; retaining $lock_dir" >&2
      fi
      ;;
    *)
      echo "warning: could not inspect the host process list after the wrapped command; retaining $lock_dir" >&2
      ;;
  esac
  exit "$original_status"
}
trap 'release_lock_if_safe "$?"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP

# Close the narrow race between the preflight process sample and atomic mkdir.
# A bare executable cannot honor our lock, so this second sample is mandatory.
require_clear_process_list "after acquiring the host lock"

export YMGAP_LEAN_SESSION_LOCK_HELD=1
export YMGAP_LEAN_LOCK_DIR="$lock_dir"
cd "$workdir"
command_status=0
"$@" || command_status=$?
exit "$command_status"

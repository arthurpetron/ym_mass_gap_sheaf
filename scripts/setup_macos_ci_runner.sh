#!/usr/bin/env bash
set -euo pipefail

# Install the pinned GitHub Actions runner binary used by the YMGap all-module
# Lean build.  This script intentionally does not register a persistent runner
# or install a service.  The foreground launcher requests one short-lived JIT
# configuration for each accepted job.

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=host_load_patterns.sh
source "$script_dir/host_load_patterns.sh"

readonly repo="${YMGAP_GITHUB_REPOSITORY:-arthurpetron/ym_mass_gap_sheaf}"
readonly runner_label="${YMGAP_RUNNER_LABEL:-ymgap-m4max}"
readonly runner_dir="${YMGAP_RUNNER_DIR:-$HOME/.local/share/ymgap-actions-runner}"
readonly runner_version="2.335.1"
readonly archive_name="actions-runner-osx-arm64-${runner_version}.tar.gz"
readonly download_url="https://github.com/actions/runner/releases/download/v${runner_version}/${archive_name}"
readonly expected_sha256="e1a9bc7a3661e06fa0b129d15c2064fe65dc81a431001d8958a9db1409b73769"
readonly canonical_lock_dir="/tmp/ymgap-lean-session-${UID}.lock"
if [[ -n "${YMGAP_LEAN_LOCK_DIR:-}" &&
      "$YMGAP_LEAN_LOCK_DIR" != "$canonical_lock_dir" ]]; then
  echo "error: Mac CI setup must use the fixed host lock: $canonical_lock_dir" >&2
  exit 1
fi
readonly lock_dir="$canonical_lock_dir"
readonly conflict_pattern="$YMGAP_CONFLICT_PROCESS_PATTERN"
archive_dir=""
archive_path=""
setup_lock_held=false
setup_lock_releasable=false
setup_shutdown_uncertain=false

cleanup_setup() {
  local original_status="$?"
  local process_status=0

  trap - EXIT INT TERM HUP
  if [[ -n "$archive_path" && -f "$archive_path" && ! -L "$archive_path" ]]; then
    unlink "$archive_path" 2>/dev/null || true
  fi
  if [[ -n "$archive_dir" && -d "$archive_dir" && ! -L "$archive_dir" ]]; then
    rmdir "$archive_dir" 2>/dev/null || true
  fi
  if [[ "$setup_lock_held" == "true" ]]; then
    if [[ "$setup_lock_releasable" != "true" ]]; then
      echo "warning: retaining the unverified setup host lock for operator inspection: $lock_dir" >&2
    elif [[ "$setup_shutdown_uncertain" == "true" ]]; then
      echo "warning: setup was interrupted; retaining the host lock without guessing about child processes: $lock_dir" >&2
    else
      pgrep -if "$conflict_pattern" >/dev/null 2>&1 || process_status=$?
      case "$process_status" in
        0)
          echo "warning: a runner/Lean/Lake/pytest process is active; retaining the setup host lock: $lock_dir" >&2
          ;;
        1)
          if ! rmdir "$lock_dir" 2>/dev/null &&
              [[ -e "$lock_dir" || -L "$lock_dir" ]]; then
            echo "warning: could not remove the setup host lock; retaining it: $lock_dir" >&2
          fi
          ;;
        *)
          echo "warning: could not inspect the host process list; retaining the setup host lock: $lock_dir" >&2
          ;;
      esac
    fi
  fi
  exit "$original_status"
}
mark_setup_shutdown_uncertain_and_exit() {
  setup_shutdown_uncertain=true
  exit "$1"
}
trap cleanup_setup EXIT
trap 'mark_setup_shutdown_uncertain_and_exit 130' INT
trap 'mark_setup_shutdown_uncertain_and_exit 143' TERM
trap 'mark_setup_shutdown_uncertain_and_exit 129' HUP

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo "error: this setup is pinned for Apple-silicon macOS" >&2
  exit 1
fi

if [[ ! "$repo" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]; then
  echo "error: YMGAP_GITHUB_REPOSITORY must be an owner/repository slug" >&2
  exit 1
fi
if [[ ! "$runner_label" =~ ^[A-Za-z0-9_.-]+$ ]]; then
  echo "error: YMGAP_RUNNER_LABEL contains unsupported characters" >&2
  exit 1
fi
# The launcher exports this value through the official runner's line-oriented
# `.env` file.  Reject whitespace, newlines, ambiguous components, and relative
# paths here as well as at every launch so setup cannot create an unusable or
# environment-injecting installation root.
if [[ "$runner_dir" != /* ||
      ! "$runner_dir" =~ ^/[A-Za-z0-9._/-]+$ ||
      "$runner_dir" == */ ||
      "$runner_dir" == *//* ]]; then
  echo "error: YMGAP_RUNNER_DIR must be an absolute path with safe path characters and no empty components" >&2
  exit 1
fi
case "/${runner_dir#/}/" in
  */./*|*/../*)
    echo "error: YMGAP_RUNNER_DIR must not contain '.' or '..' path components" >&2
    exit 1
    ;;
esac

command -v gh >/dev/null || {
  echo "error: GitHub CLI (gh) is required" >&2
  exit 1
}
gh auth status >/dev/null

require_no_conflicting_processes() {
  local operation="$1"
  local process_status=0

  pgrep -if "$conflict_pattern" >/dev/null 2>&1 || process_status=$?
  case "$process_status" in
    0)
      echo "error: a GitHub runner supervisor/updater/worker or Lean/Lake/pytest is already active; refusing to ${operation}" >&2
      return 1
      ;;
    1) return 0 ;;
    *)
      echo "error: could not inspect the host process list; refusing to ${operation}" >&2
      return 1
      ;;
  esac
}

# Setup mutates the same executable tree used by the foreground runner.  It
# therefore holds the repository's canonical host lock for its entire mutable
# phase, just like a Lean build or JIT session.  A plain atomic mkdir rejects an
# existing directory, file, or symlink instead of following or reusing it.
require_no_conflicting_processes "acquire the setup host lock"
previous_umask="$(umask)"
umask 077
if ! mkdir "$lock_dir" 2>/dev/null; then
  umask "$previous_umask"
  echo "error: another repository-managed Lean/CI session holds $lock_dir" >&2
  exit 1
fi
umask "$previous_umask"
setup_lock_held=true
lock_mode=""
if [[ ! -d "$lock_dir" || -L "$lock_dir" || ! -O "$lock_dir" ]] ||
    ! lock_mode="$(/usr/bin/stat -f '%Lp' "$lock_dir" 2>/dev/null)" ||
    [[ "$lock_mode" != "700" ]]; then
  echo "error: the newly acquired setup host lock is not a real owner-only account-owned directory: $lock_dir" >&2
  echo "error: retaining the suspicious lock path for operator inspection" >&2
  exit 1
fi
setup_lock_releasable=true

# Close the race between the first process sample and atomic lock acquisition.
# External bare tools need not honor the lock, so later irreversible boundaries
# sample the same complete conflict pattern again.
require_no_conflicting_processes "continue setup after acquiring the host lock"

assert_private_runner_dir() {
  local mode=""
  if [[ ! -d "$runner_dir" || -L "$runner_dir" || ! -O "$runner_dir" ]]; then
    echo "error: the runner root must be a real account-owned directory: $runner_dir" >&2
    exit 1
  fi
  if ! /bin/chmod 700 "$runner_dir"; then
    echo "error: could not make the runner root owner-only: $runner_dir" >&2
    exit 1
  fi
  if ! mode="$(/usr/bin/stat -f '%Lp' "$runner_dir" 2>/dev/null)"; then
    echo "error: could not verify runner-root permissions: $runner_dir" >&2
    exit 1
  fi
  if [[ "$mode" != "700" ]]; then
    echo "error: runner-root permissions are not owner-only after chmod: $runner_dir" >&2
    exit 1
  fi
}

require_no_conflicting_processes "mutate the runner root"
if ! mkdir -p "$runner_dir"; then
  echo "error: could not create the runner root: $runner_dir" >&2
  exit 1
fi
# Never chmod through an attacker-controlled symlink.  Authenticity and
# ownership are checked before both permission mutation and archive extraction.
assert_private_runner_dir

runner_recovery_or_config_present() {
  local marker=""

  for marker in \
      "$runner_dir/.ymgap-jit-runner-id" \
      "$runner_dir/.ymgap-jit-runner-id.tmp" \
      "$runner_dir/.runner" \
      "$runner_dir/.runner_migrated" \
      "$runner_dir/.credentials" \
      "$runner_dir/.credentials_rsaparams" \
      "$runner_dir/.credentials_migrated"; do
    if [[ -e "$marker" || -L "$marker" ]]; then
      return 0
    fi
  done
  return 1
}

if [[ -e "$runner_dir/.service" || -L "$runner_dir/.service" ]]; then
  echo "error: this runner root has a persistent service marker: $runner_dir/.service" >&2
  printf 'error: run: cd %q && ./svc.sh uninstall\n' "$runner_dir" >&2
  exit 1
fi

if [[ ! -x "$runner_dir/config.sh" ]]; then
  archive_dir="$(mktemp -d "${TMPDIR:-/tmp}/ymgap-actions-runner.XXXXXX")"
  archive_path="${archive_dir}/${archive_name}"
  curl --fail --location --retry 3 --output "$archive_path" "$download_url"
  actual_sha256="$(shasum -a 256 "$archive_path" | awk '{ print $1 }')"
  if [[ "$actual_sha256" != "$expected_sha256" ]]; then
    echo "error: GitHub runner archive checksum mismatch" >&2
    exit 1
  fi
  require_no_conflicting_processes "extract the runner archive"
  assert_private_runner_dir
  tar -xzf "$archive_path" -C "$runner_dir"
fi

# Runner archives contain a top-level directory entry whose recorded mode can
# replace the destination mode during extraction.  Reassert the owner-only
# boundary after both fresh extraction and preexisting-install validation.
assert_private_runner_dir

if [[ ! -x "$runner_dir/bin/Runner.Listener" ]]; then
  echo "error: the runner installation is incomplete: bin/Runner.Listener is missing" >&2
  exit 1
fi

installed_version=""
require_no_conflicting_processes "execute the installed runner version probe"
if ! installed_version="$(
  "$runner_dir/bin/Runner.Listener" --version 2>/dev/null |
    tr -d '[:space:]'
)"; then
  echo "error: could not verify the installed GitHub runner version" >&2
  exit 1
fi
if [[ "$installed_version" != "$runner_version" ]]; then
  echo "error: installed GitHub runner version '$installed_version' does not match pinned version '$runner_version'" >&2
  if runner_recovery_or_config_present; then
    echo "error: recovery or local registration remains in this runner root; do not switch directories" >&2
    echo "error: run scripts/run_macos_ci_runner.sh in this same YMGAP_RUNNER_DIR to reconcile it before reinstalling" >&2
  else
    echo "error: with no recovery/config state remaining, use a fresh YMGAP_RUNNER_DIR or deliberately update the pinned version and checksum" >&2
  fi
  exit 1
fi

require_no_conflicting_processes "set the repository runner-label variable"
gh variable set YMGAP_LEAN_RUNNER \
  --repo "$repo" \
  --body "$runner_label"

echo
echo "Pinned runner binary $runner_version installed and verified; no persistent runner was registered."
if [[ -f "$runner_dir/.runner" ]]; then
  echo "The launcher will safely remove the legacy registration after its active job exits."
fi
echo "When the Mac is idle and on AC power, create one foreground JIT session with:"
echo "  scripts/run_macos_ci_runner.sh"

#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=host_load_patterns.sh
source "$script_dir/host_load_patterns.sh"

# Start one just-in-time repository runner in the foreground.  GitHub assigns
# a JIT runner at most one job. Normal exit verifies remote/local cleanup;
# trapped shutdown uses a bounded direct-child stop protocol and retains the
# recovery record and host lock rather than guessing about orphan descendants.
# The workflow repeats the host checks before it starts Lean.

readonly repo="${YMGAP_GITHUB_REPOSITORY:-arthurpetron/ym_mass_gap_sheaf}"
readonly runner_label="${YMGAP_RUNNER_LABEL:-ymgap-m4max}"
readonly runner_dir="${YMGAP_RUNNER_DIR:-$HOME/.local/share/ymgap-actions-runner}"
readonly runner_group_id="${YMGAP_RUNNER_GROUP_ID:-1}"
readonly runner_version="2.335.1"
readonly runner_path="$HOME/.elan/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"
readonly canonical_lock_dir="/tmp/ymgap-lean-session-${UID}.lock"
if [[ -n "${YMGAP_LEAN_LOCK_DIR:-}" &&
      "$YMGAP_LEAN_LOCK_DIR" != "$canonical_lock_dir" ]]; then
  echo "error: the Mac CI launcher must use the fixed host lock: $canonical_lock_dir" >&2
  exit 1
fi
readonly lock_dir="$canonical_lock_dir"
readonly jit_state="${runner_dir}/.ymgap-jit-runner-id"
readonly jit_state_tmp="${jit_state}.tmp"
readonly conflict_pattern="$YMGAP_CONFLICT_PROCESS_PATTERN"
check_only=false
shutdown_uncertain=false

if [[ "${1:-}" == "--check" ]]; then
  check_only=true
elif [[ "$#" -ne 0 ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

if [[ ! "$repo" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]; then
  echo "error: YMGAP_GITHUB_REPOSITORY must be an owner/repository slug" >&2
  exit 1
fi
if [[ ! "$runner_label" =~ ^[A-Za-z0-9_.-]+$ ]]; then
  echo "error: YMGAP_RUNNER_LABEL contains unsupported characters" >&2
  exit 1
fi
if [[ ! "$runner_group_id" =~ ^[1-9][0-9]*$ ]]; then
  echo "error: YMGAP_RUNNER_GROUP_ID must be a positive decimal integer" >&2
  exit 1
fi
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

assert_private_runner_dir() {
  local mode=""
  if [[ ! -d "$runner_dir" || -L "$runner_dir" || ! -O "$runner_dir" ]]; then
    echo "error: the runner root must be a real account-owned directory: $runner_dir" >&2
    exit 1
  fi
  if ! mode="$(/usr/bin/stat -f '%Lp' "$runner_dir" 2>/dev/null)"; then
    echo "error: could not verify runner-root permissions: $runner_dir" >&2
    exit 1
  fi
  if [[ "$mode" != "700" ]]; then
    if [[ "$check_only" == "true" ]]; then
      echo "error: runner-root permissions are not owner-only; --check will not chmod: $runner_dir" >&2
      exit 1
    fi
    if ! /bin/chmod 700 "$runner_dir"; then
      echo "error: could not make the runner root owner-only: $runner_dir" >&2
      exit 1
    fi
    if ! mode="$(/usr/bin/stat -f '%Lp' "$runner_dir" 2>/dev/null)"; then
      echo "error: could not reverify runner-root permissions: $runner_dir" >&2
      exit 1
    fi
  fi
  if [[ "$mode" != "700" ]]; then
    echo "error: runner-root permissions are not owner-only after chmod: $runner_dir" >&2
    exit 1
  fi
}

assert_private_runner_dir

if [[ -e "$runner_dir/.service" || -L "$runner_dir/.service" ]]; then
  echo "error: a persistent GitHub runner service marker exists: $runner_dir/.service" >&2
  printf 'error: run: cd %q && ./svc.sh uninstall\n' "$runner_dir" >&2
  exit 1
fi

if [[ ! -x "$runner_dir/config.sh" ]]; then
  echo "error: config.sh is required in the original runner root to reconcile local registration state" >&2
  echo "error: repair this same YMGAP_RUNNER_DIR; do not strand recovery by switching directories" >&2
  exit 1
fi

command -v gh >/dev/null || {
  echo "error: GitHub CLI (gh) is required to create a one-job JIT runner" >&2
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

require_new_job_host_ready() {
  local total_bytes=""
  local free_percent=""
  local min_available_bytes=$((32 * 1024 * 1024 * 1024))

  if [[ ! -x "$HOME/.elan/bin/elan" ]]; then
    echo "error: install elan before accepting a Lean CI job" >&2
    return 1
  fi
  if ! /usr/bin/pmset -g batt | head -n 1 | grep -q "AC Power"; then
    echo "error: connect the Mac to AC power before accepting a CI build" >&2
    return 1
  fi
  total_bytes="$(/usr/sbin/sysctl -n hw.memsize)"
  free_percent="$(
    /usr/bin/memory_pressure -Q |
      awk '/System-wide memory free percentage:/ {
        gsub(/%/, "", $5); print $5
      }'
  )"
  if [[ -z "$free_percent" ||
        $((total_bytes * free_percent / 100)) -lt "$min_available_bytes" ]]; then
    echo "error: at least approximately 32 GiB RAM must currently be available" >&2
    return 1
  fi
}

require_complete_runner_installation() {
  if [[ ! -x "$runner_dir/run.sh" ||
        ! -x "$runner_dir/bin/Runner.Listener" ]]; then
    echo "error: run scripts/setup_macos_ci_runner.sh before accepting a new job" >&2
    return 1
  fi
}

require_no_conflicting_processes "bring the runner online"

if [[ "$check_only" != "true" ]]; then
  previous_umask="$(umask)"
  umask 077
  if ! mkdir "$lock_dir" 2>/dev/null; then
    umask "$previous_umask"
    echo "error: another repository-managed Lean/CI session holds $lock_dir" >&2
    exit 1
  fi
  umask "$previous_umask"
  if [[ ! -d "$lock_dir" || -L "$lock_dir" || ! -O "$lock_dir" ]]; then
    echo "error: the newly acquired host lock is not a real account-owned directory: $lock_dir" >&2
    echo "error: retaining the suspicious lock path for operator inspection" >&2
    exit 1
  fi
  export YMGAP_LEAN_SESSION_LOCK_HELD=1
  export YMGAP_LEAN_LOCK_DIR="$lock_dir"
fi

# Until the full JIT cleanup trap is installed below, retain the new lock when
# a post-mkdir conflict survives and remove it only after a conclusive clear
# process sample. This mirrors the standalone Lean-session wrapper.
release_pre_recovery_lock_if_safe() {
  local original_status="$1"
  local process_status=0

  trap - EXIT
  if [[ "${shutdown_uncertain:-false}" == "true" ]]; then
    echo "warning: launcher shutdown was interrupted; retaining $lock_dir without guessing about descendants" >&2
    exit "$original_status"
  fi
  pgrep -if "$conflict_pattern" >/dev/null 2>&1 || process_status=$?
  case "$process_status" in
    0)
      echo "warning: a runner/Lean/Lake/pytest process remains; retaining $lock_dir" >&2
      ;;
    1)
      if ! rmdir "$lock_dir" 2>/dev/null && [[ -e "$lock_dir" ]]; then
        echo "warning: could not remove the repository session lock; retaining $lock_dir" >&2
      fi
      ;;
    *)
      echo "warning: could not inspect the host process list; retaining $lock_dir" >&2
      ;;
  esac
  exit "$original_status"
}
mark_shutdown_uncertain_and_exit() {
  shutdown_uncertain=true
  exit "$1"
}
if [[ "$check_only" != "true" ]]; then
  trap 'release_pre_recovery_lock_if_safe "$?"' EXIT
  trap 'mark_shutdown_uncertain_and_exit 130' INT
  trap 'mark_shutdown_uncertain_and_exit 143' TERM
  trap 'mark_shutdown_uncertain_and_exit 129' HUP

  # Close the race between the first process sample and winning atomic mkdir
  # before stale-state reconciliation can deregister or alter any runner.
  require_no_conflicting_processes "continue after acquiring the host lock"
fi

jit_runner_id=""
jit_session_created=false
jit_state_active=false
jit_remote_visible=false
runner_name=""
runner_supervisor_pid=""
jit_state_repo=""
jit_state_name=""
jit_state_id=""
jit_state_schema=""
jit_state_phase=""
jit_state_runner_id=""

local_runner_settings_present() {
  [[ -e "$runner_dir/.runner" || -L "$runner_dir/.runner" ||
     -e "$runner_dir/.runner_migrated" || -L "$runner_dir/.runner_migrated" ]]
}

local_runner_credentials_present() {
  [[ -e "$runner_dir/.credentials" || -L "$runner_dir/.credentials" ||
     -e "$runner_dir/.credentials_migrated" || -L "$runner_dir/.credentials_migrated" ]]
}

local_runner_config_present() {
  [[ -e "$runner_dir/.runner" || -L "$runner_dir/.runner" ||
     -e "$runner_dir/.runner_migrated" || -L "$runner_dir/.runner_migrated" ||
     -e "$runner_dir/.credentials" || -L "$runner_dir/.credentials" ||
     -e "$runner_dir/.credentials_rsaparams" || -L "$runner_dir/.credentials_rsaparams" ||
     -e "$runner_dir/.credentials_migrated" || -L "$runner_dir/.credentials_migrated" ]]
}

require_local_config_paths_safe() {
  local marker=""

  for marker in \
      "$runner_dir/.runner" \
      "$runner_dir/.runner_migrated" \
      "$runner_dir/.credentials" \
      "$runner_dir/.credentials_rsaparams" \
      "$runner_dir/.credentials_migrated"; do
    [[ -e "$marker" || -L "$marker" ]] || continue
    if [[ ! -f "$marker" || -L "$marker" || ! -O "$marker" ]]; then
      echo "error: local runner marker is not a real account-owned file: $marker" >&2
      return 1
    fi
  done
}

local_runner_id_from_file() {
  local settings_file="$1"
  local key=""
  local candidate=""
  local parsed=""
  local successes=0

  # Persistent registrations currently serialize lower-case agentId, while a
  # JIT payload may serialize the RunnerSettings data member AgentId and may
  # encode it as either a JSON number or decimal string. plutil handles both
  # forms (and a UTF-8 BOM); exactly one spelling must be present.
  for key in agentId AgentId; do
    candidate=""
    if candidate="$(
      /usr/bin/plutil -extract "$key" raw -o - "$settings_file" 2>/dev/null
    )"; then
      if [[ ! "$candidate" =~ ^[1-9][0-9]*$ ]]; then
        return 1
      fi
      parsed="$candidate"
      successes=$((successes + 1))
    fi
  done

  [[ "$successes" -eq 1 ]] || return 1
  printf '%s\n' "$parsed"
}

require_local_runner_ids_match() {
  local expected="$1"
  local settings_file=""
  local local_id=""

  for settings_file in "$runner_dir/.runner" "$runner_dir/.runner_migrated"; do
    [[ -e "$settings_file" || -L "$settings_file" ]] || continue
    if [[ ! -f "$settings_file" || -L "$settings_file" || ! -O "$settings_file" ]]; then
      echo "error: local runner settings are not a real account-owned file: $settings_file" >&2
      return 1
    fi
    if ! local_id="$(local_runner_id_from_file "$settings_file")"; then
      echo "error: could not read one unambiguous positive runner ID from $settings_file" >&2
      return 1
    fi
    if [[ "$local_id" != "$expected" ]]; then
      echo "error: local runner identity in $settings_file does not match the expected ID; preserving state" >&2
      return 1
    fi
  done
}

write_jit_state() {
  local state_repo="$1"
  local state_name="$2"
  local state_id="$3"
  local mode=""

  if [[ ! "$state_repo" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ||
        ! "$state_name" =~ ^[A-Za-z0-9_.-]+$ ||
        "${#state_name}" -gt 64 ||
        ( "$state_id" != "pending" &&
          ! "$state_id" =~ ^registered:[1-9][0-9]*$ &&
          ! "$state_id" =~ ^remote-visible:[1-9][0-9]*$ &&
          ! "$state_id" =~ ^remote-delete-requested:[1-9][0-9]*$ &&
          ! "$state_id" =~ ^remote-removed:[1-9][0-9]*$ ) ]]; then
    echo "error: refusing to write invalid JIT recovery values" >&2
    return 1
  fi
  if [[ -e "$jit_state_tmp" || -L "$jit_state_tmp" ]]; then
    echo "error: refusing to overwrite unexpected temporary JIT recovery evidence: $jit_state_tmp" >&2
    return 1
  fi
  if [[ -e "$jit_state" || -L "$jit_state" ]]; then
    if [[ ! -f "$jit_state" || -L "$jit_state" || ! -O "$jit_state" ]] ||
        ! mode="$(/usr/bin/stat -f '%Lp' "$jit_state" 2>/dev/null)" ||
        [[ "$mode" != "600" ]]; then
      echo "error: refusing to replace unsafe JIT recovery evidence: $jit_state" >&2
      return 1
    fi
  fi
  # noclobber closes the check/create race on the fixed temporary name.
  if ! (
    set -o noclobber
    umask 077
    printf 'v2\n%s\n%s\n%s\n' \
      "$state_repo" "$state_name" "$state_id" > "$jit_state_tmp"
  ); then
    echo "error: could not exclusively create the temporary JIT recovery record" >&2
    return 1
  fi
  # Every mutation is explicitly guarded: Bash suppresses `errexit` throughout
  # a function invoked from an `if`/`!` conditional, which is exactly how these
  # state transitions are called during cleanup and recovery.
  if ! /bin/chmod 600 "$jit_state_tmp"; then
    echo "error: could not make the temporary JIT recovery record owner-only; preserving it" >&2
    return 1
  fi
  if ! /bin/mv -f "$jit_state_tmp" "$jit_state"; then
    echo "error: could not atomically promote the JIT recovery record; preserving prior/temporary evidence" >&2
    return 1
  fi
  if [[ ! -f "$jit_state" || -L "$jit_state" || ! -O "$jit_state" ]] ||
      ! mode="$(/usr/bin/stat -f '%Lp' "$jit_state" 2>/dev/null)" ||
      [[ "$mode" != "600" ]]; then
    echo "error: atomically promoted JIT recovery record failed ownership/mode validation" >&2
    return 1
  fi
  # Re-read the promoted inode and compare every byte, including the schema and
  # terminal newline, before the durability barrier.  Parsed-field equality is
  # insufficient here because extra lines/bytes could change recovery meaning.
  if ! /usr/bin/cmp -s "$jit_state" <(
    printf 'v2\n%s\n%s\n%s\n' "$state_repo" "$state_name" "$state_id"
  ); then
    echo "error: promoted JIT recovery bytes do not exactly match the requested transition; preserving evidence" >&2
    return 1
  fi
  # Atomic rename prevents torn readers; sync is the conservative macOS
  # persistence barrier needed before GitHub can own a registration that is
  # not yet durably recoverable after a power/kernel crash.
  if ! /bin/sync; then
    echo "error: could not durably flush the JIT recovery record" >&2
    return 1
  fi
}

read_jit_state() {
  local line=""
  local mode=""
  local size=""
  local -a lines=()

  if [[ ! -f "$jit_state" || -L "$jit_state" || ! -O "$jit_state" ]]; then
    echo "error: JIT recovery record is not a real account-owned file: $jit_state" >&2
    return 1
  fi
  if ! mode="$(/usr/bin/stat -f '%Lp' "$jit_state" 2>/dev/null)" ||
      [[ "$mode" != "600" ]]; then
    echo "error: JIT recovery record is not owner-only: $jit_state" >&2
    return 1
  fi
  if ! size="$(/usr/bin/stat -f '%z' "$jit_state" 2>/dev/null)" ||
      [[ ! "$size" =~ ^[1-9][0-9]*$ ]] ||
      [[ "$size" -gt 512 ]]; then
    echo "error: JIT recovery record has an invalid or excessive byte size: $jit_state" >&2
    return 1
  fi
  while IFS= read -r line || [[ -n "$line" ]]; do
    lines[${#lines[@]}]="$line"
  done < "$jit_state"
  if [[ "${#lines[@]}" -ne 4 ]]; then
    echo "error: malformed JIT recovery record: $jit_state" >&2
    return 1
  fi
  if [[ "${lines[0]}" != "v1" && "${lines[0]}" != "v2" ]]; then
    echo "error: malformed JIT recovery record: $jit_state" >&2
    return 1
  fi

  jit_state_schema="${lines[0]}"
  jit_state_repo="${lines[1]}"
  jit_state_name="${lines[2]}"
  jit_state_id="${lines[3]}"
  if [[ ! "$jit_state_repo" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ||
        ! "$jit_state_name" =~ ^[A-Za-z0-9_.-]+$ ||
        "${#jit_state_name}" -gt 64 ]]; then
    echo "error: invalid values in JIT recovery record: $jit_state" >&2
    return 1
  fi

  jit_state_phase=""
  jit_state_runner_id=""
  if [[ "$jit_state_schema" == "v1" ]]; then
    if [[ "$jit_state_id" == "pending" ]]; then
      jit_state_phase="pending"
    elif [[ "$jit_state_id" =~ ^[1-9][0-9]*$ ]]; then
      jit_state_phase="registered"
      jit_state_runner_id="$jit_state_id"
    elif [[ "$jit_state_id" =~ ^completed:([1-9][0-9]*)$ ]]; then
      jit_state_phase="registered"
      jit_state_runner_id="${BASH_REMATCH[1]}"
    elif [[ "$jit_state_id" =~ ^remote-(delete-requested|removed):([1-9][0-9]*)$ ]]; then
      jit_state_phase="registered"
      jit_state_runner_id="${BASH_REMATCH[2]}"
    else
      echo "error: invalid legacy phase in JIT recovery record: $jit_state" >&2
      return 1
    fi
    # All v1 ID-bearing phases are conservative registrations.  In
    # particular, the old completion heuristic used a normalized run-helper
    # status, so even its deletion/absence descendants must regain exact
    # repository/name/ID visibility before a later 404 is authoritative.
  elif [[ "$jit_state_id" == "pending" ]]; then
    jit_state_phase="pending"
  elif [[ "$jit_state_id" =~ ^registered:([1-9][0-9]*)$ ]]; then
    jit_state_phase="registered"
    jit_state_runner_id="${BASH_REMATCH[1]}"
  elif [[ "$jit_state_id" =~ ^remote-visible:([1-9][0-9]*)$ ]]; then
    jit_state_phase="remote-visible"
    jit_state_runner_id="${BASH_REMATCH[1]}"
  elif [[ "$jit_state_id" =~ ^remote-delete-requested:([1-9][0-9]*)$ ]]; then
    jit_state_phase="remote-delete-requested"
    jit_state_runner_id="${BASH_REMATCH[1]}"
  elif [[ "$jit_state_id" =~ ^remote-removed:([1-9][0-9]*)$ ]]; then
    jit_state_phase="remote-removed"
    jit_state_runner_id="${BASH_REMATCH[1]}"
  elif [[ "$jit_state_id" =~ ^[1-9][0-9]*$ ]]; then
    # Bare numeric v2 records are accepted only for backward compatibility and
    # have no positive visibility witness.
    jit_state_phase="registered"
    jit_state_runner_id="$jit_state_id"
  else
    echo "error: invalid phase in JIT recovery record: $jit_state" >&2
    return 1
  fi
}

remote_runner_collection_snapshot_without_id() {
  local target_repo="$1"
  local runner_id="$2"
  local collection_rows=""
  local tag=""
  local first=""
  local second=""
  local third=""
  local extra=""
  local total_count=""
  local page_count=0
  local page_item_count=0
  local runner_count=0
  local runner_ids=""
  local sorted_ids=""
  local duplicate_ids=""

  # This repository-admin endpoint must return every page successfully.  Each
  # page emits one metadata row followed by its runner IDs.  We then prove that
  # all pages agree on a nonnegative integral total, every page payload is an
  # array, the concatenated IDs are positive and globally unique, and their
  # exact count equals total_count.  The canonical sorted snapshot is emitted
  # only when the target ID is absent.  A caller must compare two independently
  # acquired snapshots: GitHub pagination is not a transactional snapshot, so
  # cardinality checks on one traversal cannot exclude a page-shift race.
  if ! collection_rows="$(
    gh api --method GET --paginate \
      "repos/${target_repo}/actions/runners?per_page=100" \
      --jq '
        (["M", (.total_count | tostring), (.runners | type),
          ((.runners | length) | tostring)] | @tsv),
        (.runners[] | ["I", (.id | tostring)] | @tsv)
      ' 2>/dev/null
  )" || [[ -z "$collection_rows" ]]; then
    return 1
  fi

  while IFS=$'\t' read -r tag first second third extra; do
    case "$tag" in
      M)
        if [[ ! "$first" =~ ^(0|[1-9][0-9]*)$ ||
              "$second" != "array" ||
              ! "$third" =~ ^(0|[1-9][0-9]*)$ ||
              -n "$extra" ||
              "$first" -gt 100000 ||
              "$third" -gt 100 ]]; then
          return 1
        fi
        if [[ -z "$total_count" ]]; then
          total_count="$first"
        elif [[ "$first" != "$total_count" ]]; then
          return 1
        fi
        page_count=$((page_count + 1))
        page_item_count=$((page_item_count + third))
        ;;
      I)
        if [[ ! "$first" =~ ^[1-9][0-9]*$ ||
              -n "$second" || -n "$third" || -n "$extra" ||
              "$first" == "$runner_id" ]]; then
          return 1
        fi
        runner_count=$((runner_count + 1))
        if [[ "$runner_count" -gt 100000 ]]; then
          return 1
        fi
        runner_ids="${runner_ids}${first}"$'\n'
        ;;
      *) return 1 ;;
    esac
  done <<< "$collection_rows"

  if [[ "$page_count" -lt 1 || -z "$total_count" ||
        "$page_item_count" -ne "$total_count" ||
        "$runner_count" -ne "$total_count" ]]; then
    return 1
  fi
  if [[ "$runner_count" -gt 0 ]]; then
    if ! sorted_ids="$(
      printf '%s' "$runner_ids" |
        LC_ALL=C /usr/bin/sort
    )"; then
      return 1
    fi
    if ! duplicate_ids="$(
      printf '%s\n' "$sorted_ids" |
        /usr/bin/uniq -d
    )"; then
      return 1
    fi
    [[ -z "$duplicate_ids" ]] || return 1
  fi

  # Prefix the canonical ID list with its independently checked cardinality so
  # even the empty collection has a nonempty, unambiguous snapshot.
  printf 'count:%s\n' "$total_count"
  if [[ -n "$sorted_ids" ]]; then
    printf '%s\n' "$sorted_ids"
  fi
}

remote_runner_exact_get_is_404() {
  local target_repo="$1"
  local runner_id="$2"
  local get_output=""
  local get_status=0
  local status_codes=""

  get_output="$(
    gh api --method GET --include \
      "repos/${target_repo}/actions/runners/${runner_id}" 2>&1
  )" || get_status=$?
  if [[ "$get_status" -eq 0 ]]; then
    return 1
  fi
  # `gh api --include` may contain multiple response blocks (for example after
  # an intermediary or redirect).  Exactly one syntactically valid HTTP status
  # line must be present, and its code must be 404; finding any 404 somewhere in
  # a mixed response is not an absence witness.
  if ! status_codes="$(
    printf '%s\n' "$get_output" |
      LC_ALL=C /usr/bin/awk '
        /^HTTP\/[0-9]+([.][0-9]+)?[[:space:]]+[0-9][0-9][0-9]([[:space:]]|$)/ {
          print $2
        }
      '
  )"; then
    return 1
  fi
  [[ "$status_codes" == "404" ]]
}

remote_runner_absent() {
  local target_repo="$1"
  local runner_id="$2"
  local first_snapshot=""
  local second_snapshot=""
  if gh api --method DELETE \
      "repos/${target_repo}/actions/runners/${runner_id}" \
      >/dev/null 2>&1; then
    return 0
  fi

  # An ID-endpoint 404 can be authorization- or repository-masked, and one
  # paginated collection traversal can omit an extant runner if the collection
  # shifts between pages.  Require two independently acquired, structurally
  # complete, identical snapshots which both omit this ID, with the exact-ID
  # 404 bracketed between their successful repository-admin reads.  Thus a
  # credential/access loss after the first snapshot cannot certify absence.
  if ! first_snapshot="$(
    remote_runner_collection_snapshot_without_id "$target_repo" "$runner_id"
  )" ||
      ! remote_runner_exact_get_is_404 "$target_repo" "$runner_id" ||
      ! second_snapshot="$(
        remote_runner_collection_snapshot_without_id "$target_repo" "$runner_id"
      )" ||
      [[ "$first_snapshot" != "$second_snapshot" ]]; then
    return 1
  fi
}

remote_runner_visible() {
  local target_repo="$1"
  local target_name="$2"
  local runner_id="$3"
  local observed=""
  local observed_id=""
  local observed_name=""

  if ! observed="$(
    gh api --method GET \
      "repos/${target_repo}/actions/runners/${runner_id}" \
      --jq '[.id, .name] | @tsv' 2>/dev/null
  )"; then
    return 1
  fi
  IFS=$'\t' read -r observed_id observed_name <<< "$observed"
  [[ "$observed_id" == "$runner_id" && "$observed_name" == "$target_name" ]]
}

await_remote_runner_visible() {
  local target_repo="$1"
  local target_name="$2"
  local runner_id="$3"
  local attempt=1
  local max_attempts=12

  while [[ "$attempt" -le "$max_attempts" ]]; do
    if remote_runner_visible "$target_repo" "$target_name" "$runner_id"; then
      return 0
    fi
    if [[ "$attempt" -lt "$max_attempts" ]]; then
      /bin/sleep 2
    fi
    attempt=$((attempt + 1))
  done
  return 1
}

establish_remote_visibility() {
  local target_repo="$1"
  local target_name="$2"
  local runner_id="$3"

  await_remote_runner_visible "$target_repo" "$target_name" "$runner_id" || return 1
  write_jit_state \
    "$target_repo" "$target_name" "remote-visible:${runner_id}"
}

delete_visible_remote_runner_with_recovery() {
  local target_repo="$1"
  local target_name="$2"
  local runner_id="$3"

  # This function is called only after `remote-visible:<id>` was durably
  # flushed.  Record the delete intent before making the remote mutation so a
  # crash can safely retry and accept an exact-ID 404.
  write_jit_state \
    "$target_repo" "$target_name" "remote-delete-requested:${runner_id}" || return 1
  remote_runner_absent "$target_repo" "$runner_id" || return 1
  write_jit_state \
    "$target_repo" "$target_name" "remote-removed:${runner_id}"
}

remove_remote_runner_by_exact_name() {
  local target_repo="$1"
  local target_name="$2"
  local matching_ids=""
  local runner_id=""
  local found_id=""

  if ! matching_ids="$(
    gh api --paginate \
      "repos/${target_repo}/actions/runners?per_page=100" \
      --jq ".runners[] | select(.name == \"${target_name}\") | .id" \
      2>/dev/null
  )"; then
    return 1
  fi
  # Empty list output is deliberately inconclusive for a pending/lost POST.
  # Preserve the record and retry later instead of orphaning a late-visible
  # registration.
  [[ -z "$matching_ids" ]] && return 1

  while IFS= read -r runner_id; do
    [[ "$runner_id" =~ ^[1-9][0-9]*$ ]] || return 1
    [[ -z "$found_id" ]] || return 1
    found_id="$runner_id"
  done <<< "$matching_ids"
  [[ -n "$found_id" ]] || return 1
  # Confirm the list result through the exact-ID endpoint and durably record
  # visibility before the delete-requested phase may make a later 404
  # authoritative.
  establish_remote_visibility \
    "$target_repo" "$target_name" "$found_id" || return 1
  delete_visible_remote_runner_with_recovery \
    "$target_repo" "$target_name" "$found_id"
}

cleanup_session() {
  local remote_clean=true
  local local_clean=true
  local cleanup_allowed=true
  local pre_cleanup_status=0
  local post_supervisor_status=0

  # A trapped shutdown may orphan arbitrary action descendants which no finite
  # executable-name pattern can prove absent.  In that case never mutate remote
  # or local registration state, even when pgrep looks clear; preserve both the
  # recovery record and host lock for conflict-free next-launch reconciliation.
  if [[ "${shutdown_uncertain:-false}" == "true" ]]; then
    cleanup_allowed=false
    echo "warning: trapped runner shutdown is descendant-uncertain; skipping JIT cleanup and retaining state" >&2
  else
    # Never deregister or delete credentials underneath a surviving supervisor,
    # updater, helper, Listener, Worker, PluginHost, Lean, Lake, or pytest
    # descendant. The host lock and recovery record are fail-closed evidence.
    pgrep -if "$conflict_pattern" >/dev/null 2>&1 || pre_cleanup_status=$?
    case "$pre_cleanup_status" in
      0)
        cleanup_allowed=false
        echo "warning: a runner/build process remains; skipping JIT cleanup and retaining state" >&2
        ;;
      1) ;;
      *)
        cleanup_allowed=false
        echo "warning: could not verify runner/build quiescence; skipping JIT cleanup and retaining state" >&2
        ;;
    esac
  fi

  if [[ "$cleanup_allowed" != "true" ]]; then
    remote_clean=false
    local_clean=false
  elif [[ "${jit_state_active:-false}" == "true" ]]; then
    if [[ "${jit_runner_id:-}" =~ ^[1-9][0-9]*$ ]]; then
      if [[ "${jit_remote_visible:-false}" != "true" ]]; then
        if establish_remote_visibility "$repo" "$runner_name" "$jit_runner_id"; then
          jit_remote_visible=true
        else
          remote_clean=false
        fi
      fi
      if [[ "$remote_clean" == "true" ]] &&
          ! delete_visible_remote_runner_with_recovery \
            "$repo" "$runner_name" "$jit_runner_id"; then
        remote_clean=false
      fi
    elif [[ -n "${runner_name:-}" ]]; then
      # The registration POST may have succeeded even when its response was
      # lost.  GitHub's list endpoint need not expose the new runner
      # immediately, so absence during this same invocation is not proof of
      # cleanup.  Preserve the pending write-ahead record unconditionally;
      # the next launch reconciles its exact repository/name after time has
      # elapsed.
      remote_clean=false
    else
      remote_clean=false
    fi
    if [[ "$remote_clean" != "true" ]]; then
      echo "warning: could not verify JIT runner removal; retaining $jit_state" >&2
    fi
  fi
  if [[ "$cleanup_allowed" == "true" &&
        "$remote_clean" == "true" &&
        "$jit_session_created" == "true" ]] &&
      local_runner_config_present &&
      ! validate_local_config_for_id "$jit_runner_id" "remote-removed"; then
    local_clean=false
    echo "warning: ambiguous or mismatched local JIT marker remains; retaining $jit_state" >&2
  elif [[ "$cleanup_allowed" == "true" &&
        "$remote_clean" == "true" &&
        "$jit_session_created" == "true" ]] &&
      local_runner_settings_present; then
    # Runner.Listener removes these itself only after a completed ephemeral
    # job.  A normal no-job exit must remove the local JIT credentials
    # explicitly, after the runner supervisor and its descendants have stopped.
    (
      cd "$runner_dir"
      ./config.sh remove --local
    ) >/dev/null 2>&1 || true
  fi
  if [[ "$cleanup_allowed" == "true" &&
        "$remote_clean" == "true" &&
        "$jit_session_created" == "true" ]] && local_runner_config_present; then
    local_clean=false
    echo "warning: local JIT credentials remain; retaining $jit_state" >&2
  fi
  if [[ "${jit_state_active:-false}" == "true" &&
        "$remote_clean" == "true" && "$local_clean" == "true" ]]; then
    if ! unlink "$jit_state" 2>/dev/null; then
      echo "warning: verified cleanup completed, but the recovery record could not be removed: $jit_state" >&2
    elif ! /bin/sync; then
      echo "warning: verified cleanup completed, but recovery-record removal could not be durably flushed" >&2
    fi
    if [[ -e "$jit_state_tmp" || -L "$jit_state_tmp" ]]; then
      unlink "$jit_state_tmp" 2>/dev/null || true
    fi
  fi
  # Release the host lock only after proving that no supervisor, updater,
  # Listener, Worker, PluginHost, or competing Lean/Lake/pytest process survived
  # a normal shutdown. A trapped shutdown retains it unconditionally because an
  # arbitrary orphaned action child cannot be exhaustively recognized by name.
  if [[ "${shutdown_uncertain:-false}" == "true" ]]; then
    echo "warning: retaining $lock_dir after trapped descendant-uncertain shutdown" >&2
  else
    pgrep -if "$conflict_pattern" >/dev/null 2>&1 || post_supervisor_status=$?
    case "$post_supervisor_status" in
      0)
        echo "warning: a runner supervisor/updater/worker/plugin host or Lean/Lake/pytest process remains; retaining $lock_dir" >&2
        ;;
      1)
        if ! rmdir "$lock_dir" 2>/dev/null && [[ -e "$lock_dir" ]]; then
          echo "warning: could not remove the Lean session lock: $lock_dir" >&2
        fi
        ;;
      *)
        echo "warning: could not inspect the host process list after runner shutdown; retaining $lock_dir" >&2
        ;;
    esac
  fi
}

runner_supervisor_process_state() {
  local pid="$1"
  local process_row=""
  local ps_status=0
  local observed_ppid=""
  local observed_state=""
  local extra=""

  [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 2
  process_row="$(
    /bin/ps -o ppid= -o stat= -p "$pid" 2>/dev/null
  )" || ps_status=$?
  case "$ps_status" in
    0) [[ -n "$process_row" ]] || return 2 ;;
    1)
      # With headings suppressed, macOS ps returns 1 and no row only when the
      # PID is absent. Any contradictory output remains inconclusive.
      [[ -z "$process_row" ]] && return 1
      return 2
      ;;
    *) return 2 ;;
  esac
  if ! read -r observed_ppid observed_state extra <<< "$process_row"; then
    return 2
  fi
  if [[ ! "$observed_ppid" =~ ^[1-9][0-9]*$ ||
        -z "$observed_state" || -n "$extra" ||
        "$observed_ppid" != "$$" ]]; then
    return 2
  fi
  # Status 3 is reserved for a confirmed direct-child zombie. Only that state
  # may be passed to blocking `wait`; status 1 means ps proved PID absence.
  [[ "$observed_state" == Z* ]] && return 3
  # A failed permission/existence probe must not be collapsed into absence:
  # EPERM and a live-to-gone race are both conservative uncertainty.
  if ! kill -0 "$pid" 2>/dev/null; then
    return 2
  fi
  return 0
}

signal_runner_supervisor() {
  kill "-$1" "$2"
}

pause_runner_supervisor_poll() {
  /bin/sleep 1
}

reap_stopped_runner_supervisor() {
  wait "$1"
}

poll_runner_supervisor_stop() {
  local pid="$1"
  local max_polls="$2"
  local poll=0
  local process_status=0

  while [[ "$poll" -lt "$max_polls" ]]; do
    pause_runner_supervisor_poll || return 2
    process_status=0
    runner_supervisor_process_state "$pid" || process_status=$?
    case "$process_status" in
      0) ;;
      1) return 0 ;;
      3)
        # A direct-child zombie cannot become live again, so wait is bounded to
        # reaping already-terminated state (and may harmlessly report reaped).
        reap_stopped_runner_supervisor "$pid" 2>/dev/null || true
        return 0
        ;;
      *) return 2 ;;
    esac
    poll=$((poll + 1))
  done
  return 1
}

stop_runner_supervisor_bounded() {
  local pid="$1"
  local process_status=0
  local poll_status=0
  local signal_name=""
  local max_polls=0

  runner_supervisor_process_state "$pid" || process_status=$?
  case "$process_status" in
    1) return 0 ;;
    3)
      reap_stopped_runner_supervisor "$pid" 2>/dev/null || true
      return 0
      ;;
    0) ;;
    *) return 1 ;;
  esac

  # The second TERM closes the official run.sh gap in which its forwarding trap
  # has a stale helper PID. KILL is restricted to the still-verified direct
  # child, and every phase has a finite poll budget (15 + 15 + 5 seconds).
  for signal_name in TERM TERM KILL; do
    if [[ "$signal_name" == "KILL" ]]; then
      max_polls=5
    else
      max_polls=15
    fi
    if ! signal_runner_supervisor "$signal_name" "$pid" 2>/dev/null; then
      process_status=0
      runner_supervisor_process_state "$pid" || process_status=$?
      case "$process_status" in
        1) return 0 ;;
        3)
          reap_stopped_runner_supervisor "$pid" 2>/dev/null || true
          return 0
          ;;
        *) return 1 ;;
      esac
    fi
    poll_status=0
    poll_runner_supervisor_stop "$pid" "$max_polls" || poll_status=$?
    case "$poll_status" in
      0) return 0 ;;
      1) ;;
      *) return 1 ;;
    esac
  done
  return 1
}

stop_runner_and_exit() {
  local status="$1"
  local supervisor_pid="${runner_supervisor_pid:-}"

  # Prevent signal-trap reentrancy while the finite shutdown protocol runs.
  trap '' INT TERM HUP
  shutdown_uncertain=true
  if [[ "$supervisor_pid" =~ ^[1-9][0-9]*$ ]]; then
    if ! stop_runner_supervisor_bounded "$supervisor_pid"; then
      echo "warning: runner supervisor did not stop conclusively within the bounded signal protocol" >&2
    fi
  elif [[ -n "$supervisor_pid" ]]; then
    echo "warning: invalid runner supervisor PID; preserving shutdown state without signaling" >&2
  fi
  runner_supervisor_pid=""
  exit "$status"
}

validate_local_config_for_id() {
  local expected="$1"
  local phase_label="$2"

  if local_runner_config_present && ! require_local_config_paths_safe; then
    return 1
  fi
  if local_runner_settings_present; then
    require_local_runner_ids_match "$expected"
  elif local_runner_config_present; then
    echo "error: partial local credentials cannot be matched to the ${phase_label} JIT ID; preserving state" >&2
    return 1
  fi
}

read_installed_runner_version() {
  local observed=""

  if ! observed="$(
    "$runner_dir/bin/Runner.Listener" --version 2>/dev/null |
      tr -d '[:space:]'
  )"; then
    echo "error: could not verify the installed GitHub runner version" >&2
    return 1
  fi
  printf '%s\n' "$observed"
}

# `--check` is deliberately read-only with respect to GitHub and every
# recovery/configuration file. It parses all recovery evidence and local
# identities instead of returning a false PASS merely because no process or
# lock currently exists.
if [[ "$check_only" == "true" ]]; then
  if [[ -e "$lock_dir" || -L "$lock_dir" ]]; then
    echo "error: repository-managed Lean session lock already exists: $lock_dir" >&2
    exit 1
  fi
  if [[ -e "$jit_state_tmp" || -L "$jit_state_tmp" ]]; then
    echo "error: temporary JIT recovery evidence exists; --check will not mutate it: $jit_state_tmp" >&2
    exit 1
  fi
  if [[ -e "$jit_state" || -L "$jit_state" ]]; then
    read_jit_state || exit 1
    if [[ "$jit_state_phase" == "pending" ]]; then
      if local_runner_config_present; then
        require_local_config_paths_safe || exit 1
        echo "error: pending JIT recovery has unexpected local credentials; preserving state" >&2
        exit 1
      fi
    else
      validate_local_config_for_id \
        "$jit_state_runner_id" "$jit_state_phase" || exit 1
    fi
    echo "error: valid JIT recovery phase '$jit_state_phase' is pending reconciliation; --check made no remote or local change" >&2
    echo "error: after verifying no conflicting process and removing only a stale host lock, run the launcher without --check in this same runner directory" >&2
    exit 1
  fi
  if [[ -f "$runner_dir/.runner" && ! -L "$runner_dir/.runner" ]]; then
    if ! require_local_config_paths_safe ||
        ! legacy_runner_id="$(local_runner_id_from_file "$runner_dir/.runner")" ||
        ! require_local_runner_ids_match "$legacy_runner_id" ||
        ! local_runner_credentials_present; then
      echo "error: legacy runner registration is incomplete or ambiguous; preserving it" >&2
      exit 1
    fi
    echo "Mac CI runner preflight found a valid legacy registration pending migration; --check made no remote or local change."
    exit 0
  fi
  if local_runner_config_present; then
    require_local_config_paths_safe || exit 1
    echo "error: markerless partial or migrated-only runner configuration remains; --check made no change" >&2
    exit 1
  fi
  require_complete_runner_installation
  require_new_job_host_ready
  installed_runner_version="$(read_installed_runner_version)" || exit 1
  if [[ "$installed_runner_version" != "$runner_version" ]]; then
    echo "error: installed GitHub runner version '$installed_runner_version' does not match pinned version '$runner_version'" >&2
    echo "error: no recovery or local registration remains; rerun setup deliberately before accepting a job" >&2
    exit 1
  fi
  echo "Mac CI runner preflight passed; no JIT runner was registered or started."
  exit 0
fi

trap cleanup_session EXIT
trap 'stop_runner_and_exit 130' INT
trap 'stop_runner_and_exit 143' TERM
trap 'stop_runner_and_exit 129' HUP

# The stable record is written before the registration POST, promoted to
# `registered:<id>` after a complete response, and then to
# `remote-visible:<id>` only after an exact-ID GET binds the same repository,
# runner name, and ID.  Listener startup is forbidden until that visibility
# witness is durable.  Deletion has its own write-ahead phase, so a later 404 is
# authoritative and a crash is reconciled from the last flushed transition.
if [[ -e "$jit_state_tmp" || -L "$jit_state_tmp" ]]; then
  if [[ ! -f "$jit_state_tmp" || -L "$jit_state_tmp" ||
        ! -O "$jit_state_tmp" ]]; then
    echo "error: unsafe temporary JIT recovery record: $jit_state_tmp" >&2
    exit 1
  fi
  unlink "$jit_state_tmp"
fi

if [[ -e "$jit_state" || -L "$jit_state" ]]; then
  if ! read_jit_state; then
    exit 1
  fi
  case "$jit_state_phase" in
    pending)
      if local_runner_config_present; then
        echo "error: pending JIT recovery has unexpected local credentials; preserving state" >&2
        exit 1
      fi
      if ! remove_remote_runner_by_exact_name "$jit_state_repo" "$jit_state_name"; then
        echo "error: pending JIT registration is not conclusively visible/removable by exact repository/name; preserving state" >&2
        echo "error: retry later or inspect/remove the exact recorded runner in GitHub before manually clearing the record" >&2
        exit 1
      fi
      ;;
    registered)
      if ! establish_remote_visibility \
          "$jit_state_repo" "$jit_state_name" "$jit_state_runner_id"; then
        echo "error: registered JIT runner never produced an exact-ID/name visibility witness; preserving state" >&2
        exit 1
      fi
      if ! delete_visible_remote_runner_with_recovery \
          "$jit_state_repo" "$jit_state_name" "$jit_state_runner_id"; then
        echo "error: visible JIT runner is not yet verifiably absent; preserving state" >&2
        exit 1
      fi
      ;;
    remote-visible)
      if ! delete_visible_remote_runner_with_recovery \
          "$jit_state_repo" "$jit_state_name" "$jit_state_runner_id"; then
        echo "error: visible JIT runner is not yet verifiably absent; preserving state" >&2
        exit 1
      fi
      ;;
    remote-delete-requested)
      if ! remote_runner_absent "$jit_state_repo" "$jit_state_runner_id"; then
        echo "error: delete-requested JIT runner is not yet verifiably absent; preserving state" >&2
        exit 1
      fi
      write_jit_state \
        "$jit_state_repo" "$jit_state_name" \
        "remote-removed:${jit_state_runner_id}"
      ;;
    remote-removed)
      ;;
    *)
      echo "error: internal unknown JIT recovery phase; preserving state" >&2
      exit 1
      ;;
  esac
  if [[ "$jit_state_phase" != "pending" ]]; then
    # Remote cleanup is independent of local credential contents.  Complete it
    # first, then preserve the durable `remote-removed:<id>` record if a local
    # marker is partial, symlinked, or names a different runner.  Never erase or
    # operate through ambiguous local state.
    validate_local_config_for_id \
      "$jit_state_runner_id" "$jit_state_phase" || exit 1
  fi
  if local_runner_settings_present; then
    (
      cd "$runner_dir"
      ./config.sh remove --local
    )
  fi
  if local_runner_config_present; then
    echo "error: stale local JIT credentials remain; preserving $jit_state" >&2
    exit 1
  fi
  if ! unlink "$jit_state" || ! /bin/sync; then
    echo "error: could not durably remove the reconciled JIT recovery record" >&2
    exit 1
  fi
fi

# Migrate the legacy persistent registration created by older versions of the
# setup script. Rechecking immediately before removal narrows the unavoidable
# race with external foreground launchers, which do not honor this host lock.
if [[ -f "$runner_dir/.runner" ]]; then
  if ! require_local_config_paths_safe; then
    exit 1
  fi
  if ! legacy_runner_id="$(local_runner_id_from_file "$runner_dir/.runner")"; then
    echo "error: legacy .runner has no unambiguous positive runner identity; preserving it" >&2
    exit 1
  fi
  if ! require_local_runner_ids_match "$legacy_runner_id"; then
    exit 1
  fi
  if ! local_runner_credentials_present; then
    echo "error: legacy runner settings have no primary/migrated credential; refusing a local-only deletion" >&2
    exit 1
  fi
  removal_token="$(
    gh api --method POST \
      "repos/${repo}/actions/runners/remove-token" --jq .token
  )"
  require_no_conflicting_processes "remove the legacy persistent runner"
  echo "Removing the legacy persistent runner registration."
  (
    cd "$runner_dir"
    ./config.sh remove --token "$removal_token"
  )
  unset removal_token
fi

if local_runner_config_present; then
  echo "error: markerless partial or migrated-only runner configuration remains; refusing JIT registration" >&2
  exit 1
fi

# Version rejection is intentionally after stale-JIT reconciliation and legacy
# migration.  A self-updated binary must not strand credentials merely because
# it no longer matches the pin; once local/recovery state is clean, however, no
# new registration is allowed until setup is deliberately repaired.
require_complete_runner_installation
installed_runner_version="$(read_installed_runner_version)" || exit 1
if [[ "$installed_runner_version" != "$runner_version" ]]; then
  echo "error: installed GitHub runner version '$installed_runner_version' does not match pinned version '$runner_version'" >&2
  echo "error: recovery and local registration are clear; rerun setup deliberately before accepting a job" >&2
  exit 1
fi
require_new_job_host_ready

# Revalidate the security boundary immediately before requesting credentials.
# Keep the restrictive umask through Listener startup so any settings or
# credential files the official runner creates are owner-only as well.
assert_private_runner_dir
umask 077

runner_nonce=""
if ! runner_nonce="$(
  /usr/bin/uuidgen |
    /usr/bin/tr '[:upper:]' '[:lower:]' |
    /usr/bin/tr -d '-' |
    /usr/bin/cut -c 1-16
)"; then
  echo "error: could not generate a unique JIT runner name" >&2
  exit 1
fi
runner_name="${runner_label}-$(date -u +%Y%m%dT%H%M%SZ)-${runner_nonce}"
if [[ ! "$runner_nonce" =~ ^[0-9a-f]{16}$ ||
      ! "$runner_name" =~ ^[A-Za-z0-9_.-]+$ ||
      "${#runner_name}" -gt 64 ]]; then
  echo "error: generated JIT runner name is invalid or too long" >&2
  exit 1
fi

# A manually started external runner can ignore the repository lock. Narrow the
# remaining race again at the last point before durable write-ahead and POST.
require_no_conflicting_processes "register the JIT runner"

# Write-ahead recovery is durable before GitHub can create the registration.
write_jit_state "$repo" "$runner_name" "pending"
jit_state_active=true

jit_fields="$(
  gh api --method POST \
    "repos/${repo}/actions/runners/generate-jitconfig" \
    -f "name=${runner_name}" \
    -F "runner_group_id=${runner_group_id}" \
    -f "labels[]=self-hosted" \
    -f "labels[]=macOS" \
    -f "labels[]=ARM64" \
    -f "labels[]=${runner_label}" \
    -f "work_folder=_work" \
    --jq '[.runner.id, .encoded_jit_config] | @tsv'
)"
candidate_jit_runner_id=""
IFS=$'\t' read -r candidate_jit_runner_id jit_config <<< "$jit_fields"
unset jit_fields

if [[ ! "$candidate_jit_runner_id" =~ ^[1-9][0-9]*$ ||
      -z "$jit_config" ]]; then
  echo "error: GitHub did not return a complete JIT runner configuration" >&2
  exit 1
fi

jit_runner_id="$candidate_jit_runner_id"
unset candidate_jit_runner_id
write_jit_state "$repo" "$runner_name" "registered:${jit_runner_id}"
jit_session_created=true

# Never start the official Listener on the strength of the POST response alone.
# The exact-ID endpoint must return this same repository/name/ID tuple, and that
# positive visibility witness must survive an atomic rename plus `/bin/sync`.
# Every later cleanup can then distinguish an authoritative post-visibility 404
# from an eventually-consistent miss immediately after registration.
if ! establish_remote_visibility "$repo" "$runner_name" "$jit_runner_id"; then
  echo "error: the new JIT runner did not become exactly visible; refusing to start it and preserving recovery state" >&2
  exit 1
fi
jit_remote_visible=true

# The official runner reloads `.env` and `.path` from its installation root.
# Pin both files and start its foreground supervisor from an explicit
# environment allowlist so an ambient ELAN_TOOLCHAIN/LEAN_PATH/Lake
# configuration or shell/cloud token cannot alter the build or leak into
# trusted job processes.  The immutable runner root and pinned expected version
# also reach the job so its final pre-Lean gate can detect an automatic update.
# This does not sandbox the account's filesystem or Keychain; use a dedicated
# account for that boundary.
printf '%s\n' \
  'LANG=C.UTF-8' \
  'LC_ALL=C.UTF-8' \
  'LC_CTYPE=C.UTF-8' \
  'GIT_CONFIG_GLOBAL=/dev/null' \
  'GIT_CONFIG_NOSYSTEM=1' \
  'LAKE_CONFIG=/dev/null' \
  'LEAN_NUM_THREADS=1' \
  'OMP_NUM_THREADS=1' \
  'OPENBLAS_NUM_THREADS=1' \
  'MKL_NUM_THREADS=1' \
  'VECLIB_MAXIMUM_THREADS=1' \
  'NUMEXPR_NUM_THREADS=1' \
  'PYTHONNOUSERSITE=1' \
  "YMGAP_RUNNER_DIR=${runner_dir}" \
  "YMGAP_EXPECTED_RUNNER_VERSION=${runner_version}" > "$runner_dir/.env"
printf '%s\n' "$runner_path" > "$runner_dir/.path"
chmod 600 "$runner_dir/.env" "$runner_dir/.path"

echo "Starting ephemeral runner ${runner_name} for exactly one foreground job."
runner_status=0
# Use the official foreground supervisor so an update-request exit is handled
# by the runner's supported update/relaunch path.  The outer launcher signals
# the supervisor PID, and RUNNER_MANUALLY_TRAP_SIG asks run.sh to install its
# official forwarding trap for the helper/Listener process group.  The helper's
# exit code is never used as a completion or remote-absence witness; cleanup is
# based solely on the durable exact-ID visibility/delete state machine above.
/usr/bin/env -i \
  HOME="$HOME" \
  USER="$(/usr/bin/id -un)" \
  LOGNAME="$(/usr/bin/id -un)" \
  PATH="$runner_path" \
  TMPDIR="${TMPDIR:-/tmp}" \
  LANG="C.UTF-8" \
  LC_ALL="C.UTF-8" \
  LC_CTYPE="C.UTF-8" \
  GIT_CONFIG_GLOBAL="/dev/null" \
  GIT_CONFIG_NOSYSTEM="1" \
  LAKE_CONFIG="/dev/null" \
  LEAN_NUM_THREADS="1" \
  OMP_NUM_THREADS="1" \
  OPENBLAS_NUM_THREADS="1" \
  MKL_NUM_THREADS="1" \
  VECLIB_MAXIMUM_THREADS="1" \
  NUMEXPR_NUM_THREADS="1" \
  PYTHONNOUSERSITE="1" \
  SHELL="/bin/bash" \
  TERM="${TERM:-dumb}" \
  RUNNER_MANUALLY_TRAP_SIG="1" \
  YMGAP_LEAN_SESSION_LOCK_HELD="1" \
  YMGAP_LEAN_LOCK_DIR="$lock_dir" \
  YMGAP_RUNNER_DIR="$runner_dir" \
  YMGAP_EXPECTED_RUNNER_VERSION="$runner_version" \
  "$runner_dir/run.sh" --jitconfig "$jit_config" &
runner_supervisor_pid=$!
unset jit_config
wait "$runner_supervisor_pid" || runner_status=$?
runner_supervisor_pid=""
exit "$runner_status"

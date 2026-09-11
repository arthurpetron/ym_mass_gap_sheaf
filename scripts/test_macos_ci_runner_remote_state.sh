#!/usr/bin/env bash
set -euo pipefail

# Pure mocked regression checks for the remote-absence and bounded-shutdown
# proofs in the Mac JIT launcher.  No runner/build process is signalled or
# started and no network or GitHub mutation is performed.  Extracting
# production function blocks keeps these checks tied to the exact
# implementation instead of a test-only copy.

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly launcher="${script_dir}/run_macos_ci_runner.sh"

remote_functions="$(
  /usr/bin/awk '
    /^remote_runner_collection_snapshot_without_id\(\) \{/ { capture = 1 }
    /^remote_runner_visible\(\) \{/ { exit }
    capture { print }
  ' "$launcher"
)"
if [[ -z "$remote_functions" ]]; then
  echo "error: could not extract the production remote-state functions" >&2
  exit 1
fi
eval "$remote_functions"
unset remote_functions

write_state_function="$(
  /usr/bin/awk '
    /^write_jit_state\(\) \{/ { capture = 1 }
    /^read_jit_state\(\) \{/ { exit }
    capture { print }
  ' "$launcher"
)"
cleanup_function="$(
  /usr/bin/awk '
    /^cleanup_session\(\) \{/ { capture = 1 }
    /^runner_supervisor_process_state\(\) \{/ { exit }
    capture { print }
  ' "$launcher"
)"
supervisor_functions="$(
  /usr/bin/awk '
    /^runner_supervisor_process_state\(\) \{/ { capture = 1 }
    /^validate_local_config_for_id\(\) \{/ { exit }
    capture { print }
  ' "$launcher"
)"
if [[ -z "$write_state_function" || -z "$cleanup_function" ||
      -z "$supervisor_functions" ]]; then
  echo "error: could not extract the production durability/cleanup/shutdown functions" >&2
  exit 1
fi

require_fragment() {
  local body="$1"
  local fragment="$2"
  local label="$3"

  if [[ "$body" != *"$fragment"* ]]; then
    echo "error: production launcher lacks required $label guard" >&2
    return 1
  fi
}

require_fragment "$write_state_function" \
  'if ! /bin/chmod 600 "$jit_state_tmp"; then' \
  "temporary-state chmod"
require_fragment "$write_state_function" \
  'if ! /bin/mv -f "$jit_state_tmp" "$jit_state"; then' \
  "atomic state promotion"
require_fragment "$write_state_function" \
  'if ! /usr/bin/cmp -s "$jit_state" <(' \
  "byte-exact state readback"
require_fragment "$write_state_function" \
  'if ! /bin/sync; then' \
  "state durability barrier"
cmp_line="$(
  printf '%s\n' "$write_state_function" |
    LC_ALL=C /usr/bin/awk 'index($0, "/usr/bin/cmp -s") { print NR; exit }'
)"
sync_line="$(
  printf '%s\n' "$write_state_function" |
    LC_ALL=C /usr/bin/awk 'index($0, "if ! /bin/sync; then") { print NR; exit }'
)"
if [[ ! "$cmp_line" =~ ^[1-9][0-9]*$ ||
      ! "$sync_line" =~ ^[1-9][0-9]*$ ||
      "$cmp_line" -ge "$sync_line" ]]; then
  echo "error: byte-exact JIT-state readback must precede the durability barrier" >&2
  exit 1
fi
require_fragment "$cleanup_function" \
  'if [[ "${shutdown_uncertain:-false}" == "true" ]]; then' \
  "interrupt-uncertainty cleanup"
require_fragment "$cleanup_function" \
  'retaining $lock_dir after trapped descendant-uncertain shutdown' \
  "interrupt-uncertainty host-lock retention"

eval "$supervisor_functions"
unset supervisor_functions write_state_function cleanup_function cmp_line sync_line

mock_counter_file="$(
  /usr/bin/mktemp "${TMPDIR:-/tmp}/ymgap-runner-remote-mock.XXXXXX"
)"
cleanup_mock_counter() {
  local original_status="$?"
  trap - EXIT
  /usr/bin/unlink "$mock_counter_file" 2>/dev/null || true
  exit "$original_status"
}
trap cleanup_mock_counter EXIT

mock_scenario=""

reset_mock() {
  mock_scenario="$1"
  printf '0\n' > "$mock_counter_file"
}

next_mock_call() {
  local current=""

  IFS= read -r current < "$mock_counter_file"
  [[ "$current" =~ ^(0|[1-9][0-9]*)$ ]] || return 1
  current=$((current + 1))
  printf '%s\n' "$current" > "$mock_counter_file"
  printf '%s\n' "$current"
}

emit_collection_a() {
  # Deliberately unsorted; the production snapshot must canonicalize it.
  printf 'M\t2\tarray\t2\nI\t12\nI\t11\n'
}

emit_collection_a_sorted() {
  printf 'M\t2\tarray\t2\nI\t11\nI\t12\n'
}

emit_collection_b() {
  # Same cardinality and individually valid, but a page-shifted membership.
  printf 'M\t2\tarray\t2\nI\t11\nI\t13\n'
}

gh() {
  local call_no=""
  local args=" $* "

  call_no="$(next_mock_call)" || return 97
  if [[ "$call_no" -eq 1 ]]; then
    [[ "$args" == *" --method DELETE "* ]] || return 96
    [[ "$mock_scenario" == "delete-success" ]] && return 0
    return 1
  fi

  if [[ "$call_no" -eq 2 || "$call_no" -eq 4 ]]; then
    [[ "$args" == *" --method GET "* &&
       "$args" == *" --paginate "* ]] || return 95
    case "$mock_scenario:$call_no" in
      stable-404:2|exact-200:2|exact-non404:2|multi-status:2|page-shift:2)
        emit_collection_a
        ;;
      stable-404:4|exact-200:4|exact-non404:4|multi-status:4)
        emit_collection_a_sorted
        ;;
      page-shift:4)
        emit_collection_b
        ;;
      auth-masked:2)
        printf 'HTTP/2.0 404 Not Found\n' >&2
        return 1
        ;;
      target-present:2)
        printf 'M\t2\tarray\t2\nI\t11\nI\t99\n'
        ;;
      duplicate-id:2)
        printf 'M\t2\tarray\t2\nI\t11\nI\t11\n'
        ;;
      malformed-page:2)
        printf 'M\t2\tarray\t1\nI\t11\n'
        ;;
      *) return 94 ;;
    esac
    return 0
  fi

  if [[ "$call_no" -eq 3 ]]; then
    [[ "$args" == *" --method GET "* &&
       "$args" == *" --include "* &&
       "$args" != *" --paginate "* ]] || return 93
    case "$mock_scenario" in
      stable-404|page-shift)
        printf 'HTTP/2.0 404 Not Found\n' >&2
        return 1
        ;;
      exact-200)
        printf 'HTTP/2.0 200 OK\n\n{"id":99,"name":"still-present"}\n'
        return 0
        ;;
      exact-non404)
        printf 'HTTP/2.0 403 Forbidden\n' >&2
        return 1
        ;;
      multi-status)
        printf 'HTTP/1.1 200 Connection-established\n\nHTTP/2.0 404 Not Found\n' >&2
        return 1
        ;;
      *) return 92 ;;
    esac
  fi
  return 91
}

expect_remote_absence() {
  local scenario="$1"
  local expected_status="$2"
  local expected_calls="$3"
  local observed_status=0
  local observed_calls=""

  reset_mock "$scenario"
  if remote_runner_absent "owner/repository" "99"; then
    observed_status=0
  else
    observed_status=$?
  fi
  IFS= read -r observed_calls < "$mock_counter_file"
  if [[ "$observed_status" -ne "$expected_status" ||
        "$observed_calls" -ne "$expected_calls" ]]; then
    echo "error: scenario '$scenario' returned status/calls ${observed_status}/${observed_calls}; expected ${expected_status}/${expected_calls}" >&2
    return 1
  fi
}

expect_remote_absence delete-success 0 1
expect_remote_absence stable-404 0 4
expect_remote_absence page-shift 1 4
expect_remote_absence auth-masked 1 2
expect_remote_absence exact-200 1 3
expect_remote_absence exact-non404 1 3
expect_remote_absence multi-status 1 3
expect_remote_absence target-present 1 2
expect_remote_absence duplicate-id 1 2
expect_remote_absence malformed-page 1 2

mock_stop_scenario=""
mock_state_calls=0
mock_signal_count=0
mock_signal_log=""
mock_pause_count=0
mock_reap_count=0

reset_stop_mock() {
  mock_stop_scenario="$1"
  mock_state_calls=0
  mock_signal_count=0
  mock_signal_log=""
  mock_pause_count=0
  mock_reap_count=0
}

# Override only the four side-effecting/liveness adapters.  The bounded control
# flow under test remains the exact production function extracted above.
runner_supervisor_process_state() {
  mock_state_calls=$((mock_state_calls + 1))
  case "$mock_stop_scenario" in
    term-gap)
      [[ "$mock_signal_count" -lt 2 ]] && return 0
      return 3
      ;;
    unkillable) return 0 ;;
    already-gone) return 1 ;;
    uncertain) return 2 ;;
    *) return 2 ;;
  esac
}

signal_runner_supervisor() {
  local signal_name="$1"

  mock_signal_count=$((mock_signal_count + 1))
  if [[ -n "$mock_signal_log" ]]; then
    mock_signal_log="${mock_signal_log} "
  fi
  mock_signal_log="${mock_signal_log}${signal_name}"
  return 0
}

pause_runner_supervisor_poll() {
  mock_pause_count=$((mock_pause_count + 1))
  return 0
}

reap_stopped_runner_supervisor() {
  mock_reap_count=$((mock_reap_count + 1))
  return 0
}

expect_bounded_stop() {
  local scenario="$1"
  local expected_status="$2"
  local expected_signals="$3"
  local expected_pauses="$4"
  local expected_reaps="$5"
  local expected_states="$6"
  local observed_status=0

  reset_stop_mock "$scenario"
  if stop_runner_supervisor_bounded 4242; then
    observed_status=0
  else
    observed_status=$?
  fi
  if [[ "$observed_status" -ne "$expected_status" ||
        "$mock_signal_log" != "$expected_signals" ||
        "$mock_pause_count" -ne "$expected_pauses" ||
        "$mock_reap_count" -ne "$expected_reaps" ||
        "$mock_state_calls" -ne "$expected_states" ]]; then
    echo "error: bounded-stop scenario '$scenario' observed status/signals/pauses/reaps/states ${observed_status}/'$mock_signal_log'/${mock_pause_count}/${mock_reap_count}/${mock_state_calls}; expected ${expected_status}/'$expected_signals'/${expected_pauses}/${expected_reaps}/${expected_states}" >&2
    return 1
  fi
}

# The first case models run.sh's stale-helper-PID TERM gap.  The second proves
# the total wait budget is finite even when the direct child never disappears.
expect_bounded_stop term-gap 0 "TERM TERM" 16 1 17
expect_bounded_stop unkillable 1 "TERM TERM KILL" 35 0 36
expect_bounded_stop already-gone 0 "" 0 0 1
expect_bounded_stop uncertain 1 "" 0 0 1

echo "Mac CI remote-state mocked checks passed (10 scenarios)."
echo "Mac CI bounded-supervisor mocked checks passed (4 scenarios, no signals or sleeps)."

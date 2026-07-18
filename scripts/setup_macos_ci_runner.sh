#!/usr/bin/env bash
set -euo pipefail

# Repository-scoped, manually started GitHub Actions runner for the YMGap
# all-module Lean build.  This script intentionally does not install a service:
# the runner remains offline until the owner starts it in a foreground terminal.

readonly repo="${YMGAP_GITHUB_REPOSITORY:-arthurpetron/ym_mass_gap_sheaf}"
readonly runner_label="${YMGAP_RUNNER_LABEL:-ymgap-m4max}"
readonly runner_dir="${YMGAP_RUNNER_DIR:-$HOME/.local/share/ymgap-actions-runner}"
readonly runner_version="2.335.1"
readonly archive_name="actions-runner-osx-arm64-${runner_version}.tar.gz"
readonly archive_path="${TMPDIR:-/tmp}/${archive_name}"
readonly download_url="https://github.com/actions/runner/releases/download/v${runner_version}/${archive_name}"
readonly expected_sha256="e1a9bc7a3661e06fa0b129d15c2064fe65dc81a431001d8958a9db1409b73769"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo "error: this setup is pinned for Apple-silicon macOS" >&2
  exit 1
fi

command -v gh >/dev/null || {
  echo "error: GitHub CLI (gh) is required" >&2
  exit 1
}
gh auth status >/dev/null

mkdir -p "$runner_dir"

if [[ ! -x "$runner_dir/config.sh" ]]; then
  curl --fail --location --retry 3 --output "$archive_path" "$download_url"
  actual_sha256="$(shasum -a 256 "$archive_path" | awk '{ print $1 }')"
  if [[ "$actual_sha256" != "$expected_sha256" ]]; then
    echo "error: GitHub runner archive checksum mismatch" >&2
    exit 1
  fi
  tar -xzf "$archive_path" -C "$runner_dir"
fi

if [[ ! -f "$runner_dir/.runner" ]]; then
  registration_token="$(
    gh api --method POST \
      "repos/${repo}/actions/runners/registration-token" --jq .token
  )"
  "$runner_dir/config.sh" \
    --unattended \
    --url "https://github.com/${repo}" \
    --token "$registration_token" \
    --name "$runner_label" \
    --labels "$runner_label" \
    --work _work
fi

gh variable set YMGAP_LEAN_RUNNER \
  --repo "$repo" \
  --body "$runner_label"

echo
echo "Runner registered but intentionally offline."
echo "When the Mac is idle and on AC power, accept exactly one CI job with:"
echo "  scripts/run_macos_ci_runner.sh"

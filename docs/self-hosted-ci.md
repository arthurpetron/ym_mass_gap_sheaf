# Safe self-hosted Lean CI on Apple silicon

The authoritative all-module Lean job is routed to a repository-scoped
self-hosted runner instead of a paid GitHub-hosted machine.  The runner is
registered once but is deliberately **not** installed as a macOS service.  It
accepts exactly one job after its foreground launcher is run, so a full build
cannot begin unexpectedly while the Mac is in normal use.

## One-time setup

From the repository root:

```text
scripts/setup_macos_ci_runner.sh
```

The setup script:

1. downloads the pinned official GitHub runner for macOS ARM64;
2. verifies its published SHA-256 checksum;
3. registers it only with `arthurpetron/ym_mass_gap_sheaf`, under the custom
   label `ymgap-m4max`; and
4. sets the repository variable `YMGAP_LEAN_RUNNER` to that label.

It installs under `~/.local/share/ymgap-actions-runner` by default.  Override
that location with `YMGAP_RUNNER_DIR` if needed.  No registration token is
stored in this repository.

## Accepting a queued build

Connect the Mac to AC power, close other Lean/Lake/pytest work, and run:

```text
scripts/run_macos_ci_runner.sh
```

To check the same host preconditions without bringing the runner online, use
`scripts/run_macos_ci_runner.sh --check`.

The runner stays in the foreground and exits after exactly one job.  Control-C
takes it offline earlier.  If the runner is offline, matching jobs wait in
GitHub's queue; they do not fall back to a paid runner.

## Host-safety contract

Both the launcher and workflow fail closed when another Lean/Lake/pytest
process is active or the Mac is not on AC power.  The workflow additionally:

- requires at least 24 GiB installed RAM and approximately 24 GiB currently
  available according to macOS memory pressure;
- runs exactly one Lean worker with the repository's 20 GB per-process cap;
- lowers the build process priority with `nice`;
- uses `caffeinate` only for the duration of the build;
- keeps at most one all-module run current;
- preserves `lean/.lake` locally between trusted main builds, avoiding paid
  GitHub cache storage, while manual `clean_build=true` dispatches delete it;
- uploads the build log only after failure, retaining it for three days; and
- gives the workflow token read-only repository contents permission and does
  not persist Git credentials on the Mac.

Only trusted pushes to `main` and manual dispatches whose selected ref is also
`main` enter this workflow.  Routing requires all four labels `self-hosted`,
`macOS`, `ARM64`, and the custom repository variable, so changing that variable
to a hosted label cannot incur hosted compute. Pull-request code is deliberately
excluded from the persistent self-hosted machine. The repository is currently
private; if it is ever made public, do not broaden this trigger without an
isolated ephemeral runner.

## Cost and operational limits

GitHub does not charge Actions compute minutes for self-hosted runners, though
the owner pays the machine and electricity costs.  Artifact storage can still
be billable, which is why successful logs and remote Lake caches are not
uploaded.

The GitHub account must still be operational enough to schedule Actions.  A
billing lock can prevent even a free self-hosted job from being dispatched; if
that happens, repair or downgrade the account plan before retrying.

GitHub references: [adding a self-hosted runner](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/add-runners),
[using self-hosted labels](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/use-in-a-workflow),
[secure use](https://docs.github.com/en/actions/reference/security/secure-use),
and [Actions billing](https://docs.github.com/en/billing/concepts/product-billing/github-actions).

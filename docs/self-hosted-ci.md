# Safe self-hosted Lean CI on Apple silicon

The authoritative all-module Lean job is routed to a repository-scoped
self-hosted runner instead of a paid GitHub-hosted machine.  The runner is
deliberately **not** installed as a macOS service or registered persistently.
Its foreground launcher asks GitHub for a just-in-time configuration; GitHub
assigns that ephemeral registration at most one job and removes it afterward,
so no full build can begin while the foreground launcher is offline.  While it
is online, however, it can accept any matching queued job; start it only for a
known trusted run and exit it before returning the Mac to normal use.
Workflow concurrency independently permits at most one full-library job at a
time and does not cancel an in-progress build when a newer checkpoint is
pushed.

## One-time setup

From the repository root:

```text
scripts/setup_macos_ci_runner.sh
```

Prerequisites are an authenticated GitHub CLI and an existing `elan`
installation.  The workflow selects the repository's pinned Lean toolchain but
deliberately refuses to execute a mutable remote `elan` bootstrap script on the
personal machine.

The setup script:

1. downloads the pinned official GitHub runner for macOS ARM64;
2. verifies the downloaded archive's published SHA-256 checksum and verifies
   the exact pinned executable version for both fresh and preexisting
   installations;
3. does **not** register a persistent runner; and
4. sets the repository variable `YMGAP_LEAN_RUNNER=ymgap-m4max` for the
   short-lived runner label.

Before it touches the runner installation, setup conclusively checks the
shared runner/Lean/Lake/pytest process fence and atomically acquires the same
fixed per-user host lock used by builds and the foreground launcher.  It holds
that real, account-owned, owner-only lock through runner-root creation,
permission repair, download, extraction, executable-version inspection, and
the repository-variable update.  Normal and error exits release it only after
a conclusive clear process scan; process-list failure or an
`INT`/`TERM`/`HUP` interruption deliberately retains the lock for operator
inspection.

It installs under `~/.local/share/ymgap-actions-runner` by default.  Override
that location with an exported `YMGAP_RUNNER_DIR` if needed; the override must
be an absolute path using only safe path characters, with no spaces, empty
components, or `.`/`..` components.  The same exported value must be present
for both setup and every launcher invocation.  No registration token is stored
in this repository.

## Accepting a queued build

CI checks out the pushed `main` commit from GitHub.  It never builds
uncommitted changes from the operator's ordinary working copy.  Connect the Mac
to AC power, close other Lean/Lake/pytest work, and use this sequence from the
repository root:

```text
scripts/run_macos_ci_runner.sh --check
git push origin main
git rev-parse HEAD
gh run list --repo arthurpetron/ym_mass_gap_sheaf --workflow lean-audit.yml --branch main --limit 5 --json databaseId,headSha,status,event,displayTitle
```

A Lean-relevant push queues the workflow automatically.  Find the entry whose
`headSha` equals the preceding `git rev-parse HEAD` output.  Start the listener
only when that entry's status is `queued`; if it is already `in_progress` or
`completed`, inspect that run instead.  **Do not manually dispatch a second run
when an entry for that commit already exists.**  If no entry for that commit
appears after a brief refresh because the push did not match the workflow's
Lean-relevant path filter, explicitly queue one cached audit and list it again:

```text
gh workflow run lean-audit.yml --repo arthurpetron/ym_mass_gap_sheaf --ref main -f clean_build=false
gh run list --repo arthurpetron/ym_mass_gap_sheaf --workflow lean-audit.yml --branch main --limit 5 --json databaseId,headSha,status,event,displayTitle
```

Only after exactly the intended trusted `main` run is queued, start its one-job
foreground listener:

```text
scripts/run_macos_ci_runner.sh
```

Keep its terminal visible, and if it does not claim that run promptly, press
Control-C.  Exit the launcher before resuming normal use of the Mac: while the
JIT listener is online, it can accept a later job carrying the same labels.
The initial `--check` command above tests the same host preconditions without
registering or starting a runner. It is strictly read-only: a well-formed
recovery record is reported as pending reconciliation, malformed or partial
state fails closed and is preserved, and a safe legacy registration is
reported as pending migration rather than silently removed.

The launcher creates a uniquely named repository-scoped JIT runner carrying
the stable `ymgap-m4max` label and runs it in the foreground. On normal exit it
requests and verifies remote/local cleanup; successful cleanup removes the
credentials and recovery marker, while a failed verification retains recovery
evidence and makes the next launch fail closed or recover the same identity.
On `INT`, `TERM`, or `HUP`, the launcher applies a finite `TERM`, `TERM`,
`KILL` protocol only to its still-verified direct supervisor child (at most
35 one-second polls). It then conservatively skips registration cleanup and
retains both the recovery record and host lock, because no finite process-name
list can prove that an arbitrary action descendant was not orphaned. Follow the
stale-lock no-process procedure below before the next recovery launch. Any
stale JIT state or valid legacy registration is reconciled
before the launcher applies its exact pinned-version rejection, so a supported
self-update cannot strand credentials behind a version check. Once recovery
and local registration are clear, a mismatched binary is rejected while still
offline. It then uses the official `run.sh` foreground
supervisor, including that supervisor's supported update/relaunch handling.
The workflow rechecks the exact pinned `Runner.Listener` version in the final
host gate immediately before Lean; a self-update therefore prevents
compilation until the pin, checksum, setup, and workflow are deliberately
updated together. GitHub itself guarantees at most one assigned job for this
JIT registration. Control-C initiates the bounded conservative shutdown just
described; workflow concurrency independently leaves only one matching
full-library job running and at most one current checkpoint pending. If no JIT
runner is online,
matching jobs wait in GitHub's queue; they do not fall back to a paid runner.

## Host-safety contract

Both the launcher and workflow sample the host at launch and immediately before
the build, and fail closed when another Lean/Lake/pytest process is active
(including `python3 -m pytest`) or the Mac is not then on AC power. Outside the
intentionally inherited foreground-runner session, runner supervisors,
listeners, workers, plugin hosts, services, helpers, and updater scripts such as
`_update.sh`/`update.sh` are also conflicting processes.  Inside that inherited
session the runner is expected, so the lock wrapper rechecks only the shared
high-load pattern immediately before `exec`.  The workflow additionally:

- requires at least 32 GiB installed RAM and approximately 32 GiB currently
  available according to macOS memory pressure;
- refuses to run if the operating system process list itself cannot be
  inspected, rather than treating that infrastructure error as “no conflict”;
- uses a fresh just-in-time registration which GitHub can assign at most one
  job, rather than the runner's deprecated persistent `--once` mode;
- holds an atomic host lock for the entire foreground session; every
  repository-managed Make target which can invoke Lean/Lake or pytest honors
  the same lock, and the workflow repeats AC, memory, and process checks
  immediately before compilation;
- runs a bounded static host-load guard over tracked and untracked,
  non-ignored repository executable entry points, rejecting Lean/Lake/pytest
  routes that bypass the shared lock or one-thread caps, and pure mocked
  regressions reject authorization-masked 404s, pagination shifts, malformed
  collections, non-404 or multi-status runner-identity probes, and unbounded
  supervisor shutdown behavior without starting or signalling a process;
- runs exactly one Lean worker with the repository's 20 GB per-process cap;
- lowers the build process priority with `nice`;
- uses `caffeinate -s`/`-m` only for the duration of the build; its system-sleep
  assertion is valid only on AC, so unplugging the Mac permits ordinary sleep
  instead of forcing a battery-draining awake state;
- keeps at most one all-module run current;
- preserves `lean/.lake` locally between trusted main builds, avoiding paid
  GitHub cache storage; manual dispatches also retain it by default, while the
  exceptional `clean_build=true` option deletes it for a cache-independent
  reproducibility run;
- attempts to upload the build log only after failure or cancellation,
  retaining it for three days; a hard timeout, lost runner, or forced
  cancellation can prevent that best-effort final step;
- gives the workflow token read-only repository contents permission and does
  not persist Git credentials on the Mac; and
- pins both GitHub-maintained actions to verified immutable commit SHAs.

The authoritative build log is itself fail-closed evidence.  Its exact
provenance fingerprint covers every default-build Lean source and guard root,
the pinned Lean toolchain and Lake inputs, the Make entry point, and the
audit/import-selection scripts.  The audit requires the source-located
diagnostic from every current executable axiom gate, with its exact
multiplicity, plus Lake's terminal success marker.  A truncated log, or one
from stale sources, toolchain, Lake configuration, Make wiring, or audited
scripts, is rejected rather than reused.

The runner's `_diag` logs remain on the Mac for troubleshooting.  The workflow
log remains in the GitHub run, and the failed or cancelled Lean build log is a
three-day artifact when GitHub can run the best-effort upload step.  The
launcher starts the official `run.sh` supervisor with a minimal environment
allowlist and pins its `.env`/`.path`, so ambient Lean/Lake overrides,
SSH-agent access, and shell or cloud-token variables are not inherited by job
processes.  It also disables account-global Git configuration, the
account-global Lake configuration, and Python user-site packages for the job.
This environment sanitization is why the pinned project toolchain and local
import path, rather than an operator-shell override, control the build.

The lock serializes repository-managed entry points, not arbitrary executables
on the operating system.  A separately launched bare `lean`, `lake`, or another
project's build cannot be prevented atomically; the immediate process recheck
and the rule to avoid bare invocations remain part of the operator contract.
If a process is killed so abruptly that the empty lock directory remains, first
verify that no GitHub runner supervisor/helper/listener/worker/plugin host,
Lean, Lake, or pytest process exists and then remove only the stale directory
printed by the launcher.

Before asking GitHub to create a JIT registration, the launcher atomically
writes an owner-only recovery record containing the repository, unique runner
name, and `pending` phase. A complete POST response promotes it to
`registered:<id>`, but the Listener still does not start: a bounded exact-ID
GET must first return the same recorded name and ID, after which the launcher
durably records `remote-visible:<id>`. Cleanup then records
`remote-delete-requested:<id>` before deletion and
`remote-removed:<id>` only after verified absence. Every accepted deletion 404
follows a durable positive exact-ID visibility witness and two independently
acquired and identical completely paginated repository-runner snapshots whose
structurally valid unique IDs omit that exact ID, with exactly one well-formed
HTTP status line carrying the exact-ID 404 bracketed between those successful
reads. This rejects page-shift races, authorization- or repository-masked
404s, and ambiguous intermediary/redirect response chains containing multiple
status lines. The official `run.sh` helper's status and disappearance
of local settings are never treated as completion evidence. Every atomic
promotion is followed by `/bin/sync`; only verified remote and local cleanup
removes the record. Thus a lost API response, power loss, or untrappable
`SIGKILL` can be reconciled from the last durable phase by exact name or ID on
the next conflict-free launch. Legacy `completed` and pre-visibility deletion records
are deliberately downgraded to conservative unconfirmed registrations and
must regain exact visibility before a 404 can be accepted. If the atomic lock
was already acquired, perform the documented no-process check and remove only
that stale empty lock directory before relaunching. Every baseline or migrated
local identity must match the recorded ID. Ambiguous, mismatched,
credentials-only, symlinked, or otherwise partial state is preserved and
rejected rather than guessed. Do not switch runner directories while any such
state or local registration remains; reconcile the same validated root first.

The JIT runner still executes as the macOS account which starts it.  Trusted
`main` code therefore has that account's filesystem access even though the
GitHub workflow token is read-only and ambient shell variables are stripped.
It can still read same-account files and may be able to use same-account
Keychain credentials or invoke explicitly located tools.  For isolation
against a compromised GitHub account or trusted branch, run the launcher from
a dedicated non-admin macOS account with no personal SSH keys, Keychain items,
Dropbox mounts, or other credentials.  The current same-account setup is scoped
to trusted-main crash/cost protection, not a hostile-code sandbox.  The
installer makes the runner root owner-only (`0700`).

Only trusted pushes to `main` and manual dispatches whose selected ref is also
`main` enter this workflow.  Routing requires all four labels `self-hosted`,
`macOS`, `ARM64`, and the custom repository variable, so changing that variable
to a hosted label cannot incur hosted compute. Pull-request code is deliberately
excluded from the personal machine.  Labels are routing selectors, not an
authorization boundary: a repository-scoped JIT registration is not bound to
this workflow file or ref.  Every actor and workflow able to queue a job with
these matching labels must therefore be trusted, and repository access and
branch protection are part of the security boundary.  For stronger isolation,
use an organization runner group restricted to selected workflows or a
dedicated disposable account and host.  The repository is currently private;
if it is ever made public, do not broaden this trigger without a fully isolated
disposable machine.

## Cost and operational limits

GitHub does not bill Actions compute-minute usage for jobs executed on
self-hosted runners.  The owner still bears the local machine, electricity,
network, wear, and maintenance costs, and GitHub artifact storage can still be
billable.  Successful logs and remote Lake caches are therefore not uploaded.

Use ordinary cached runs for mathematical checkpoints.  Reserve
`clean_build=true` for a pinned toolchain change, Lake/source-selection/cache
contract change, concrete evidence of stale dependency tracking, or an
occasional milestone attestation.  A clean build is not required on every
commit: Lake revalidates changed sources and their reverse dependencies, while
the static import guard verifies that every production source remains selected.
Some generated exact-rational certificate tranches take more than an hour from
a cold cache, and a complete one-worker clean job may run beyond six hours.
The workflow therefore allows up to eight hours without weakening its
one-worker or memory caps.  Keep the Mac on AC power and leave the manually
started foreground runner visible for the entire exceptional clean run.

The GitHub account must still be operational enough to schedule Actions.  A
billing lock can prevent even a free self-hosted job from being dispatched; if
that happens, repair or downgrade the account plan before retrying.

GitHub references: [self-hosted runner reference and ephemeral guarantee](https://docs.github.com/en/actions/reference/runners/self-hosted-runners),
[adding a self-hosted runner](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/add-runners),
[using self-hosted labels](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/use-in-a-workflow),
[secure use](https://docs.github.com/en/actions/reference/security/secure-use),
and [Actions billing](https://docs.github.com/en/billing/concepts/product-billing/github-actions).

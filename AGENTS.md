# Repository Agent Contract

These instructions apply to every agent and automation working in this
repository.

## Machine safety is a correctness requirement

Computationally demanding work is encouraged. Destabilizing the host is not.

- Never run bare `lake build`, `lake env lean`, or another direct Lean compiler
  command. Use `make lean-build`, a monitored Make target, or
  `python3 scripts/safe_lean_build.py`.
- The monitored launcher normally uses two workers on the 64 GiB development
  Mac and one on smaller hosts. It reserves operating-system headroom, watches
  memory pressure and swap, and refuses the crash-causing third worker on the
  64 GiB machine.
- Run only one Lean build at a time. The launcher enforces this with a
  repository lock; do not bypass or remove the lock.
- Prefer the narrowest relevant target. Run a full build/audit only when the
  task genuinely requires repository-wide verification.
- If the launcher stops a build for pressure, let the machine recover and
  resume with `--jobs 1`. Do not immediately restart the same parallel build.
- Do not raise worker counts, memory ceilings, swap thresholds, or reduce the
  OS reserve without explicit user authorization and a new capacity analysis.
- Never infer safety from silent compiler output. The telemetry, not elapsed
  time or lack of errors, determines whether a run may continue.

The incident record and supported commands are in
`docs/lean-build-safety.md`.

## Lean constructivity contract

Before changing anything under `lean/`, read and follow `lean/AGENTS.md` in
full. Its constructivity, axiom-gate, honest-hole, and frontier-honesty rules
remain mandatory in addition to the machine-safety rules above.

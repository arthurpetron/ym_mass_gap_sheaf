# Repository Agent Contract

These instructions apply to every agent and automation working in this
repository.

## Goal-directed execution

Read the opening "Whole-project goal and live completion map" and "Goal-mode
execution instructions" in `work_plan.md` before selecting a proof frontier.
They distinguish the unchanged Clay target from the current working subgoal.
Prefer a short, causally useful mathematical argument over additional proof
scaffolding. Every increment must identify its actual consumer and what remains
unproved. The constructive contract and machine-safety rules below are unchanged.

## Stable user-facing progress chart

`docs/PROJECT-STATUS.md` is the single source for ASCII progress charts.
Read it before every chart and reuse its exact chart block, fixed node labels,
layout, IDs and status meanings. Do not redesign or paraphrase the diagram
between updates. Keep the whole-project goal visible every time. `[x]` means
the EXACT displayed claim has a kernel-checked proof in its recorded scope;
`[ ]` remains open. Activity is separate from proof status. Partial results
and conditional consumers do not close broader goal nodes. Record evidence
and the delta from the previous chart. Necessary structural corrections need
a versioned old-to-new migration and user-facing explanation, never silent
changes of labels, symbols or mathematical scope.

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
- During a live long-running job, space manual status checks about five minutes
  apart and use the intervals for independent mathematics, source review, or
  targeted research. Keep automatic safety telemetry running continuously.
  Checks that finish in the initial tool call need no artificial waiting period.

The incident record and supported commands are in
`docs/lean-build-safety.md`.

## Lean constructivity contract

Before changing anything under `lean/`, read and follow `lean/AGENTS.md` in
full. Its constructivity, axiom-gate, honest-hole, and frontier-honesty rules
remain mandatory in addition to the machine-safety rules above.

## Literature review cadence

- Routine arXiv math-ph listing reviews must be at least 12 hours apart.
  A new goal turn, proof frontier, or reviewer does not reset this interval.
- Before browsing, read the latest `audits/RESEARCH-MATH-PH-*.md` report and
  its last-completed-scan timestamp. Reuse the saved findings between scans;
  do not repeatedly fetch or re-screen the same abstracts.
- Record each completed scan's UTC time and earliest next routine refresh
  in its report. An eligible refresh is optional, not a reason to interrupt
  productive proof work. Coordinate reviewers so only one performs a scan.
- Explicit requests to inspect a particular paper may be handled separately;
  they do not authorize another full listing scan.

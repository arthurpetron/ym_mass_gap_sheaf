# Repository agent instructions

## Machine-safety contract (non-negotiable)

This repository contains generated exact-rational Lean certificates whose kernel
checks can consume several GB per worker; the heaviest known module has consumed
about 15 GB. Uncapped Lake builds have twice exhausted the host and crashed the
MacBook Pro. Protecting the host takes precedence over verification throughput.

- Never run bare `lake build`, `lake env lean YMGap.lean`, `make test`, a full
  `pytest` suite, or multiple build/test commands concurrently.
- Start with static inspection. Then run the smallest relevant test or Lean
  target, with one worker. For Lean use, from `lean/`,
  `LEAN_NUM_THREADS=1 lake build <Module.Target>`. For Python, run one named test
  file or test node and cap numerical-library threads with
  `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
  VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1`.
- Before any compile/test, check whether another `lean`, `lake`, or `pytest`
  process is already active. Do not start a competing run and do not kill a
  user-owned process; report the conflict.
- A full-tree build, full test suite, axiom audit, or statement/frontier guard is
  a separate high-load operation. Run it only when the user explicitly approves
  that run, after targeted checks pass, and use `make lean-build LEAN_JOBS=1`
  (or the corresponding target with `LEAN_JOBS=1`). Never exceed
  `LEAN_JOBS=3` on this host.
- The per-process `-M 20480` ceiling in `lean/lakefile.toml` is mandatory. A
  higher ceiling such as `-M 40960`, or any removal/bypass of the ceiling,
  requires explicit user approval for that specific run.
- If a targeted check approaches the memory ceiling, swaps heavily, stalls, or
  causes thermal pressure, stop it and report the last verified state. Do not
  retry with more workers or a higher limit automatically.
- If verification is intentionally not run for safety, say so precisely. Never
  describe a historical green build recorded in the work plan as a build
  re-verified in the current session.

The Lean constructivity and frontier-honesty contract in `lean/AGENTS.md` also
applies to every change under `lean/`.

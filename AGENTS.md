# Repository agent instructions

## Machine-safety contract (non-negotiable)

This repository contains generated exact-rational Lean certificates whose kernel
checks can consume several GB per worker; the heaviest known module has consumed
about 15 GB. Uncapped Lake builds have twice exhausted the host and crashed the
MacBook Pro. Protecting the host takes precedence over verification throughput.

- Never run bare `lake build`, `lake env lean YMGap.lean`, `make test`, a full
  `pytest` suite, or multiple build/test commands concurrently.
- Start with static inspection. Then run the smallest relevant test or Lean
  target, with one worker. For Lean use the repository lock wrapper from the
  repository root:
  `scripts/with_lean_session_lock.sh lean env LEAN_NUM_THREADS=1 lake build <Module.Target>`.
  For Python, run one named test file or test node through the same lock and cap
  numerical-library threads:
  `scripts/with_lean_session_lock.sh . env OMP_NUM_THREADS=1
  OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
  NUMEXPR_NUM_THREADS=1 pytest <file-or-node>`.
- Before any compile/test, check whether another GitHub runner
  supervisor/helper/listener/worker/plugin host, `lean`, `lake`, or `pytest` process is
  already active. Do not start a competing run
  and do not kill a user-owned process; report the conflict.
- Do not bypass `scripts/with_lean_session_lock.sh` or the locked Make targets.
  The lock serializes repository-managed entry points; because it cannot stop
  an arbitrary bare process, the process check remains mandatory.
- After Control-C, TERM, HUP, or an abrupt child failure, never remove a
  retained lock until process inspection conclusively shows that no
  GitHub runner supervisor/helper/listener/worker/plugin host, Lean, Lake, or pytest
  process survives.
- A full-tree build, full test suite, axiom audit, or statement/frontier guard is
  a separate high-load operation. Run it only when the user explicitly approves
  that run, after targeted checks pass, and use `make lean-build LEAN_JOBS=1`
  (or the corresponding target with `LEAN_JOBS=1`). `LEAN_JOBS=1` is a hard
  repository invariant on this host; do not raise or bypass it.
- The per-process `-M 20480` ceiling in `lean/lakefile.toml` is mandatory. A
  higher ceiling such as `-M 40960`, or any removal/bypass of the ceiling,
  requires explicit user approval for that specific run.
- If a targeted check approaches the memory ceiling, swaps heavily, stalls, or
  causes thermal pressure, stop it and report the last verified state. Do not
  retry with more workers or a higher limit automatically.
- Never `#eval`, `#reduce`, or otherwise materialize a Cartesian Lean
  enumerator such as `boundedEdgeLabellings`, `boundedLabellingsOn`, or a
  definition built from them until a symbolic cardinality bound has first
  proved the concrete instance safely small.  Evaluating `.length` still
  constructs the list and is not a safe size probe.  Inspect only the short
  coordinate/id list first, compute the resulting product bound externally,
  and prefer symbolic support/Fubini proofs whenever that bound is large.
- If verification is intentionally not run for safety, say so precisely. Never
  describe a historical green build recorded in the work plan as a build
  re-verified in the current session.

The Lean constructivity and frontier-honesty contract in `lean/AGENTS.md` also
applies to every change under `lean/`.

"""Codynamic transfer template — Milestone 4.1 of `work_plan.md`.

Concrete code-level realization of the type-signature correspondence
written up in [`notes/codynamic-transfer.md`](../../notes/codynamic-transfer.md):
the shared "local trusted estimate + overlap compatibility + summable
innovation budget ⇒ global stable bound" proof shape that appears in
both EKF-style sensor fusion and Yang–Mills RG-glued bound certificates.

This package contains:

  * `protocol.py` — the `InductiveBoundWitness` Protocol capturing the
    shared interface.
  * `runner.py` — a generic `run_inductive_steps` that consumes any
    instance and reports the final budget margin / closure outcome.
  * `ekf_example.py` — a vendored 1-D toy EKF instance.  Closes the
    work_plan 4.1 open question "depend on `codynamic-sensor-data` or
    vendor?" by vendoring a minimal example: no external dependency.
  * `ym_example.py` — a YM instance wrapping the SU(2) σ̂ pilot from
    `computations/sigma_hat_trajectory.py`.

Both instances satisfy the same Protocol; both feed the same
generic runner; the test in `tests/test_transfer_examples.py`
verifies the structural isomorphism.
"""

from computations.transfer_examples.protocol import (
    BoundWitness,
    InductiveBoundWitness,
    RunResult,
)
from computations.transfer_examples.runner import run_inductive_steps

__all__ = [
    "BoundWitness",
    "InductiveBoundWitness",
    "RunResult",
    "run_inductive_steps",
]

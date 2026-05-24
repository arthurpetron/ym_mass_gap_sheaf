"""The shared `InductiveBoundWitness` Protocol.

Captures the proof-shape line of `docs/context.md` §6:

    "local trusted estimate + overlap compatibility + summable
     innovation budget ⇒ global stable bound."

The Protocol is structurally typed (no `isinstance`-required inheritance),
which directly mirrors the typed-template claim of the codynamic-transfer
note: EKF-side and YM-side classes are unrelated by inheritance but share
this interface, and that sharing is the load-bearing structural fact.

# Field-level correspondence with `notes/codynamic-transfer.md` §2–§4

| Protocol member        | EKF semantic                  | YM semantic                  |
| ---                    | ---                           | ---                          |
| `bound_witness`        | covariance bound `P_n`        | string-tension margin `σ̂_k` |
| `remaining_budget`     | rewind margin `B_n`           | RG-degradation margin `B_k`  |
| `degradation`          | innovation `‖D_n‖`            | `η_k`                        |
| `step()`               | EKF predict + update          | block-spin pushforward       |
| `overlap_compatible()` | sensor-section overlap check  | KP buffer-glue check         |
| `scale_index`          | timestep / sample index `n`   | RG scale `k`                 |
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, runtime_checkable


@dataclass(frozen=True)
class BoundWitness:
    """A local bound-witness: scalar bound + descriptive label.

    EKF: the witness scalar is a covariance bound (variance for the 1-D
    toy EKF).  YM: the witness scalar is the renormalized string-tension
    margin σ̂_k.

    The single scalar suffices for the type-signature template; the
    real EKF / YM types carry richer structure (covariance matrix,
    KP triple, polymer atlas, etc.) but the *interface* contract is
    just "a positive bound witness".
    """

    bound: float
    """The scalar bound.  Positive on success; non-positive flags
    that the local estimate has failed."""

    label: str
    """Human-readable description: e.g. ``'EKF P_5'`` or ``'YM σ̂_3'``."""


@runtime_checkable
class InductiveBoundWitness(Protocol):
    """The shared interface for one step of an inductive bound-witness
    system in the codynamic-transfer template.

    Conformance is **structural** — any class providing these members at
    the right types is an `InductiveBoundWitness`, no explicit
    subclassing required.  This is the type-level realization of
    `notes/codynamic-transfer.md`'s §4 line-by-line transfer table.

    The runtime check `isinstance(obj, InductiveBoundWitness)` succeeds
    for any object with the right shape, enabling the structural-typing
    test in `tests/test_transfer_examples.py`.
    """

    @property
    def scale_index(self) -> int:
        """The discrete step index: ``n`` for EKF, ``k`` for YM."""

    @property
    def bound_witness(self) -> BoundWitness:
        """The local bound witness at this scale."""

    @property
    def remaining_budget(self) -> float:
        """The remaining degradation budget.  Closure requires this to
        stay positive across all steps."""

    @property
    def degradation(self) -> float:
        """The per-step degradation produced *from* this state (the
        innovation in EKF, η_k in YM).  Aggregated by the runner into
        the summable-innovation total."""

    def step(self) -> "InductiveBoundWitness | None":
        """Produce the next state.

        Returns the next ``InductiveBoundWitness`` instance.  Returns
        ``None`` if the local update has failed (e.g. the budget is
        exhausted or a regime threshold has been crossed) — this is
        the constructive equivalent of "the inductive step does not
        close at this scale."
        """

    def overlap_compatible(self, other: "InductiveBoundWitness") -> bool:
        """Check overlap compatibility with another state.

        EKF: are the local sensor estimates agreeing on the overlap
        within covariance tolerance?  YM: does the buffer-glue KP
        certificate combine cleanly?

        Returns True iff the overlap-compatibility certificate exists
        constructively.
        """


@dataclass(frozen=True)
class RunResult:
    """The outcome of `run_inductive_steps` over a finite step range."""

    final_state: InductiveBoundWitness | None
    """The state at the last step, or ``None`` if a step failed."""

    n_steps_taken: int
    """How many successful steps were taken (≤ requested ``K``)."""

    total_degradation: float
    """Σ_k d_k accumulated across the run."""

    initial_budget: float
    """The starting ``remaining_budget`` for reference."""

    final_budget: float
    """Last successful ``remaining_budget`` (= initial - total_degradation
    if every step closed)."""

    closes: bool
    """True iff every step succeeded AND ``total_degradation <
    initial_budget`` (the summability/closure condition)."""

    per_step_bounds: list[float]
    """The ``bound_witness.bound`` value at each scale, for plotting /
    audit."""

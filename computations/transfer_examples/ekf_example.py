"""Vendored 1-D toy EKF — the EKF side of the codynamic transfer template.

A minimal extended-Kalman-filter step satisfying the
`InductiveBoundWitness` Protocol.  Closes the work_plan 4.1 open
question "depend on `codynamic-sensor-data` or vendor?" by vendoring a
sufficient example here: no external dependency.

# The model

  * **State**: scalar ``x_n``, evolving as
    ``x_{n+1} = a · x_n + w_n``  with process noise ``w_n ~ 𝒩(0, q)``.
  * **Observation**: scalar ``z_n = h · x_n + v_n``  with measurement
    noise ``v_n ~ 𝒩(0, r)``.
  * **Covariance**: ``P_n`` tracks the estimator's uncertainty.

# The inductive bound

The EKF Riccati equation gives the steady-state covariance bound; for
a stable scalar EKF (``|a| < 1``), the closed-loop ``P_n`` converges to
a fixed point ``P_∞``.  We track the *budget* of permitted innovation
across the run: starting with ``B_0`` and consuming ``|D_n| = |z_n - h·x̂_n|``
at each step.

# Why this matches the codynamic-transfer §4 table

  * **local sensor section** → the per-step estimate ``(x̂_n, P_n)``.
  * **overlap agreement**     → checking that two estimators' bounds on
                                an overlap window stay within tolerance
                                (here: simple variance-difference check).
  * **rewind budget**         → the ``B_n`` field, decremented by
                                ``|innovation|`` each step.
  * **summable degradation**  → closure requires
                                ``Σ_n |innovation_n| < B_0``.

The toy specifics (1-D, deterministic test sequence) are simpler than a
real EKF, but the Protocol-level signature is exactly the same.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, replace

from computations.transfer_examples.protocol import (
    BoundWitness,
    InductiveBoundWitness,
)


@dataclass(frozen=True)
class EKFStep:
    """One step of a 1-D EKF satisfying `InductiveBoundWitness`."""

    n: int
    """Timestep index."""
    x_hat: float
    """Current state estimate."""
    P: float
    """Current covariance (variance for 1-D)."""
    a: float
    """State transition coefficient."""
    h: float
    """Observation coefficient."""
    q: float
    """Process noise variance."""
    r: float
    """Measurement noise variance."""
    B: float
    """Remaining innovation budget."""
    last_innovation: float
    """The most recent ``|z_n - h·x̂_n|``, exposed as `degradation`."""
    measurements: tuple[float, ...]
    """Hard-coded measurement sequence; we read index ``n`` at `step()`.

    Use a stable, finite test sequence to keep tests deterministic.
    """

    # --- InductiveBoundWitness Protocol ---

    @property
    def scale_index(self) -> int:
        return self.n

    @property
    def bound_witness(self) -> BoundWitness:
        # The "bound witness" is the covariance scalar — strictly
        # positive in a stable EKF.
        return BoundWitness(bound=self.P, label=f"EKF P_{self.n}")

    @property
    def remaining_budget(self) -> float:
        return self.B

    @property
    def degradation(self) -> float:
        return self.last_innovation

    def step(self) -> "EKFStep | None":
        """One EKF predict-update step.

        Returns ``None`` if either the budget is exhausted or there is
        no measurement at index ``n+1`` — the structural equivalent of
        "the inductive step has no admissible witness at this scale."
        """
        if self.B <= 0.0:
            return None
        next_n = self.n + 1
        if next_n >= len(self.measurements):
            return None

        # Predict.
        x_pred = self.a * self.x_hat
        P_pred = self.a * self.a * self.P + self.q

        # Update with measurement z_{n+1}.
        z = self.measurements[next_n]
        innovation = z - self.h * x_pred
        S = self.h * self.h * P_pred + self.r  # innovation variance
        K_gain = (P_pred * self.h) / S
        x_new = x_pred + K_gain * innovation
        P_new = (1.0 - K_gain * self.h) * P_pred

        # Consume budget by |innovation|.
        abs_innov = abs(innovation)
        B_new = self.B - abs_innov
        if B_new <= 0.0:
            return None  # budget exhausted; honest failure

        return replace(
            self,
            n=next_n,
            x_hat=x_new,
            P=P_new,
            B=B_new,
            last_innovation=abs_innov,
        )

    def overlap_compatible(self, other: "InductiveBoundWitness") -> bool:
        """Two EKF estimates are overlap-compatible if their bound witnesses
        agree within a tolerance (``|P_self - P_other| ≤ sqrt(P_self + P_other)``).

        This is a toy version of the EKF overlap agreement: in a real
        sensor-fusion deployment, this would involve a full covariance
        ellipsoid intersection check.
        """
        if not isinstance(other, EKFStep):
            # Cross-type overlap (e.g. EKF vs YM) is structurally
            # decidable but semantically meaningless; refuse.
            return False
        tolerance = math.sqrt(self.P + other.P)
        return abs(self.P - other.P) <= tolerance


# --------------------------------------------------------------------------
# Convenience: build a small test pilot
# --------------------------------------------------------------------------


def toy_ekf_pilot(
    n_measurements: int = 5,
    a: float = 0.9,
    h: float = 1.0,
    q: float = 0.01,
    r: float = 0.1,
    initial_P: float = 1.0,
    initial_budget: float = 5.0,
    measurement_offset: float = 0.5,
) -> EKFStep:
    """A small EKF instance for the transfer-template smoke test.

    Constructs a deterministic measurement sequence that produces small,
    bounded innovations — enough for the budget closure to hold across
    `n_measurements` steps but not so small that the test is vacuous.
    """
    if n_measurements < 1:
        raise ValueError(f"n_measurements must be ≥ 1; got {n_measurements}")
    # Hard-coded measurement sequence: x_true follows the stable dynamics
    # from a small starting offset, plus a tiny constant bias.
    measurements = tuple(
        measurement_offset * (a**i) + 0.01 for i in range(n_measurements)
    )
    return EKFStep(
        n=0,
        x_hat=0.0,
        P=initial_P,
        a=a,
        h=h,
        q=q,
        r=r,
        B=initial_budget,
        last_innovation=0.0,
        measurements=measurements,
    )


if __name__ == "__main__":
    from computations.transfer_examples.runner import run_inductive_steps

    initial = toy_ekf_pilot(n_measurements=5)
    print("Toy 1-D EKF — `InductiveBoundWitness` Protocol instance")
    print("=" * 65)
    print(f"  initial state : n=0, P={initial.P}, B={initial.B}")
    result = run_inductive_steps(initial, K=4)
    print(f"  steps taken   : {result.n_steps_taken}")
    print(f"  total |innov| : {result.total_degradation:.4e}")
    print(f"  final budget  : {result.final_budget:.4e}")
    print(f"  closes?       : {result.closes}")
    print(f"  per-step P    : {[f'{b:.4e}' for b in result.per_step_bounds]}")

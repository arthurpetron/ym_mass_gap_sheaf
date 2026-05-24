"""YM-side instance of the codynamic transfer template.

Wraps the SU(2) σ̂ pilot in `computations/sigma_hat_trajectory.py` to
satisfy the `InductiveBoundWitness` Protocol.

The point of this wrapper is structural: showing that the SU(2)
RG-step state — which carries σ̂_k, the per-step η_k, and the
remaining σ̂_0 - Σ η budget — fits *exactly* the same Protocol that
the toy EKF does.  This is the §4 line-by-line transfer made concrete:

  EKF                   YM
  ---                   ---
  P_n   (covariance)    σ̂_k  (renormalized string tension)
  B_n   (rewind budget) σ̂_0 - Σ_{i<k} η_i (remaining margin)
  D_n   (innovation)    η_k  (per-step σ̂ degradation)
  n     (timestep)      k    (RG scale)

The wrapper does not reproduce the σ̂ trajectory computation — that
lives in `sigma_hat_trajectory.py` and feeds in via the precomputed
trajectory passed at construction.  This separation keeps the
transfer-template code small and Protocol-focused.
"""

from __future__ import annotations

from dataclasses import dataclass

from computations.heat_kernel import HeatKernelConvention
from computations.overlap_measure import standard_su2_trajectory
from computations.sigma_hat_trajectory import (
    SigmaHatTrajectory,
    sigma_hat_trajectory,
)
from computations.transfer_examples.protocol import (
    BoundWitness,
    InductiveBoundWitness,
)


@dataclass(frozen=True)
class YMStep:
    """One step of the SU(2) σ̂ pilot satisfying `InductiveBoundWitness`.

    Holds the precomputed `SigmaHatTrajectory` plus the current scale
    index.  ``step()`` advances to the next scale; ``remaining_budget``
    tracks ``σ̂_0 - Σ_{i<k} η_i`` (decreasing in `k`).
    """

    k: int
    """Current RG scale index."""
    trajectory: SigmaHatTrajectory
    """The precomputed σ̂ trajectory.  Index ``k`` references
    ``trajectory.steps[k]``."""

    # --- InductiveBoundWitness Protocol ---

    @property
    def scale_index(self) -> int:
        return self.k

    @property
    def bound_witness(self) -> BoundWitness:
        # The "bound witness" is σ̂_k — the renormalized string-tension margin.
        sigma_hat_k = self.trajectory.steps[self.k].sigma_hat
        return BoundWitness(bound=sigma_hat_k, label=f"YM σ̂_{self.k}")

    @property
    def remaining_budget(self) -> float:
        # σ̂_0 - Σ_{i < k} η_i.  By construction this equals
        # trajectory.steps[k].sigma_hat (which IS the running margin).
        return self.trajectory.steps[self.k].sigma_hat

    @property
    def degradation(self) -> float:
        # η_k — the per-step transition from scale k to k+1.
        # Last step has η_k = 0 by sigma_hat_trajectory convention.
        return self.trajectory.steps[self.k].eta_k

    def step(self) -> "YMStep | None":
        """Advance to scale ``k + 1``.

        Returns ``None`` if we're already at the trajectory's last
        scale (no next step), or if the next step's σ̂ has hit zero
        (budget exhausted).
        """
        next_k = self.k + 1
        if next_k >= len(self.trajectory.steps):
            return None
        if self.trajectory.steps[next_k].sigma_hat <= 0.0:
            return None
        return YMStep(k=next_k, trajectory=self.trajectory)

    def overlap_compatible(self, other: "InductiveBoundWitness") -> bool:
        """Two YM RG steps are overlap-compatible if their σ̂ values
        agree within the local η budget.

        Concretely: ``|σ̂_self - σ̂_other| ≤ max(η_self, η_other)``.
        This is a toy version of the buffer-glue KP-compatibility
        check; the actual P3.3 overlap KP certificate is richer
        (carries ρ_∩, K_∩ pair), but the Protocol-level signature
        captures the existence of a compatibility witness.
        """
        if not isinstance(other, YMStep):
            return False
        sigma_self = self.bound_witness.bound
        sigma_other = other.bound_witness.bound
        tolerance = max(self.degradation, other.degradation, 1e-12)
        return abs(sigma_self - sigma_other) <= tolerance


# --------------------------------------------------------------------------
# Convenience: build a small YM pilot wrapping the existing σ̂ machinery
# --------------------------------------------------------------------------


def toy_ym_pilot(
    g_0: float = 0.10,
    K: int = 4,
    sigma_hat_initial: float = 10.0,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> YMStep:
    """A small YM instance for the transfer-template smoke test.

    Uses the existing `sigma_hat_trajectory` machinery to compute a
    weak-coupling SU(2) trajectory, then exposes it as the YM-side
    `InductiveBoundWitness`.  Default `g_0 = 0.10` sits comfortably
    inside the small-field convergence regime (g_max_sf ≈ 0.40),
    yielding η_k ≈ 0 and σ̂ surviving across all K steps.
    """
    g_trajectory = standard_su2_trajectory(k_max=K, g_0=g_0)[0]
    traj = sigma_hat_trajectory(
        g_trajectory,
        sigma_hat_initial=sigma_hat_initial,
        t_choice=convention,
    )
    return YMStep(k=0, trajectory=traj)


if __name__ == "__main__":
    from computations.transfer_examples.runner import run_inductive_steps

    initial = toy_ym_pilot(g_0=0.10, K=4, sigma_hat_initial=10.0)
    print("Toy SU(2) YM σ̂ pilot — `InductiveBoundWitness` Protocol instance")
    print("=" * 65)
    print(f"  initial state : k=0, σ̂={initial.bound_witness.bound}, "
          f"B={initial.remaining_budget}")
    result = run_inductive_steps(initial, K=4)
    print(f"  steps taken   : {result.n_steps_taken}")
    print(f"  total Σ η_k   : {result.total_degradation:.4e}")
    print(f"  final σ̂      : "
          f"{result.final_state.bound_witness.bound if result.final_state else 'None'}")
    print(f"  closes?       : {result.closes}")
    print(f"  per-step σ̂   : "
          f"{[f'{b:.4e}' for b in result.per_step_bounds]}")

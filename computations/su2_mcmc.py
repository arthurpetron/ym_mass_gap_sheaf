"""SU(2) lattice-gauge Monte Carlo — small-lattice cross-check.

Manuscript MCMC cross-check (2026-05-27): a small Metropolis SU(2)
lattice-gauge simulation on a 4D cubic lattice (4⁴ or 6⁴), measuring
the average plaquette `⟨P⟩` at a grid of bare couplings β = 4/g², and
comparing to (a) the strong-coupling expansion `⟨P⟩ ≈ β/4` valid at
small β, and (b) the weak-coupling expansion `⟨P⟩ ≈ 1 − 3/(4β)` valid
at large β.  The MCMC validates the deterministic σ̂-pilot framework
by demonstrating that lattice MCMC on the same Wilson action behaves
as expected across the strong-to-weak coupling crossover.

# Why a cross-check

The deterministic σ̂-pilot of `sigma_hat_trajectory.py` operates at
small g (weak coupling) where direct lattice MCMC has very long
autocorrelation times (the deep-weak-coupling regime is where the
project's analytical work shines and direct MCMC is hardest).  The
cross-check below targets the strong-to-intermediate coupling
crossover (β ∈ [2.0, 3.2]) where MCMC is fast and the literature
benchmarks are well-known.  Demonstrating quantitative agreement
with the standard SU(2) literature (e.g. [Creutz 1980]) in this
regime is the physics-community-style evidence that anchors the
project's analytical framework.

# Algorithm

Standard Metropolis on the Wilson action

    S = β Σ_p [1 − (1/2) Re tr(U_p)],

with link-by-link updates: at each link `(t, x, y, z, μ)`, propose
`U' = R · U` where `R` is a small random SU(2) close to identity,
compute the action change `ΔS` from the 6 plaquettes containing the
link via the standard staple-sum formula, and accept with
probability `min(1, exp(−ΔS))`.

# Scope

  * **Lattice size**: 4⁴ by default (256 sites, 1024 links).  Larger
    sizes (6⁴, 8⁴) are supported via the `L` parameter; default keeps
    each cross-check run within a few minutes.
  * **Sweeps**: configurable thermalization + measurement (default
    50 thermal + 50 measurement, single update per link per sweep).
  * **Measurement**: average plaquette `⟨P⟩ = ⟨(1/2) Re tr U_p⟩` only.
    Wilson loops (for direct σ extraction) are NOT implemented in
    this MVP; they require larger lattices and longer runs.

# References

  * [Creutz 1980] M. Creutz, "Monte Carlo study of quantized SU(2)
    gauge theory", Phys. Rev. D 21 (1980), 2308–2315.  Original SU(2)
    Wilson-action MCMC.  Reference values for ⟨P⟩ at small β.
  * [Wilson 1974] K. Wilson, "Confinement of quarks", Phys. Rev. D 10
    (1974), 2445–2459.  The Wilson action.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from numpy.typing import NDArray

# --------------------------------------------------------------------------
# SU(2) helpers
# --------------------------------------------------------------------------

# Pauli matrices (the σ_a, a = 1, 2, 3; the SU(2) generators are σ_a / 2).
SIGMA_1: NDArray[np.complex128] = np.array([[0, 1], [1, 0]], dtype=np.complex128)
SIGMA_2: NDArray[np.complex128] = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
SIGMA_3: NDArray[np.complex128] = np.array([[1, 0], [0, -1]], dtype=np.complex128)
IDENTITY_2: NDArray[np.complex128] = np.eye(2, dtype=np.complex128)


def random_su2_uniform(rng: np.random.Generator, count: int = 1) -> NDArray[np.complex128]:
    """Sample `count` SU(2) matrices uniformly from the Haar measure.

    Parametrization: `U = a₀ I + i (a₁ σ₁ + a₂ σ₂ + a₃ σ₃)` with
    `a₀² + a₁² + a₂² + a₃² = 1`.  Uniform on `S³ ⊂ ℝ⁴` ⟺ Haar on SU(2).

    Returns shape `(count, 2, 2)` if `count > 1`, else `(2, 2)`.
    """
    a = rng.normal(size=(count, 4))
    a /= np.linalg.norm(a, axis=1, keepdims=True)
    U = np.zeros((count, 2, 2), dtype=np.complex128)
    U[:, 0, 0] = a[:, 0] + 1j * a[:, 3]
    U[:, 0, 1] = a[:, 2] + 1j * a[:, 1]
    U[:, 1, 0] = -a[:, 2] + 1j * a[:, 1]
    U[:, 1, 1] = a[:, 0] - 1j * a[:, 3]
    return U if count > 1 else U[0]


def small_su2_perturbation(
    rng: np.random.Generator, epsilon: float = 0.3
) -> NDArray[np.complex128]:
    """Small random SU(2) close to identity (Metropolis proposal kernel).

    Returns `U = cos(θ/2) I + i sin(θ/2) (n · σ)` where `θ = ‖r‖` for
    `r ~ N(0, ε² I)` in ℝ³ and `n = r / ‖r‖` is the rotation axis.  For
    `ε = 0.3` the proposed `U` is close to identity (mean angle ~0.5 rad).
    """
    r = rng.normal(size=3, scale=epsilon)
    r_norm = float(np.linalg.norm(r))
    if r_norm < 1e-15:
        return IDENTITY_2.copy()
    n = r / r_norm
    half_theta = r_norm / 2.0
    cos_h = math.cos(half_theta)
    sin_h = math.sin(half_theta)
    return cos_h * IDENTITY_2 + 1j * sin_h * (
        n[0] * SIGMA_1 + n[1] * SIGMA_2 + n[2] * SIGMA_3
    )


def is_unitary(U: NDArray[np.complex128], tol: float = 1e-10) -> bool:
    """Check `U · U† = I` to tolerance `tol`."""
    return bool(np.allclose(U @ U.conj().T, IDENTITY_2, atol=tol))


def is_special(U: NDArray[np.complex128], tol: float = 1e-10) -> bool:
    """Check `det U = 1` to tolerance `tol`."""
    return bool(abs(np.linalg.det(U) - 1.0) < tol)


def is_su2(U: NDArray[np.complex128], tol: float = 1e-10) -> bool:
    """Check `U ∈ SU(2)`: unitary AND determinant 1."""
    return is_unitary(U, tol) and is_special(U, tol)


# --------------------------------------------------------------------------
# Lattice configuration + initialization
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class LatticeConfig:
    """4D cubic-lattice configuration parameters.

    Fields:
      * `L` — lattice side length (4⁴ = 4^4 = 256 sites at L=4).
      * `beta` — Wilson coupling `β = 4/g²` for SU(2).
    """

    L: int
    beta: float

    def __post_init__(self) -> None:
        if self.L < 2:
            raise ValueError(f"L must be ≥ 2; got {self.L}")
        if self.beta <= 0:
            raise ValueError(f"beta must be positive; got {self.beta}")

    @property
    def n_sites(self) -> int:
        return self.L ** 4

    @property
    def n_links(self) -> int:
        return self.n_sites * 4

    @property
    def g_squared(self) -> float:
        """Bare coupling squared, `g² = 4/β`."""
        return 4.0 / self.beta


def initialize_random(config: LatticeConfig, rng: np.random.Generator) -> NDArray[np.complex128]:
    """Initialize an L⁴ lattice with Haar-random SU(2) link variables.

    Shape: `(L, L, L, L, 4, 2, 2)`.  Index convention:
    `U[t, x, y, z, μ, :, :]` is the SU(2) matrix on the link starting
    at site `(t, x, y, z)` pointing in direction `μ ∈ {0, 1, 2, 3}`.
    """
    L = config.L
    U_flat = random_su2_uniform(rng, count=config.n_links)
    return U_flat.reshape(L, L, L, L, 4, 2, 2)


# --------------------------------------------------------------------------
# Staple sum + plaquette measurement
# --------------------------------------------------------------------------


def staple_at_link(
    U: NDArray[np.complex128], t: int, x: int, y: int, z: int, mu: int, L: int
) -> NDArray[np.complex128]:
    """Compute the staple sum `Σ_p (U-bar of the rest of plaquette p)`
    at link `(t, x, y, z, mu)`.

    The Wilson action contribution of the link `U_link` is
    `S_link = -β/2 · Re tr(U_link · staple_sum)`, so the change in
    action under `U_link → U_link'` is
    `ΔS = -β/2 · Re tr((U_link' - U_link) · staple_sum)`.

    The 6 plaquettes containing link `(x, μ)`: for each `ν ≠ μ`, one
    forward plaquette and one backward plaquette.  Standard formulas
    (e.g., [Creutz 1980] eq. 2.5 or any lattice-QCD textbook).
    """
    stp = np.zeros((2, 2), dtype=np.complex128)
    site = (t, x, y, z)
    e_mu = [0, 0, 0, 0]
    e_mu[mu] = 1
    for nu in range(4):
        if nu == mu:
            continue
        e_nu = [0, 0, 0, 0]
        e_nu[nu] = 1
        # Forward staple: U(x+μ, ν) · U(x+ν, μ)† · U(x, ν)†.
        x_p_mu = tuple((site[i] + e_mu[i]) % L for i in range(4))
        x_p_nu = tuple((site[i] + e_nu[i]) % L for i in range(4))
        forward = (
            U[x_p_mu[0], x_p_mu[1], x_p_mu[2], x_p_mu[3], nu]
            @ U[x_p_nu[0], x_p_nu[1], x_p_nu[2], x_p_nu[3], mu].conj().T
            @ U[site[0], site[1], site[2], site[3], nu].conj().T
        )
        stp = stp + forward
        # Backward staple: U(x+μ-ν, ν)† · U(x-ν, μ)† · U(x-ν, ν).
        x_m_nu = tuple((site[i] - e_nu[i]) % L for i in range(4))
        x_p_mu_m_nu = tuple((site[i] + e_mu[i] - e_nu[i]) % L for i in range(4))
        backward = (
            U[x_p_mu_m_nu[0], x_p_mu_m_nu[1], x_p_mu_m_nu[2], x_p_mu_m_nu[3], nu].conj().T
            @ U[x_m_nu[0], x_m_nu[1], x_m_nu[2], x_m_nu[3], mu].conj().T
            @ U[x_m_nu[0], x_m_nu[1], x_m_nu[2], x_m_nu[3], nu]
        )
        stp = stp + backward
    return stp


def plaquette_at(
    U: NDArray[np.complex128],
    t: int, x: int, y: int, z: int, mu: int, nu: int, L: int,
) -> NDArray[np.complex128]:
    """Compute the plaquette `U_p = U_μ(x) U_ν(x+μ) U_μ(x+ν)† U_ν(x)†`."""
    site = (t, x, y, z)
    e_mu = [0, 0, 0, 0]; e_mu[mu] = 1
    e_nu = [0, 0, 0, 0]; e_nu[nu] = 1
    x_p_mu = tuple((site[i] + e_mu[i]) % L for i in range(4))
    x_p_nu = tuple((site[i] + e_nu[i]) % L for i in range(4))
    return (
        U[site[0], site[1], site[2], site[3], mu]
        @ U[x_p_mu[0], x_p_mu[1], x_p_mu[2], x_p_mu[3], nu]
        @ U[x_p_nu[0], x_p_nu[1], x_p_nu[2], x_p_nu[3], mu].conj().T
        @ U[site[0], site[1], site[2], site[3], nu].conj().T
    )


def average_plaquette(U: NDArray[np.complex128], L: int) -> float:
    """Compute `⟨P⟩ = (1/N_p) Σ_p (1/2) Re tr U_p` over the entire lattice.

    `N_p = L⁴ · 6` (six independent plaquette planes per site).  Returns
    a real number in `[-1, 1]`; for the Wilson action `S = β Σ (1 - P_p)`,
    minimizing `S` is equivalent to maximizing `⟨P⟩`.
    """
    total = 0.0
    count = 0
    for t in range(L):
        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for mu in range(4):
                        for nu in range(mu + 1, 4):
                            U_p = plaquette_at(U, t, x, y, z, mu, nu, L)
                            total += 0.5 * float(np.real(np.trace(U_p)))
                            count += 1
    return total / count


# --------------------------------------------------------------------------
# Metropolis update
# --------------------------------------------------------------------------


def metropolis_update_link(
    U: NDArray[np.complex128], t: int, x: int, y: int, z: int, mu: int,
    beta: float, L: int, rng: np.random.Generator,
    epsilon: float = 0.3,
) -> bool:
    """Update a single link via Metropolis-Hastings on the Wilson action.

    Returns True if the proposal was accepted.
    """
    U_old = U[t, x, y, z, mu].copy()
    R = small_su2_perturbation(rng, epsilon=epsilon)
    U_new = R @ U_old
    stp = staple_at_link(U, t, x, y, z, mu, L)
    # ΔS = -β/2 · Re tr((U_new - U_old) · staple).
    delta_S = -(beta / 2.0) * float(np.real(np.trace((U_new - U_old) @ stp)))
    if delta_S <= 0.0 or rng.random() < math.exp(-delta_S):
        U[t, x, y, z, mu] = U_new
        return True
    return False


def sweep(
    U: NDArray[np.complex128], beta: float, L: int, rng: np.random.Generator,
    epsilon: float = 0.3,
) -> float:
    """One Metropolis sweep over the entire lattice (every link updated once).

    Returns the acceptance rate.
    """
    accept = 0
    total = 0
    for t in range(L):
        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for mu in range(4):
                        if metropolis_update_link(U, t, x, y, z, mu, beta, L, rng, epsilon):
                            accept += 1
                        total += 1
    return accept / total


# --------------------------------------------------------------------------
# Driver: run MCMC and measure ⟨P⟩
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class MCMCResult:
    """One MCMC run's outcome: per-β plaquette average + statistical error."""

    beta: float
    L: int
    n_thermalization: int
    n_measurement: int
    measurement_interval: int
    plaquette_mean: float
    plaquette_stderr: float
    acceptance_rate: float


def run_mcmc(
    config: LatticeConfig,
    n_thermalization: int = 50,
    n_measurement: int = 50,
    measurement_interval: int = 5,
    epsilon: float = 0.3,
    seed: int = 42,
) -> MCMCResult:
    """Run a small SU(2) lattice MCMC and measure the average plaquette.

    Parameters:
      * `config` — lattice size + β.
      * `n_thermalization` — sweeps to discard at the start.
      * `n_measurement` — sweeps after thermalization.
      * `measurement_interval` — measure ⟨P⟩ every k sweeps (auto-decorr.).
      * `epsilon` — proposal kernel width for Metropolis updates.
      * `seed` — RNG seed.

    Returns: an `MCMCResult` with the mean ⟨P⟩, bootstrap-style standard
    error (over independent samples), and the overall acceptance rate.
    """
    rng = np.random.default_rng(seed)
    U = initialize_random(config, rng)
    L = config.L
    beta = config.beta

    # Thermalization.
    accept_thermal = 0.0
    for _ in range(n_thermalization):
        accept_thermal += sweep(U, beta, L, rng, epsilon=epsilon)
    accept_thermal /= max(1, n_thermalization)

    # Measurement.
    plaquette_samples: list[float] = []
    accept_meas = 0.0
    sweeps_since_meas = 0
    for _ in range(n_measurement):
        accept_meas += sweep(U, beta, L, rng, epsilon=epsilon)
        sweeps_since_meas += 1
        if sweeps_since_meas >= measurement_interval:
            plaquette_samples.append(average_plaquette(U, L))
            sweeps_since_meas = 0

    if not plaquette_samples:
        # If interval > n_measurement, take a final measurement.
        plaquette_samples.append(average_plaquette(U, L))

    accept_meas /= max(1, n_measurement)
    overall_accept = (accept_thermal + accept_meas) / 2.0

    arr = np.array(plaquette_samples)
    p_mean = float(arr.mean())
    p_stderr = float(arr.std(ddof=1) / math.sqrt(len(arr))) if len(arr) > 1 else 0.0

    return MCMCResult(
        beta=beta,
        L=L,
        n_thermalization=n_thermalization,
        n_measurement=n_measurement,
        measurement_interval=measurement_interval,
        plaquette_mean=p_mean,
        plaquette_stderr=p_stderr,
        acceptance_rate=overall_accept,
    )


# --------------------------------------------------------------------------
# Analytical reference curves
# --------------------------------------------------------------------------


def strong_coupling_plaquette(beta: float) -> float:
    """Strong-coupling expansion: `⟨P⟩ ≈ β/4 + O(β³)` for SU(2).

    Valid at small β; first-order term from the character expansion of
    the Wilson action.  Reference: [Wilson 1974], [Drouffe–Itzykson 1989].
    """
    return beta / 4.0


def weak_coupling_plaquette(beta: float) -> float:
    """Weak-coupling expansion: `⟨P⟩ ≈ 1 − 3/(4β) + O(1/β²)` for SU(2).

    Valid at large β; first-order term from the one-loop perturbative
    expansion around the trivial vacuum.  Reference: [Coste et al.
    1986], [Müller–Preussker 1987] for higher-order corrections.
    """
    return 1.0 - 3.0 / (4.0 * beta)

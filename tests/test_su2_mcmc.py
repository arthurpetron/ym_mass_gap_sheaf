"""Tests for `computations.su2_mcmc` (SU(2) lattice MCMC cross-check).

Coverage:
  * SU(2) primitives: random_su2_uniform, small_su2_perturbation
    produce matrices in SU(2) (unitary + det 1).
  * LatticeConfig validation.
  * initialize_random produces lattice of SU(2) matrices.
  * staple_at_link returns a 2×2 complex matrix.
  * plaquette_at returns a matrix in SU(2) (product of SU(2)s).
  * average_plaquette returns a value in [-1, 1].
  * metropolis_update_link preserves SU(2) at the updated link.
  * sweep returns an acceptance rate in [0, 1].
  * run_mcmc on a tiny lattice (L=4, few sweeps) completes and produces
    a sensible ⟨P⟩ value.
  * Strong/weak-coupling analytical curves return expected limits.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from computations.su2_mcmc import (
    IDENTITY_2,
    LatticeConfig,
    average_plaquette,
    initialize_random,
    is_special,
    is_su2,
    is_unitary,
    metropolis_update_link,
    plaquette_at,
    random_su2_uniform,
    run_mcmc,
    small_su2_perturbation,
    staple_at_link,
    strong_coupling_plaquette,
    sweep,
    weak_coupling_plaquette,
)


# --------------------------------------------------------------------------
# SU(2) primitives
# --------------------------------------------------------------------------


def test_random_su2_uniform_is_su2() -> None:
    rng = np.random.default_rng(0)
    for _ in range(50):
        U = random_su2_uniform(rng)
        assert is_su2(U), f"random_su2_uniform produced non-SU(2): {U}"


def test_random_su2_uniform_batch() -> None:
    rng = np.random.default_rng(0)
    Us = random_su2_uniform(rng, count=20)
    assert Us.shape == (20, 2, 2)
    for U in Us:
        assert is_su2(U)


def test_small_su2_perturbation_is_su2() -> None:
    rng = np.random.default_rng(1)
    for _ in range(50):
        R = small_su2_perturbation(rng, epsilon=0.3)
        assert is_su2(R), f"perturbation not SU(2): {R}"


def test_small_su2_perturbation_zero_epsilon_is_identity() -> None:
    """Zero ε should give a matrix very close to the identity."""
    rng = np.random.default_rng(2)
    R = small_su2_perturbation(rng, epsilon=0.0)
    assert np.allclose(R, IDENTITY_2, atol=1e-10)


def test_is_unitary_and_special_helpers() -> None:
    assert is_unitary(IDENTITY_2)
    assert is_special(IDENTITY_2)
    assert is_su2(IDENTITY_2)
    # A non-unitary matrix.
    M = np.array([[2.0, 0.0], [0.0, 1.0]], dtype=complex)
    assert not is_unitary(M)
    assert not is_su2(M)


# --------------------------------------------------------------------------
# LatticeConfig
# --------------------------------------------------------------------------


def test_lattice_config_basics() -> None:
    c = LatticeConfig(L=4, beta=2.4)
    assert c.L == 4
    assert c.beta == 2.4
    assert c.n_sites == 4 ** 4
    assert c.n_links == 4 ** 4 * 4
    # g² = 4/β: at β=2.4, g² = 5/3 ≈ 1.667.
    assert c.g_squared == pytest.approx(4.0 / 2.4)


def test_lattice_config_rejects_invalid() -> None:
    with pytest.raises(ValueError, match="L"):
        LatticeConfig(L=1, beta=2.0)
    with pytest.raises(ValueError, match="beta"):
        LatticeConfig(L=4, beta=0.0)


# --------------------------------------------------------------------------
# Lattice initialization + staple + plaquette
# --------------------------------------------------------------------------


def test_initialize_random_shape() -> None:
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    assert U.shape == (4, 4, 4, 4, 4, 2, 2)


def test_initialize_random_every_link_is_su2() -> None:
    """Sample a few links and verify each is in SU(2)."""
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    for t, x, y, z, mu in [
        (0, 0, 0, 0, 0), (1, 2, 3, 0, 1), (3, 3, 3, 3, 3), (2, 1, 0, 2, 2),
    ]:
        assert is_su2(U[t, x, y, z, mu])


def test_staple_at_link_shape() -> None:
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    stp = staple_at_link(U, 0, 0, 0, 0, 0, L=c.L)
    assert stp.shape == (2, 2)
    assert stp.dtype == np.complex128


def test_plaquette_at_is_su2() -> None:
    """A plaquette is a product of four SU(2) matrices; should be in SU(2)."""
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    for mu, nu in [(0, 1), (0, 2), (1, 3), (2, 3)]:
        U_p = plaquette_at(U, 1, 2, 0, 3, mu, nu, L=c.L)
        assert is_su2(U_p), f"plaquette({mu},{nu}) not SU(2)"


def test_average_plaquette_in_range() -> None:
    """⟨(1/2) Re tr U_p⟩ on a random configuration should be in [-1, 1]."""
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    p = average_plaquette(U, L=c.L)
    assert -1.0 <= p <= 1.0


def test_average_plaquette_random_near_zero() -> None:
    """For a Haar-random configuration, ⟨P⟩ is near 0 (no thermalization)."""
    rng = np.random.default_rng(123)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    p = average_plaquette(U, L=c.L)
    # On a 4⁴ lattice (1536 plaquettes), thermal-mean = 0 with std ~ 1/√1536 ≈ 0.026.
    assert abs(p) < 0.1, f"random ⟨P⟩ = {p} unexpectedly far from 0"


# --------------------------------------------------------------------------
# Metropolis update + sweep
# --------------------------------------------------------------------------


def test_metropolis_update_preserves_su2() -> None:
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    metropolis_update_link(U, 1, 2, 0, 3, 1, beta=c.beta, L=c.L, rng=rng)
    assert is_su2(U[1, 2, 0, 3, 1])


def test_sweep_returns_acceptance_in_unit_interval() -> None:
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    rate = sweep(U, beta=c.beta, L=c.L, rng=rng)
    assert 0.0 <= rate <= 1.0


def test_sweep_preserves_su2() -> None:
    """After a sweep, every link should still be in SU(2)."""
    rng = np.random.default_rng(0)
    c = LatticeConfig(L=4, beta=2.4)
    U = initialize_random(c, rng)
    sweep(U, beta=c.beta, L=c.L, rng=rng)
    # Spot-check a few links.
    for t, x, y, z, mu in [(0, 0, 0, 0, 0), (1, 2, 3, 0, 1), (3, 3, 3, 3, 3)]:
        assert is_su2(U[t, x, y, z, mu])


# --------------------------------------------------------------------------
# Driver run_mcmc — end-to-end smoke test
# --------------------------------------------------------------------------


def test_run_mcmc_tiny_smoke_test() -> None:
    """A tiny MCMC run completes and produces a sensible result."""
    c = LatticeConfig(L=4, beta=2.4)
    res = run_mcmc(
        c,
        n_thermalization=20,
        n_measurement=20,
        measurement_interval=5,
        seed=42,
    )
    assert res.beta == 2.4
    assert res.L == 4
    # At β=2.4 on a thermalized lattice, ⟨P⟩ should be in a reasonable range
    # (around 0.5–0.7 — strong-coupling prediction is 0.6).
    assert 0.3 < res.plaquette_mean < 0.9, (
        f"⟨P⟩ = {res.plaquette_mean} outside reasonable thermal range"
    )
    assert res.plaquette_stderr >= 0.0
    assert 0.0 <= res.acceptance_rate <= 1.0


def test_run_mcmc_strong_coupling_matches_prediction() -> None:
    """At small β (strong coupling), ⟨P⟩ ≈ β/4 to within a few percent
    on a thermalized configuration."""
    c = LatticeConfig(L=4, beta=2.0)
    res = run_mcmc(
        c,
        n_thermalization=50,
        n_measurement=50,
        measurement_interval=5,
        seed=42,
    )
    prediction = strong_coupling_plaquette(2.0)  # = 0.5
    # Allow ±10% for finite-lattice + finite-order corrections.
    relative_error = abs(res.plaquette_mean - prediction) / prediction
    assert relative_error < 0.10, (
        f"⟨P⟩ = {res.plaquette_mean} too far from strong-coupling "
        f"prediction {prediction} (rel err {relative_error:.1%})"
    )


# --------------------------------------------------------------------------
# Analytical curves
# --------------------------------------------------------------------------


def test_strong_coupling_at_unit_beta() -> None:
    assert strong_coupling_plaquette(1.0) == pytest.approx(0.25)
    assert strong_coupling_plaquette(2.4) == pytest.approx(0.60)


def test_weak_coupling_large_beta_limit() -> None:
    """As β → ∞, ⟨P⟩ → 1 in the weak-coupling expansion."""
    assert weak_coupling_plaquette(100.0) == pytest.approx(1.0 - 3.0 / 400.0)
    # At β = 1000, ⟨P⟩ very close to 1.
    assert weak_coupling_plaquette(1000.0) > 0.99


def test_weak_and_strong_cross_near_beta_2() -> None:
    """The strong (β/4) and weak (1 − 3/(4β)) curves cross around β ≈ 2.
    Solve β/4 = 1 - 3/(4β): β² = 4β - 3, β² - 4β + 3 = 0, β = 1 or 3.
    Within the physical β > 0 regime, they cross at β = 1 and β = 3.
    """
    # Verify the crossing at β = 1: β/4 = 0.25, 1 - 3/(4·1) = 0.25.
    assert strong_coupling_plaquette(1.0) == pytest.approx(weak_coupling_plaquette(1.0))
    # And at β = 3: β/4 = 0.75, 1 - 3/(4·3) = 0.75.
    assert strong_coupling_plaquette(3.0) == pytest.approx(weak_coupling_plaquette(3.0))

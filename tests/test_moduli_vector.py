"""Tests for `computations.moduli_vector` (manuscript Ch. 1.5).

Coverage:
  * `ModuliVector` construction validation (10 nonneg fields).
  * `epsilon_total` is the sum of the five ε components.
  * `registry_inequality` six-clause chain at pilot operating points.
  * `RegistryInequalityResult.passes` + `.failed_clauses` semantics.
  * Pilot instances `canonical_pilot_moduli` and `wilson_pilot_moduli`
    pass at tolerance 0.1 (matching the Lean `ModuliAlgebra` instances).
"""

from __future__ import annotations

import pytest

from computations.moduli_vector import (
    ModuliVector,
    RegistryInequalityResult,
    canonical_pilot_moduli,
    wilson_pilot_moduli,
)


# --------------------------------------------------------------------------
# Construction validation
# --------------------------------------------------------------------------


def _well_formed_moduli(
    eps: float = 0.01,
    sigma_phys: float = 0.5,
    m_inf: float = 0.5,
) -> ModuliVector:
    """Construct a generic well-formed `ModuliVector` for tests."""
    return ModuliVector(
        eps_UV=eps, eps_IR=eps, eps_RG=eps, eps_cap=eps, eps_num=eps,
        sigma_0=1.0, sigma_hat_k=sigma_phys, sigma_phys=sigma_phys,
        m_0=m_inf, m_inf=m_inf,
    )


def test_moduli_vector_rejects_negative_field() -> None:
    for field_name in (
        "eps_UV", "eps_IR", "eps_RG", "eps_cap", "eps_num",
        "sigma_0", "sigma_hat_k", "sigma_phys", "m_0", "m_inf",
    ):
        kwargs = dict(
            eps_UV=0.01, eps_IR=0.01, eps_RG=0.01, eps_cap=0.01, eps_num=0.01,
            sigma_0=1.0, sigma_hat_k=0.5, sigma_phys=0.5,
            m_0=0.5, m_inf=0.5,
        )
        kwargs[field_name] = -0.001
        with pytest.raises(ValueError, match=field_name):
            ModuliVector(**kwargs)


def test_moduli_vector_accepts_zero_fields() -> None:
    """All fields can be zero (boundary case; useful for placeholder
    constructions before any modulus is computed)."""
    m = ModuliVector(
        eps_UV=0.0, eps_IR=0.0, eps_RG=0.0, eps_cap=0.0, eps_num=0.0,
        sigma_0=0.0, sigma_hat_k=0.0, sigma_phys=0.0,
        m_0=0.0, m_inf=0.0,
    )
    # Construction succeeds; the registry inequality fails (no positivity).
    r = m.registry_inequality(tolerance=0.1)
    assert not r.passes
    assert "sigma_phys_positive" in r.failed_clauses


# --------------------------------------------------------------------------
# epsilon_total
# --------------------------------------------------------------------------


def test_epsilon_total_is_sum_of_five() -> None:
    m = _well_formed_moduli(eps=0.01)
    assert m.epsilon_total == pytest.approx(0.05)


def test_epsilon_total_with_nonuniform_components() -> None:
    m = ModuliVector(
        eps_UV=0.01, eps_IR=0.02, eps_RG=0.03, eps_cap=0.04, eps_num=0.05,
        sigma_0=1.0, sigma_hat_k=0.5, sigma_phys=0.5,
        m_0=0.5, m_inf=0.5,
    )
    assert m.epsilon_total == pytest.approx(0.15)


# --------------------------------------------------------------------------
# Registry inequality — each clause
# --------------------------------------------------------------------------


def test_registry_inequality_passes_at_well_formed() -> None:
    m = _well_formed_moduli(eps=0.01, sigma_phys=0.5, m_inf=0.5)
    r = m.registry_inequality(tolerance=0.1)
    assert r.passes
    assert r.failed_clauses == ()


def test_registry_inequality_fails_when_epsilon_total_exceeds_tolerance() -> None:
    m = _well_formed_moduli(eps=0.05)  # ε_total = 0.25 > 0.1.
    r = m.registry_inequality(tolerance=0.1)
    assert not r.passes
    assert "epsilon_total_le_tolerance" in r.failed_clauses


def test_registry_inequality_fails_when_sigma_phys_nonpositive() -> None:
    m = ModuliVector(
        eps_UV=0.01, eps_IR=0.01, eps_RG=0.01, eps_cap=0.01, eps_num=0.01,
        sigma_0=1.0, sigma_hat_k=0.5, sigma_phys=0.0,  # σ_phys = 0
        m_0=0.5, m_inf=0.5,
    )
    r = m.registry_inequality(tolerance=0.1)
    assert not r.passes
    assert "sigma_phys_positive" in r.failed_clauses


def test_registry_inequality_fails_when_sigma_hat_below_sigma_phys() -> None:
    m = ModuliVector(
        eps_UV=0.01, eps_IR=0.01, eps_RG=0.01, eps_cap=0.01, eps_num=0.01,
        sigma_0=1.0, sigma_hat_k=0.3, sigma_phys=0.5,  # σ̂_k < σ_phys
        m_0=0.5, m_inf=0.5,
    )
    r = m.registry_inequality(tolerance=0.1)
    assert not r.passes
    assert "sigma_hat_k_ge_sigma_phys" in r.failed_clauses


def test_registry_inequality_fails_when_m_inf_squared_exceeds_sigma_phys() -> None:
    """m_∞² ≤ σ_phys is the Wilson-loop → mass-from-clustering chain."""
    m = ModuliVector(
        eps_UV=0.01, eps_IR=0.01, eps_RG=0.01, eps_cap=0.01, eps_num=0.01,
        sigma_0=1.0, sigma_hat_k=0.5, sigma_phys=0.5,
        m_0=0.9, m_inf=0.9,  # m_∞² = 0.81 > 0.5 = σ_phys
    )
    r = m.registry_inequality(tolerance=0.1)
    assert not r.passes
    assert "m_inf_squared_le_sigma_phys" in r.failed_clauses


def test_registry_inequality_fails_when_m_inf_exceeds_m_0() -> None:
    m = ModuliVector(
        eps_UV=0.01, eps_IR=0.01, eps_RG=0.01, eps_cap=0.01, eps_num=0.01,
        sigma_0=1.0, sigma_hat_k=0.5, sigma_phys=0.5,
        m_0=0.3, m_inf=0.5,  # m_∞ > m_0
    )
    r = m.registry_inequality(tolerance=0.1)
    assert not r.passes
    assert "m_inf_le_m_0" in r.failed_clauses


def test_registry_inequality_rejects_nonpositive_tolerance() -> None:
    m = _well_formed_moduli()
    with pytest.raises(ValueError, match="tolerance"):
        m.registry_inequality(tolerance=0.0)
    with pytest.raises(ValueError, match="tolerance"):
        m.registry_inequality(tolerance=-0.1)


# --------------------------------------------------------------------------
# RegistryInequalityResult semantics
# --------------------------------------------------------------------------


def test_failed_clauses_is_tuple() -> None:
    r = RegistryInequalityResult(
        epsilon_total_le_tolerance=True,
        sigma_phys_positive=False,
        sigma_hat_k_ge_sigma_phys=True,
        m_inf_positive=False,
        m_inf_squared_le_sigma_phys=True,
        m_inf_le_m_0=True,
    )
    assert r.failed_clauses == ("sigma_phys_positive", "m_inf_positive")
    assert not r.passes


def test_passes_iff_no_failed_clauses() -> None:
    r_pass = RegistryInequalityResult(
        epsilon_total_le_tolerance=True,
        sigma_phys_positive=True,
        sigma_hat_k_ge_sigma_phys=True,
        m_inf_positive=True,
        m_inf_squared_le_sigma_phys=True,
        m_inf_le_m_0=True,
    )
    assert r_pass.passes
    assert r_pass.failed_clauses == ()


# --------------------------------------------------------------------------
# Pilot instances — lockstep with the Lean `ModuliAlgebra`
# --------------------------------------------------------------------------


def test_canonical_pilot_passes_registry_at_tolerance_0_1() -> None:
    """Matches `lean/YMGap/ModuliAlgebra.lean::canonical_pilot_registry_inequality`."""
    r = canonical_pilot_moduli.registry_inequality(tolerance=0.1)
    assert r.passes, f"failed clauses: {r.failed_clauses}"


def test_wilson_pilot_passes_registry_at_tolerance_0_1() -> None:
    """Matches `lean/YMGap/ModuliAlgebra.lean::wilson_pilot_registry_inequality`."""
    r = wilson_pilot_moduli.registry_inequality(tolerance=0.1)
    assert r.passes, f"failed clauses: {r.failed_clauses}"


def test_pilot_instances_have_post_c_lambda_upgrade_values() -> None:
    """Canonical σ̂_k = 9991/10000; Wilson σ̂_k = 9997/10000.  These reflect
    the post-2026-05-26 c_λ Casimir-gap derivation (see
    `notes/fiducials_notes.md` §1).
    """
    assert canonical_pilot_moduli.sigma_hat_k == pytest.approx(9991 / 10000)
    assert wilson_pilot_moduli.sigma_hat_k == pytest.approx(9997 / 10000)


def test_pilot_instances_have_canonical_mass_gap_bound() -> None:
    """Both pilots have m_0 = m_inf = 999/1000 (the post-c_λ-upgrade
    constructive mass-gap lower bound)."""
    assert canonical_pilot_moduli.m_0 == pytest.approx(999 / 1000)
    assert canonical_pilot_moduli.m_inf == pytest.approx(999 / 1000)
    assert wilson_pilot_moduli.m_0 == pytest.approx(999 / 1000)
    assert wilson_pilot_moduli.m_inf == pytest.approx(999 / 1000)

"""Tests for `computations.inductive_state` (Milestone 2.2).

Coverage:

- Construction of `KPData` and `InductiveState` with valid and invalid inputs.
- `validate()` returns a dict of pass/fail keyed by V1/V2/V3 clause names.
- `all_valid()` passes on well-formed states, fails on each individual
  violation (positivity, buffer-glue-ρ, buffer-glue-K).
- `step_signature()` returns a string describing the 2.3 pushforward type
  (the 2.2→2.3 handoff), referencing the four conditions S1–S4.
- No test constructs ℐ_{k+1} from ℐ_k.  The step is 2.3.
"""

from __future__ import annotations

import pytest

from computations.inductive_state import InductiveState, KPData

# --------------------------------------------------------------------------
# KPData construction
# --------------------------------------------------------------------------


def test_kpdata_construction_valid() -> None:
    c = KPData(rho=0.5, K=10.0)
    assert c.rho == 0.5
    assert c.K == 10.0
    assert c.satisfies is True


def test_kpdata_rejects_nonpositive_rho() -> None:
    with pytest.raises(ValueError, match="ρ"):
        KPData(rho=0.0, K=10.0)
    with pytest.raises(ValueError, match="ρ"):
        KPData(rho=-1.0, K=10.0)


def test_kpdata_rejects_negative_K() -> None:
    with pytest.raises(ValueError, match="K"):
        KPData(rho=0.5, K=-1.0)


def test_kpdata_K_zero_allowed() -> None:
    """K = 0 is allowed (degenerate but well-formed)."""
    c = KPData(rho=0.5, K=0.0)
    assert c.K == 0.0


def test_kpdata_unsatisfied_flag() -> None:
    """`satisfies=False` marks a KPData that does not certify its inequality.

    The flag is informational; we use it to test V2 failure paths.
    """
    c = KPData(rho=0.5, K=10.0, satisfies=False)
    assert c.satisfies is False


# --------------------------------------------------------------------------
# Well-formed InductiveState fixtures
# --------------------------------------------------------------------------


def _well_formed_state(k: int = 0) -> InductiveState:
    """A scale-k state satisfying every clause of `validate()`.

    Constants chosen so the buffer-glue relationship holds with margin:
    ρ_∩ = min(ρ_sf, ρ_lf) = 0.4, K_∩ = 7.0 ≤ 5.0 + 3.0 = 8.0.
    """
    sf = KPData(rho=0.6, K=5.0)
    lf = KPData(rho=0.4, K=3.0)
    cap = KPData(rho=0.4, K=7.0)
    return InductiveState(
        k=k,
        sigma_hat=0.25,
        g=1.0,
        kp_sf=sf,
        kp_lf=lf,
        kp_cap=cap,
        poly_atlas=None,
    )


def test_well_formed_state_all_valid() -> None:
    s = _well_formed_state()
    checks = s.validate()
    assert checks == {
        "V1_sigma_hat_positive": True,
        "V2_kp_sf_well_formed": True,
        "V2_kp_lf_well_formed": True,
        "V2_kp_cap_well_formed": True,
        "V3_buffer_glue_rho": True,
        "V3_buffer_glue_K": True,
    }
    assert s.all_valid() is True


# --------------------------------------------------------------------------
# validate() failure paths — one per clause
# --------------------------------------------------------------------------


def test_validate_V1_sigma_hat_nonpositive() -> None:
    base = _well_formed_state()
    s = InductiveState(
        k=base.k,
        sigma_hat=0.0,
        g=base.g,
        kp_sf=base.kp_sf,
        kp_lf=base.kp_lf,
        kp_cap=base.kp_cap,
        poly_atlas=base.poly_atlas,
    )
    checks = s.validate()
    assert checks["V1_sigma_hat_positive"] is False
    assert s.all_valid() is False


def test_validate_V2_unsatisfied_certificate() -> None:
    base = _well_formed_state()
    s = InductiveState(
        k=base.k,
        sigma_hat=base.sigma_hat,
        g=base.g,
        kp_sf=KPData(rho=base.kp_sf.rho, K=base.kp_sf.K, satisfies=False),
        kp_lf=base.kp_lf,
        kp_cap=base.kp_cap,
        poly_atlas=base.poly_atlas,
    )
    checks = s.validate()
    assert checks["V2_kp_sf_well_formed"] is False
    assert s.all_valid() is False


def test_validate_V3_buffer_glue_rho_mismatch() -> None:
    """Buffer ρ_∩ must equal min(ρ_sf, ρ_lf); a mismatch fails V3."""
    base = _well_formed_state()
    bad_cap = KPData(rho=0.5, K=base.kp_cap.K)  # min(sf.rho, lf.rho) = 0.4
    s = InductiveState(
        k=base.k,
        sigma_hat=base.sigma_hat,
        g=base.g,
        kp_sf=base.kp_sf,
        kp_lf=base.kp_lf,
        kp_cap=bad_cap,
        poly_atlas=base.poly_atlas,
    )
    checks = s.validate()
    assert checks["V3_buffer_glue_rho"] is False
    assert s.all_valid() is False


def test_validate_V3_buffer_glue_K_too_large() -> None:
    """Buffer K_∩ must be ≤ K_sf + K_lf."""
    base = _well_formed_state()
    bad_cap = KPData(rho=base.kp_cap.rho, K=base.kp_sf.K + base.kp_lf.K + 1.0)
    s = InductiveState(
        k=base.k,
        sigma_hat=base.sigma_hat,
        g=base.g,
        kp_sf=base.kp_sf,
        kp_lf=base.kp_lf,
        kp_cap=bad_cap,
        poly_atlas=base.poly_atlas,
    )
    checks = s.validate()
    assert checks["V3_buffer_glue_K"] is False
    assert s.all_valid() is False


def test_validate_V3_buffer_glue_K_at_boundary() -> None:
    """Equality K_∩ = K_sf + K_lf is on the admissible side of V3."""
    base = _well_formed_state()
    boundary_cap = KPData(rho=base.kp_cap.rho, K=base.kp_sf.K + base.kp_lf.K)
    s = InductiveState(
        k=base.k,
        sigma_hat=base.sigma_hat,
        g=base.g,
        kp_sf=base.kp_sf,
        kp_lf=base.kp_lf,
        kp_cap=boundary_cap,
        poly_atlas=base.poly_atlas,
    )
    assert s.validate()["V3_buffer_glue_K"] is True


# --------------------------------------------------------------------------
# step_signature — the 2.2→2.3 handoff
# --------------------------------------------------------------------------


def test_step_signature_returns_string() -> None:
    sig = InductiveState.step_signature()
    assert isinstance(sig, str)
    assert len(sig) > 0


def test_step_signature_mentions_four_conditions() -> None:
    """The signature should textually reference each of S1–S4."""
    sig = InductiveState.step_signature()
    for tag in ("S1", "S2", "S3", "S4"):
        assert tag in sig, f"step_signature missing {tag}"


def test_step_signature_mentions_2_3_handoff() -> None:
    """The signature names that 2.3 is the milestone producing the term."""
    sig = InductiveState.step_signature()
    assert "2.3" in sig


# --------------------------------------------------------------------------
# Polymer atlas — open question, deliberately abstract
# --------------------------------------------------------------------------


def test_poly_atlas_accepts_any_object() -> None:
    """`poly_atlas` is `Any` per the deferred-representation decision."""
    base = _well_formed_state()
    # Replace with a deliberately exotic placeholder.
    s = InductiveState(
        k=base.k,
        sigma_hat=base.sigma_hat,
        g=base.g,
        kp_sf=base.kp_sf,
        kp_lf=base.kp_lf,
        kp_cap=base.kp_cap,
        poly_atlas={"placeholder": "any object accepted"},
    )
    assert s.all_valid() is True

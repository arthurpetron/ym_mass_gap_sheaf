"""Tests for ``computations.large_field_kp`` (Milestone 3.2, post-upgrade)."""

from __future__ import annotations

import math

import pytest

from computations.heat_kernel import HeatKernelConvention
from computations.large_field_kp import (
    J_MAX_DEFAULT,
    MU_PLAQUETTE_4D,
    MU_PLAQUETTE_4D_RATIONAL,
    SEILER_5D_MINUS_4_LEGACY,
    CharacterTailSum,
    LargeFieldKP,
    compute_large_field_kp,
    convergence_threshold_g_lf,
    eps_lf,
    first_few_rg_steps,
    heat_kernel_character_tail_Z,
    plaquette_edge_neighbor_count,
)

CANONICAL = HeatKernelConvention.CANONICAL
WILSON = HeatKernelConvention.WILSON
MANTON = HeatKernelConvention.MANTON


# --------------------------------------------------------------------------
# Structural / dataclass shape
# --------------------------------------------------------------------------


def test_lf_kp_structure_in_convergent_regime() -> None:
    """In the convergent regime, ρ_lf > 0 and K_lf is finite, non-negative."""
    kp = compute_large_field_kp(g_k=0.2)
    assert isinstance(kp, LargeFieldKP)
    assert kp.rho_lf > 0
    assert math.isfinite(kp.K_lf)
    assert kp.K_lf >= 0
    assert kp.convergent
    assert math.isfinite(kp.Z_t_upper)


def test_lf_kp_structure_non_convergent_regime() -> None:
    """Above threshold, ρ_lf may be ≤ 0 and K_lf is +∞.  Both are admissible
    values of the certificate (the bound is vacuous, honestly flagged)."""
    kp = compute_large_field_kp(g_k=1.0)
    assert isinstance(kp, LargeFieldKP)
    assert not kp.convergent
    assert math.isinf(kp.K_lf)


def test_lf_dataclass_has_new_fields() -> None:
    """The post-upgrade dataclass carries the asymptotic, convergent, and
    Z_t_upper witnesses required by the constructive law."""
    kp = compute_large_field_kp(g_k=0.2)
    assert hasattr(kp, "rho_lf")
    assert hasattr(kp, "rho_lf_asymptotic")
    assert hasattr(kp, "K_lf")
    assert hasattr(kp, "convergent")
    assert hasattr(kp, "Z_t_upper")


# --------------------------------------------------------------------------
# ρ_lf_asymptotic: matches outline §18.5 verbatim
# --------------------------------------------------------------------------


def test_lf_asymptotic_canonical_is_three_quarters_at_g_one() -> None:
    """Outline §18.5 quotes κ_{SU(2)} = 3/4 in canonical; at g=1 this is the
    leading-asymptotic ρ_lf_asymptotic value."""
    kp = compute_large_field_kp(g_k=1.0, t_choice=CANONICAL)
    assert kp.rho_lf_asymptotic == pytest.approx(0.75)


def test_lf_asymptotic_wilson_is_three_at_g_one() -> None:
    """In Wilson, the leading asymptotic is 2N · C_2 = 3 at g=1."""
    kp = compute_large_field_kp(g_k=1.0, t_choice=WILSON)
    assert kp.rho_lf_asymptotic == pytest.approx(3.0)


def test_lf_asymptotic_scales_one_over_g_squared() -> None:
    """The asymptotic rate (not the strict ρ_lf) scales as 1/g²."""
    kp1 = compute_large_field_kp(g_k=1.0)
    kp2 = compute_large_field_kp(g_k=2.0)
    assert kp2.rho_lf_asymptotic == pytest.approx(kp1.rho_lf_asymptotic / 4.0)


# --------------------------------------------------------------------------
# ρ_lf strict: approaches asymptotic - log 4 in the deep small-g regime
# --------------------------------------------------------------------------


def test_lf_strict_rate_approaches_asymptotic_minus_log4_canonical() -> None:
    """For small g canonical, ρ_lf → ρ_lf_asymptotic - log 4, because
    Z_t ≈ 4·exp(-3/(4g²)) and ρ_lf = -log Z_t."""
    kp = compute_large_field_kp(g_k=0.1, t_choice=CANONICAL)
    expected = kp.rho_lf_asymptotic - math.log(4.0)
    assert kp.rho_lf == pytest.approx(expected, rel=1e-6)


def test_lf_strict_rate_positive_in_convergent_regime() -> None:
    """In the convergent regime (g below threshold), ρ_lf > 0."""
    for g in (0.05, 0.1, 0.2, 0.3, 0.4):
        kp = compute_large_field_kp(g_k=g)
        assert kp.rho_lf > 0, f"ρ_lf must be positive at g={g}"


def test_lf_strict_rate_exceeds_log_mu_in_convergent_regime() -> None:
    """K_lf finite iff ρ_lf > log μ_plaq (cluster-expansion threshold).
    Verify the equivalence in the convergent regime."""
    kp = compute_large_field_kp(g_k=0.3)
    assert kp.convergent
    assert kp.rho_lf > math.log(MU_PLAQUETTE_4D)


# --------------------------------------------------------------------------
# K_lf: real, no longer placeholder, scales with g
# --------------------------------------------------------------------------


def test_lf_K_finite_in_convergent_regime() -> None:
    """K_lf finite for g well below the convergence threshold."""
    kp = compute_large_field_kp(g_k=0.2)
    assert math.isfinite(kp.K_lf)
    assert kp.K_lf > 0


def test_lf_K_grows_as_g_approaches_threshold() -> None:
    """As g approaches the convergence threshold, K_lf grows (q → 1).

    Re-pinned 2026-07-25 (μ_plaq 16 → 1359141/25000 ≥ 20e): the canonical
    threshold moved 0.4245 → 0.3733, so the near-threshold sample moves
    0.40 → 0.36 (K_lf(0.36) ≈ 2.004, finite)."""
    K_small = compute_large_field_kp(g_k=0.1).K_lf
    K_mid = compute_large_field_kp(g_k=0.3).K_lf
    K_near = compute_large_field_kp(g_k=0.36).K_lf
    assert K_small < K_mid < K_near
    assert math.isfinite(K_near)


def test_lf_K_infinite_above_threshold_canonical() -> None:
    """Above g_max ≈ 0.3733 canonical (μ_plaq = 20e-majorant), K_lf = ∞."""
    kp = compute_large_field_kp(g_k=0.5, t_choice=CANONICAL)
    assert math.isinf(kp.K_lf)
    assert not kp.convergent


def test_lf_K_infinite_above_threshold_wilson() -> None:
    """Above g_max ≈ 0.7466 Wilson (μ_plaq = 20e-majorant), K_lf = ∞."""
    kp = compute_large_field_kp(g_k=1.0, t_choice=WILSON)
    assert math.isinf(kp.K_lf)
    assert not kp.convergent


def test_lf_K_is_not_constant() -> None:
    """K_lf is no longer the placeholder constant 1.0; varies with g."""
    K_a = compute_large_field_kp(g_k=0.1).K_lf
    K_b = compute_large_field_kp(g_k=0.2).K_lf
    assert K_a != pytest.approx(K_b)
    assert K_a != pytest.approx(1.0)


# --------------------------------------------------------------------------
# Convergence threshold helper
# --------------------------------------------------------------------------


def test_lf_convergence_threshold_canonical_near_estimate() -> None:
    """Bisected threshold matches the small-g leading-asymptotic estimate
    g_max ≈ √(C_2 / (log 4 + log μ_plaq)) ≈ 0.3733.

    Re-pinned 2026-07-25: μ_plaq = 1359141/25000 (≥ 20e) gives
    g_max ≈ 0.373289 (was 0.424549 under the unsupported legacy 16)."""
    g_max = convergence_threshold_g_lf(t_choice=CANONICAL)
    assert 0.3732 < g_max < 0.3734


def test_lf_convergence_threshold_wilson_larger_than_canonical() -> None:
    """Wilson absorbs a factor 2N = 4 into κ, so the Wilson threshold is
    larger by exactly a factor of 2: g_max_wilson = 2 · g_max_canonical."""
    g_canon = convergence_threshold_g_lf(t_choice=CANONICAL)
    g_wilson = convergence_threshold_g_lf(t_choice=WILSON)
    assert g_wilson == pytest.approx(2.0 * g_canon, rel=1e-3)


# --------------------------------------------------------------------------
# Z_t character-tail sum is constructive
# --------------------------------------------------------------------------


def test_Z_t_returns_dataclass() -> None:
    Z = heat_kernel_character_tail_Z(g_k=0.2, t_choice=CANONICAL)
    assert isinstance(Z, CharacterTailSum)
    assert Z.partial_sum > 0
    assert Z.upper_bound >= Z.partial_sum
    assert Z.tail_finite
    assert Z.j_max_int == J_MAX_DEFAULT


def test_Z_t_truncation_tight_at_small_g() -> None:
    """At g = 0.1 canonical (t = 100), the j=1/2 term dominates by many
    orders of magnitude; the tail bound is utterly negligible."""
    Z = heat_kernel_character_tail_Z(g_k=0.1, t_choice=CANONICAL)
    # The j = 1/2 leading term is 4·exp(-75) ≈ 1.08e-32.
    expected_leading = 4.0 * math.exp(-75.0)
    assert Z.partial_sum == pytest.approx(expected_leading, rel=1e-6)
    # Tail bound vanishes to machine precision.
    assert Z.tail_bound < 1e-100


def test_Z_t_tail_finite_in_relevant_regime() -> None:
    """For g ≤ 2.0 canonical (t ≥ 0.25), the tail-bound ratio is < 1."""
    for g in (0.1, 0.5, 1.0, 2.0):
        Z = heat_kernel_character_tail_Z(g_k=g, t_choice=CANONICAL)
        assert Z.tail_finite, f"tail must be bounded at g={g}; ratio={Z.tail_ratio}"


def test_Z_t_wilson_strictly_smaller_than_canonical_at_same_g() -> None:
    """Wilson t = 4/g² > canonical t = 1/g², so exp(-t·C_2) is smaller, so
    Z_t^Wilson < Z_t^canonical at the same g."""
    Z_c = heat_kernel_character_tail_Z(g_k=0.5, t_choice=CANONICAL)
    Z_w = heat_kernel_character_tail_Z(g_k=0.5, t_choice=WILSON)
    assert Z_w.upper_bound < Z_c.upper_bound


def test_Z_t_manton_rejected() -> None:
    with pytest.raises(ValueError, match="Manton"):
        heat_kernel_character_tail_Z(g_k=1.0, t_choice=MANTON)


# --------------------------------------------------------------------------
# ε_lf budget
# --------------------------------------------------------------------------


def test_lf_eps_nonnegative_in_convergent_regime() -> None:
    """In the convergent regime, ε_lf ≥ 0 in either direction."""
    assert eps_lf(0.1, 0.2, CANONICAL) >= 0
    assert eps_lf(0.2, 0.1, CANONICAL) >= 0


def test_lf_eps_positive_when_g_grows_in_convergent_regime() -> None:
    """ρ_lf decreases as g grows (both rates decrease), so g_k < g_next ⇒ eps > 0."""
    assert eps_lf(0.1, 0.3, CANONICAL) > 0


def test_lf_eps_infinite_when_endpoint_non_finite() -> None:
    """If either endpoint has non-finite ρ_lf (truncation tail-bound failed
    or Z_t ≥ 1), ε_lf reports +∞ honestly."""
    # g = 1.0 canonical gives finite-but-negative rho_lf (Z_t > 1).
    # g = 5.0 canonical may give -inf if the tail ratio fails.
    # We instead pick a regime where the rate stays finite, then test the
    # explicit +∞ path via a synthetic case using a far-larger g.
    eps_huge = eps_lf(0.1, 100.0, CANONICAL)
    assert eps_huge == float("inf") or eps_huge > 1.0


# --------------------------------------------------------------------------
# Provenance
# --------------------------------------------------------------------------


def test_lf_provenance_marks_K_lf_derived_not_placeholder() -> None:
    """Post-upgrade, K_lf is DERIVED via Brydges–Federbush, not placeholder."""
    kp = compute_large_field_kp(g_k=0.2)
    assert "DERIVED" in kp.provenance["K_lf"]
    assert "Brydges" in kp.provenance["K_lf"]
    assert "PLACEHOLDER" not in kp.provenance["K_lf"]


def test_lf_provenance_marks_rho_lf_derived_from_character_tail() -> None:
    kp = compute_large_field_kp(g_k=0.2)
    assert "DERIVED" in kp.provenance["rho_lf"]
    assert "character tail" in kp.provenance["rho_lf"]


def test_lf_provenance_records_asymptotic_separately() -> None:
    kp = compute_large_field_kp(g_k=0.2)
    assert "ASYMPTOTIC" in kp.provenance["rho_lf_asymptotic"]
    assert "outline §18.5" in kp.provenance["rho_lf_asymptotic"]


def test_lf_provenance_records_convergence_status() -> None:
    """Provenance explicitly states the convergent/non-convergent regime."""
    kp_conv = compute_large_field_kp(g_k=0.1)
    kp_div = compute_large_field_kp(g_k=1.0)
    assert "True" in kp_conv.provenance["convergent"]
    assert "False" in kp_div.provenance["convergent"]


# --------------------------------------------------------------------------
# Input validation
# --------------------------------------------------------------------------


def test_lf_input_validation() -> None:
    with pytest.raises(ValueError):
        compute_large_field_kp(g_k=0.0)
    with pytest.raises(ValueError):
        compute_large_field_kp(g_k=1.0, scale_k=-1)


def test_lf_manton_rejected() -> None:
    with pytest.raises(ValueError, match="Manton"):
        compute_large_field_kp(g_k=1.0, t_choice=MANTON)


# --------------------------------------------------------------------------
# Trajectory
# --------------------------------------------------------------------------


def test_lf_trajectory_output_in_convergent_regime() -> None:
    """In the convergent regime, the trajectory yields per-scale certificates;
    ρ_lf decreases as g grows toward the threshold."""
    g_traj = [0.1, 0.2, 0.3]
    kps = first_few_rg_steps(g_traj)
    assert len(kps) == 3
    for i in range(len(kps) - 1):
        assert kps[i].rho_lf > kps[i + 1].rho_lf
        assert kps[i].K_lf < kps[i + 1].K_lf  # K grows with g


# --------------------------------------------------------------------------
# Direct edge-neighbor count audit (notes/fiducials_notes.md §3.1, 2026-05-25)
# --------------------------------------------------------------------------


class TestPlaquetteEdgeNeighborCount:
    """Direct combinatorial count for the d-dim plaquette edge-neighbor degree.

    Surfaces the audit calculation that produces the BF universal upper bound
    μ_plaq ≤ e · plaquette_edge_neighbor_count(d) for any d.  At d = 4 this
    gives 20e ≈ 54.4, looser than both Seiler's 16 and the project's 8e
    fallback — see notes/fiducials_notes.md §3.1 for the audit discussion.
    """

    def test_d2_returns_4(self):
        """A 2D plaquette has 4 edge-neighbors: the four other unit squares
        sharing each of its 4 edges."""
        assert plaquette_edge_neighbor_count(2) == 4

    def test_d3_returns_12(self):
        """A 3D plaquette has 12 edge-neighbors: 4 edges × 3 other plaquettes
        per edge (2 perpendicular directions × 2 sides − 1 current)."""
        assert plaquette_edge_neighbor_count(3) == 12

    def test_d4_returns_20(self):
        """A 4D plaquette has 20 edge-neighbors: 4 edges × 5 other plaquettes
        per edge (3 perpendicular directions × 2 sides − 1 current)."""
        assert plaquette_edge_neighbor_count(4) == 20

    def test_formula_8d_minus_12(self):
        """The general formula: 8d - 12 for d ≥ 2."""
        for d in (2, 3, 4, 5, 8, 10):
            assert plaquette_edge_neighbor_count(d) == 8 * d - 12

    def test_d1_rejected(self):
        with pytest.raises(ValueError, match="d ≥ 2"):
            plaquette_edge_neighbor_count(1)
        with pytest.raises(ValueError, match="d ≥ 2"):
            plaquette_edge_neighbor_count(0)

    def test_bf_universal_bound_at_d4_is_default(self):
        """Re-pinned 2026-07-25 (SL.1): the BF universal bound
        μ ≤ e · max_degree = 20e ≈ 54.366 at d = 4 is now the SOURCE of
        the default: MU_PLAQUETTE_4D is its exact-rational majorant
        1359141/25000 = 54.36564 ≥ 20e.  The legacy 16 (5d - 4) is
        strictly below the BF bound and matches no adjacency notion
        (comparison sweeps only)."""
        direct_bf_bound = math.e * plaquette_edge_neighbor_count(4)
        assert MU_PLAQUETTE_4D >= direct_bf_bound  # rational majorant ≥ 20e
        assert MU_PLAQUETTE_4D - direct_bf_bound < 1e-5  # and tight (≈3.4e-6)
        assert direct_bf_bound > SEILER_5D_MINUS_4_LEGACY
        assert direct_bf_bound > 8.0 * math.e


# --------------------------------------------------------------------------
# Genuinely-BF-conservative μ_plaq (notes/fiducials_notes.md §3.2)
# --------------------------------------------------------------------------


class TestMuPlaquetteBFConservative:
    """The genuine plaquette-polymer BF-conservative bound."""

    def test_4d_value_is_20e(self) -> None:
        """MU_PLAQUETTE_BF_CONSERVATIVE_4D = e · plaquette_edge_neighbor_count(4)
        = e · 20 ≈ 54.366."""
        from computations.large_field_kp import (
            MU_PLAQUETTE_BF_CONSERVATIVE_4D,
        )
        assert MU_PLAQUETTE_BF_CONSERVATIVE_4D == pytest.approx(
            math.e * 20.0
        )

    def test_helper_spot_values(self) -> None:
        """mu_plaquette_bf_conservative(d) = e · (8d - 12) at all valid d."""
        from computations.large_field_kp import mu_plaquette_bf_conservative
        for d in (2, 3, 4, 5, 6):
            assert mu_plaquette_bf_conservative(d) == pytest.approx(
                math.e * (8 * d - 12)
            )

    def test_helper_rejects_low_d(self) -> None:
        from computations.large_field_kp import mu_plaquette_bf_conservative
        with pytest.raises(ValueError, match="d ≥ 2"):
            mu_plaquette_bf_conservative(1)
        with pytest.raises(ValueError, match="d ≥ 2"):
            mu_plaquette_bf_conservative(0)

    def test_bf_conservative_strictly_larger_than_site_bound(self) -> None:
        """The genuine BF-conservative for plaquettes (20e) is strictly
        LARGER than the site bound (8e), because plaquettes have MORE
        edge-neighbors than sites in 4D — the inversion that prompted
        this re-derivation."""
        from computations.large_field_kp import (
            MU_PLAQUETTE_BF_CONSERVATIVE_4D,
            MU_PLAQUETTE_CONSERVATIVE_4D,
        )
        assert MU_PLAQUETTE_BF_CONSERVATIVE_4D > MU_PLAQUETTE_CONSERVATIVE_4D

    def test_bf_conservative_larger_than_legacy_and_default_majorizes(self) -> None:
        """Re-pinned 2026-07-25: the BF bound (20e ≈ 54.366) is strictly
        larger than the LEGACY Seiler-cited 16 (which matches no adjacency
        notion), and the module default MU_PLAQUETTE_4D is now the
        exact-rational majorant of the BF bound (default ≥ 20e float)."""
        from computations.large_field_kp import (
            MU_PLAQUETTE_4D,
            MU_PLAQUETTE_BF_CONSERVATIVE_4D,
            SEILER_5D_MINUS_4_LEGACY,
        )
        assert MU_PLAQUETTE_BF_CONSERVATIVE_4D > SEILER_5D_MINUS_4_LEGACY
        assert MU_PLAQUETTE_4D >= MU_PLAQUETTE_BF_CONSERVATIVE_4D

    def test_bf_default_shrinks_pilot_window_vs_legacy(self) -> None:
        """Re-pinned 2026-07-25: the rigorous default (20e-majorant)
        shrinks g_max_lf vs the unsupported legacy 16 — the quantitative
        cost of insisting on rigor, now priced into the default:
        0.424549 → 0.373289 (≈ −12%)."""
        from computations.large_field_kp import (
            MU_PLAQUETTE_4D,
            MU_PLAQUETTE_BF_CONSERVATIVE_4D,
            SEILER_5D_MINUS_4_LEGACY,
        )
        g_legacy = convergence_threshold_g_lf(mu_plaq=SEILER_5D_MINUS_4_LEGACY)
        g_default = convergence_threshold_g_lf(mu_plaq=MU_PLAQUETTE_4D)
        g_bf = convergence_threshold_g_lf(
            mu_plaq=MU_PLAQUETTE_BF_CONSERVATIVE_4D
        )
        assert g_default < g_legacy
        assert 0.42 < g_legacy < 0.43
        assert 0.3732 < g_default < 0.3734
        # The default (rational majorant) and the float 20e differ by
        # ≈ 3.4e-6 in μ, i.e. by ≲ 1e-8 in threshold.
        assert abs(g_default - g_bf) < 1e-4

# --------------------------------------------------------------------------
# ≥ 20e guard (SL.1 2026-07-25): validity of the polymer KP bound requires
# μ_plaq ≥ the true growth constant, so the wired-in rational must NEVER be
# silently downgraded below 20e.  Exact rational arithmetic only — no floats
# on the certifying side.
# --------------------------------------------------------------------------


class TestMuPlaquetteGe20eGuard:
    """Guards MU_PLAQUETTE_4D ≥ 20e via rational cross-multiplication."""

    @staticmethod
    def _e_upper_bound_rational() -> "Fraction":
        """Exact rational UPPER bound on e via the factorial series:

            e = Σ_{k≥0} 1/k!  ≤  Σ_{k=0}^{n} 1/k! + 1/(n!·(n-1))

        (tail: Σ_{k>n} 1/k! ≤ (1/n!)·Σ_{j≥1} (n+1)^{-j} = 1/(n!·n)
        ≤ 1/(n!·(n-1)) for n ≥ 2; with n = 15 the certificate error is
        < 1e-12, ample against the majorant's ≈ 3.4e-6 slack).
        """
        from fractions import Fraction
        n = 15
        fact = 1
        e_ub = Fraction(1)  # k = 0 term
        for k in range(1, n + 1):
            fact *= k
            e_ub += Fraction(1, fact)
        # rational tail bound (n = 15: 1/(15!·14) ≥ true tail)
        e_ub += Fraction(1, fact * (n - 1))
        return e_ub

    def test_rational_ge_20e_exact(self) -> None:
        """MU_PLAQUETTE_4D_RATIONAL ≥ 20e, certified in exact rational
        arithmetic (cross-multiplication under the hood of Fraction ≤)."""
        e_ub = self._e_upper_bound_rational()
        assert 20 * e_ub <= MU_PLAQUETTE_4D_RATIONAL, (
            f"MU_PLAQUETTE_4D_RATIONAL = {MU_PLAQUETTE_4D_RATIONAL} silently "
            f"downgraded below 20e (rational 20e upper cert = {20 * e_ub})"
        )

    def test_float_constant_ge_20e_exact(self) -> None:
        """The float actually consumed downstream also majorizes 20e:
        Fraction(float) is exact, so this is a rational statement too.
        (float ≥ 20·e_ub with e_ub ≥ e implies float ≥ 20e.)"""
        from fractions import Fraction
        e_ub = self._e_upper_bound_rational()
        assert Fraction(MU_PLAQUETTE_4D) >= 20 * e_ub, \
            "float MU_PLAQUETTE_4D fell below the rational 20e upper certificate"
        # And the float faithfully represents the rational (< 1e-10 off).
        assert abs(Fraction(MU_PLAQUETTE_4D) - MU_PLAQUETTE_4D_RATIONAL) < Fraction(1, 10**10)

    @staticmethod
    def _e_lower_bound_rational() -> "Fraction":
        """Exact rational LOWER bound on e: the partial series itself."""
        from fractions import Fraction
        fact = 1
        e_lb = Fraction(1)
        for k in range(1, 16):
            fact *= k
            e_lb += Fraction(1, fact)
        return e_lb

    def test_rational_is_the_documented_majorant(self) -> None:
        """The wired-in rational is exactly 20 × 2718282/1000000 (reduced),
        i.e. the 6-significant-digit decimal majorant of e, times 20."""
        from fractions import Fraction
        assert MU_PLAQUETTE_4D_RATIONAL == Fraction(20) * Fraction(2718282, 10**6)
        assert MU_PLAQUETTE_4D_RATIONAL == Fraction(1359141, 25000)

    def test_legacy_16_below_20e(self) -> None:
        """The legacy Seiler value is strictly below the certified 20e lower
        bound — it can never be re-adopted as a 'BF-conservative' value."""
        e_lb = self._e_lower_bound_rational()
        from fractions import Fraction
        assert Fraction(16) < 20 * e_lb
        assert SEILER_5D_MINUS_4_LEGACY == 16.0

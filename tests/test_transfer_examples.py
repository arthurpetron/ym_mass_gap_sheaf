"""Tests for `computations.transfer_examples` (Milestone 4.1).

Verifies that the EKF-side toy and the YM-side σ̂ pilot satisfy the same
`InductiveBoundWitness` Protocol — the work_plan-§4.1 "test showing that
the validators have isomorphic type signatures."

The structural isomorphism test is the load-bearing claim: both
instances pass `isinstance(_, InductiveBoundWitness)` *without* sharing
inheritance, which is the type-level realization of the §6 codynamic
correspondence.
"""

from __future__ import annotations

import pytest

from computations.transfer_examples import (
    BoundWitness,
    InductiveBoundWitness,
    RunResult,
    run_inductive_steps,
)
from computations.transfer_examples.ekf_example import EKFStep, toy_ekf_pilot
from computations.transfer_examples.ym_example import YMStep, toy_ym_pilot


# --------------------------------------------------------------------------
# Protocol conformance: both instances satisfy InductiveBoundWitness
# --------------------------------------------------------------------------


class TestProtocolConformance:
    """The structural-typing claim of Milestone 4.1."""

    def test_ekf_satisfies_protocol(self):
        ekf = toy_ekf_pilot(n_measurements=5)
        assert isinstance(ekf, InductiveBoundWitness), (
            "EKFStep must satisfy InductiveBoundWitness Protocol"
        )

    def test_ym_satisfies_protocol(self):
        ym = toy_ym_pilot(g_0=0.10, K=4)
        assert isinstance(ym, InductiveBoundWitness), (
            "YMStep must satisfy InductiveBoundWitness Protocol"
        )

    def test_ekf_and_ym_have_no_inheritance_relation(self):
        """The structural-typing point: neither class subclasses the other,
        nor a common ancestor beyond `object`.  The Protocol conformance is
        purely structural — exactly the codynamic-transfer claim."""
        assert not issubclass(EKFStep, YMStep)
        assert not issubclass(YMStep, EKFStep)
        # And neither inherits Protocol — `runtime_checkable` doesn't require it.
        assert EKFStep.__mro__ == (EKFStep, object)
        assert YMStep.__mro__ == (YMStep, object)


# --------------------------------------------------------------------------
# Interface members exist and have the right types on both instances
# --------------------------------------------------------------------------


class TestProtocolMembers:
    """Each Protocol member is present and well-typed on both instances."""

    @pytest.fixture
    def instances(self) -> list[InductiveBoundWitness]:
        return [
            toy_ekf_pilot(n_measurements=5),
            toy_ym_pilot(g_0=0.10, K=4),
        ]

    def test_scale_index_is_int(self, instances):
        for s in instances:
            assert isinstance(s.scale_index, int)
            assert s.scale_index == 0  # both start at scale 0

    def test_bound_witness_is_BoundWitness(self, instances):
        for s in instances:
            bw = s.bound_witness
            assert isinstance(bw, BoundWitness)
            assert isinstance(bw.bound, float)
            assert isinstance(bw.label, str)
            assert bw.bound > 0  # both instances start with positive bound

    def test_remaining_budget_is_positive_float(self, instances):
        for s in instances:
            assert isinstance(s.remaining_budget, float)
            assert s.remaining_budget > 0

    def test_degradation_is_nonneg_float(self, instances):
        for s in instances:
            assert isinstance(s.degradation, float)
            assert s.degradation >= 0

    def test_step_returns_protocol_or_none(self, instances):
        for s in instances:
            next_s = s.step()
            # Either None (failure) or a fresh InductiveBoundWitness.
            if next_s is not None:
                assert isinstance(next_s, InductiveBoundWitness)
                assert next_s.scale_index == s.scale_index + 1

    def test_overlap_compatible_is_bool(self, instances):
        for s in instances:
            # Self-overlap: should be True since bounds agree exactly.
            assert s.overlap_compatible(s) is True

    def test_cross_type_overlap_refused(self, instances):
        # EKF-vs-YM overlap is structurally decidable (isinstance check),
        # but semantically meaningless; should refuse.
        ekf, ym = instances
        assert ekf.overlap_compatible(ym) is False
        assert ym.overlap_compatible(ekf) is False


# --------------------------------------------------------------------------
# Generic runner works on both instances
# --------------------------------------------------------------------------


class TestGenericRunner:
    """The same `run_inductive_steps` function consumes either instance and
    returns a `RunResult`.  This is the operational form of the §6
    transferred-lemma claim: one runner, two domains."""

    def test_runner_on_ekf(self):
        ekf = toy_ekf_pilot(n_measurements=5, initial_budget=5.0)
        result = run_inductive_steps(ekf, K=4)
        assert isinstance(result, RunResult)
        assert result.n_steps_taken == 4
        assert result.closes is True
        assert result.total_degradation > 0  # actual EKF innovations

    def test_runner_on_ym(self):
        ym = toy_ym_pilot(g_0=0.10, K=4, sigma_hat_initial=10.0)
        result = run_inductive_steps(ym, K=4)
        assert isinstance(result, RunResult)
        assert result.n_steps_taken == 4
        assert result.closes is True

    def test_runner_signature_is_polymorphic(self):
        """One function, two domain types — the load-bearing test."""
        ekf = toy_ekf_pilot(n_measurements=3)
        ym = toy_ym_pilot(g_0=0.10, K=3)
        # The SAME callable handles both; this is the type-level realization
        # of the codynamic-transfer template.
        r_ekf = run_inductive_steps(ekf, K=2)
        r_ym = run_inductive_steps(ym, K=2)
        # Both produce a RunResult with the same field shape.
        for r in (r_ekf, r_ym):
            assert isinstance(r, RunResult)
            assert hasattr(r, "n_steps_taken")
            assert hasattr(r, "total_degradation")
            assert hasattr(r, "closes")
            assert hasattr(r, "per_step_bounds")

    def test_runner_negative_K_rejected(self):
        ekf = toy_ekf_pilot(n_measurements=3)
        with pytest.raises(ValueError, match="non-negative"):
            run_inductive_steps(ekf, K=-1)

    def test_runner_zero_steps_returns_initial(self):
        ekf = toy_ekf_pilot(n_measurements=3)
        result = run_inductive_steps(ekf, K=0)
        assert result.n_steps_taken == 0
        assert result.total_degradation == 0.0
        assert result.final_state is ekf


# --------------------------------------------------------------------------
# Failure modes: budget exhaustion / trajectory end
# --------------------------------------------------------------------------


class TestFailureModes:
    """Both instances honestly report failure when their preconditions break."""

    def test_ekf_budget_exhaustion(self):
        """A small initial budget against modest innovations — should
        exhaust mid-trajectory and report closes=False."""
        ekf = toy_ekf_pilot(n_measurements=10, initial_budget=0.05)
        result = run_inductive_steps(ekf, K=9)
        assert result.closes is False
        assert result.n_steps_taken < 9  # stopped early

    def test_ym_trajectory_exhaustion(self):
        """Requesting more steps than the σ̂ trajectory has produces
        early termination at the trajectory's end."""
        ym = toy_ym_pilot(g_0=0.10, K=2)  # trajectory has 3 σ̂ entries
        # Ask for more steps than the trajectory provides.
        result = run_inductive_steps(ym, K=10)
        # Should stop when trajectory exhausted.
        assert result.n_steps_taken < 10


# --------------------------------------------------------------------------
# Structural correspondence with notes/codynamic-transfer.md §4
# --------------------------------------------------------------------------


class TestStructuralCorrespondence:
    """Snapshot test: the BoundWitness labels reflect the §4 correspondence
    (EKF P_n ↔ YM σ̂_k)."""

    def test_ekf_label_starts_with_EKF_P(self):
        ekf = toy_ekf_pilot(n_measurements=3)
        assert ekf.bound_witness.label.startswith("EKF P_")

    def test_ym_label_starts_with_YM_sigma_hat(self):
        ym = toy_ym_pilot(g_0=0.10, K=2)
        assert ym.bound_witness.label.startswith("YM σ̂_")

    def test_scale_indices_advance_by_one(self):
        """The Protocol contract: scale_index is monotone, +1 per successful step."""
        for initial in (toy_ekf_pilot(n_measurements=5), toy_ym_pilot(g_0=0.10, K=4)):
            indices = [initial.scale_index]
            s: InductiveBoundWitness | None = initial
            for _ in range(3):
                next_s = s.step()
                if next_s is None:
                    break
                indices.append(next_s.scale_index)
                s = next_s
            for a, b in zip(indices, indices[1:]):
                assert b == a + 1

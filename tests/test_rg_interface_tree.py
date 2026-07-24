"""Tests for evolving-interface RG polynomial-tree bookkeeping."""

from __future__ import annotations

from fractions import Fraction

import pytest

from computations.rg_interface_tree import (
    ResponseKind,
    RGAction,
    RGInterfaceTree,
    RGLogEntry,
    RGState,
    RGStep,
    approximate_tree,
    demo_log,
    demo_stable_tail_certificate,
    initial_interface,
    stable_reference,
    tail_interface,
    tail_to_stable_transport,
    transported_contraction_ratio,
    verification_interface,
)


def test_depth_one_two_three_approximants_are_executable() -> None:
    tree = RGInterfaceTree()
    approximants = [approximate_tree(tree, initial_interface(), depth) for depth in (1, 2, 3)]
    assert all(approximation is not None for approximation in approximants)
    assert approximants[0] is not None
    assert approximants[0].interface.name == "uv_0"
    assert approximants[0].children[0][2] is None
    assert approximants[1] is not None
    assert approximants[1].children[0][2] is not None
    assert approximants[2] is not None
    verification = approximants[2].children[0][2]
    assert verification is not None
    assert len(verification.children) == 2


def test_interface_stabilization_metric_decreases_to_requested_resolution() -> None:
    reference = stable_reference()
    assert reference.discrepancy_to_stable.maximum == 0
    discrepancies = [tail_interface(scale).discrepancy_to_stable.maximum for scale in range(2, 9)]
    assert all(
        right < left
        for left, right in zip(discrepancies[:-1], discrepancies[1:], strict=True)
    )
    assert discrepancies[-1] <= Fraction(1, 2**8)


def test_interface_transport_preserves_semantics_and_round_trips_state() -> None:
    transport = tail_to_stable_transport(4)
    state = RGState(
        interface_name=transport.source.name,
        effective_theory=(Fraction(7, 5), Fraction(-2, 3)),
        observable=Fraction(11, 13),
        certificate_count=4,
        cumulative_dynamic_error=Fraction(1, 32),
        cumulative_interface_error=Fraction(1, 16),
    )
    assert all(transport.semantics_preserved(value) for value in state.effective_theory)
    assert transport.semantics_preserved(state.observable)
    assert transport.state_backward(transport.state_forward(state)) == state


def test_stable_tail_certificate_returns_checked_scale_and_suffix() -> None:
    certificate = demo_stable_tail_certificate()
    epsilon = Fraction(1, 100)
    physical_scale = certificate.scale_for(epsilon)
    offset = physical_scale - certificate.k_star
    assert certificate.validates_offset(offset)
    assert certificate.discrepancy_at_offset(offset) <= epsilon
    assert certificate.validates_resolution(epsilon, suffix_length=64)


def test_stable_tail_certificate_rejects_nonpositive_resolution() -> None:
    certificate = demo_stable_tail_certificate()
    with pytest.raises(ValueError, match="must be positive"):
        certificate.scale_for(Fraction(0))


def test_transported_contraction_is_measured_in_one_interface() -> None:
    source = tail_interface(3)
    target = tail_interface(4)
    ratio = transported_contraction_ratio(
        source=source,
        target=target,
        x=Fraction(7, 5),
        y=Fraction(-2, 3),
        q=Fraction(3, 4),
    )
    assert ratio == Fraction(3, 4)


def test_verification_branch_sensitivity_preserves_failure() -> None:
    tree = RGInterfaceTree()
    interface = verification_interface()
    success = tree.child(interface, RGAction.VERIFY_BOUNDS, ResponseKind.VERIFIED)
    failure = tree.child(interface, RGAction.VERIFY_BOUNDS, ResponseKind.FAILED)
    assert success.name == "tail_2"
    assert failure.name == "diagnostic_2"
    assert success != failure


def test_illegal_action_or_response_is_rejected() -> None:
    tree = RGInterfaceTree()
    with pytest.raises(ValueError, match="not legal"):
        tree.child(initial_interface(), RGAction.VERIFY_BOUNDS, ResponseKind.VERIFIED)
    with pytest.raises(ValueError, match="not legal"):
        tree.child(
            verification_interface(),
            RGAction.VERIFY_BOUNDS,
            ResponseKind.TRANSPORTED,
        )


def test_typed_step_rejects_state_for_wrong_child_interface() -> None:
    source_interface = initial_interface()
    selected = verification_interface()
    source_state = RGState(
        source_interface.name,
        (Fraction(1),),
        Fraction(1),
        0,
        Fraction(0),
        Fraction(0),
    )
    wrong_next_state = RGState(
        "tail_2",
        (Fraction(1),),
        Fraction(1),
        1,
        Fraction(1),
        Fraction(1),
    )
    with pytest.raises(ValueError, match="invalid for the selected child"):
        RGStep(
            source_interface=source_interface,
            source_state=source_state,
            action=RGAction.INTEGRATE_FLUCTUATION,
            response=ResponseKind.INTEGRATED,
            next_interface=selected,
            next_state=wrong_next_state,
            analytic_witness=True,
            observable_transport_witness=True,
            certificate_update_witness=True,
            cumulative_error_witness=True,
        )


def test_log_separates_dynamic_and_interface_distortion() -> None:
    entries = demo_log(5)
    assert all(isinstance(entry, RGLogEntry) for entry in entries)
    assert all(entry.certificate_status == "verified" for entry in entries)
    assert all(entry.contraction_q == Fraction(3, 4) for entry in entries)
    assert all(
        entry.combined_distortion == entry.dynamic_distortion * entry.interface_distortion
        for entry in entries
    )
    dynamic_excess = sum((entry.dynamic_distortion - 1 for entry in entries), Fraction(0))
    interface_excess = sum((entry.interface_distortion - 1 for entry in entries), Fraction(0))
    assert dynamic_excess < Fraction(1, 4)
    assert interface_excess < Fraction(1, 2)

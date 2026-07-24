"""Executable changing-interface RG scaffold.

The existing numerical pipeline evolves effective-theory values.  This module
adds the orthogonal structural record requested by the polynomial-tree update:
the legal actions, response evidence, carrier types, observables, norms, and
certificates can change after every interaction.

This is bookkeeping and falsification infrastructure, not a contraction proof.
All demonstration arithmetic is exact ``Fraction`` arithmetic so the tests do
not turn interface stability into a floating-point convention.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from typing import TypeAlias


class RGAction(Enum):
    """Implementation-independent actions at an RG interface."""

    INTEGRATE_FLUCTUATION = "integrate_fluctuation"
    EXTRACT_RELEVANT_PART = "extract_relevant_part"
    LOCALIZE_POLYMER = "localize_polymer"
    RESCALE_FIELDS = "rescale_fields"
    TRANSPORT_OBSERVABLE = "transport_observable"
    VERIFY_BOUNDS = "verify_bounds"
    ABORT_WITH_COUNTEREXAMPLE = "abort_with_counterexample"


class ResponseKind(Enum):
    """Response evidence used by the executable approximation."""

    INTEGRATED = "integrated"
    VERIFIED = "verified"
    FAILED = "failed"
    TRANSPORTED = "transported"
    DIAGNOSTIC_RECORDED = "diagnostic_recorded"


@dataclass(frozen=True)
class InterfaceDiscrepancy:
    """The four components of the interface-discrepancy maximum."""

    coordinate: Fraction
    norm: Fraction
    observable: Fraction
    certificate: Fraction

    @property
    def maximum(self) -> Fraction:
        """Return ``d_int = max(d_coord, d_norm, d_obs, d_cert)``."""
        return max(self.coordinate, self.norm, self.observable, self.certificate)


ActionResponses: TypeAlias = tuple[tuple[RGAction, tuple[ResponseKind, ...]], ...]


@dataclass(frozen=True)
class RGInterface:
    """One scale's polynomial interface plus its scale-dependent carriers."""

    name: str
    scale: int
    action_responses: ActionResponses
    retained_fields: tuple[str, ...]
    admissible_polymers: tuple[str, ...]
    relevant_coordinates: tuple[str, ...]
    norm_name: str
    observable_family: tuple[str, ...]
    certificate_schema: tuple[str, ...]
    discrepancy_to_stable: InterfaceDiscrepancy
    chart_scale: Fraction

    def responses_for(self, action: RGAction) -> tuple[ResponseKind, ...]:
        """Return the response directions accepted after ``action``."""
        for candidate, responses in self.action_responses:
            if candidate is action:
                return responses
        raise ValueError(f"action {action.value!r} is not legal at interface {self.name!r}")


def stable_reference() -> RGInterface:
    """The limiting fixed interface used only as a comparison target."""
    zero = InterfaceDiscrepancy(*(Fraction(0) for _ in range(4)))
    return RGInterface(
        name="stable_reference",
        scale=-1,
        action_responses=((RGAction.TRANSPORT_OBSERVABLE, (ResponseKind.TRANSPORTED,)),),
        retained_fields=("effective_connection",),
        admissible_polymers=("localized_polymer",),
        relevant_coordinates=("g", "m", "Z", "K"),
        norm_name="gaussian",
        observable_family=("transported_local",),
        certificate_schema=("analytic", "interface", "observable", "error"),
        discrepancy_to_stable=zero,
        chart_scale=Fraction(1),
    )


def tail_interface(scale: int) -> RGInterface:
    """A coherently transported tail whose interface discrepancy tends to zero."""
    if scale < 2:
        raise ValueError("the demonstration tail begins at scale 2")
    discrepancy = Fraction(1, 2**scale)
    return RGInterface(
        name=f"tail_{scale}",
        scale=scale,
        action_responses=((RGAction.TRANSPORT_OBSERVABLE, (ResponseKind.TRANSPORTED,)),),
        retained_fields=("effective_connection",),
        admissible_polymers=("localized_polymer",),
        relevant_coordinates=("g", "m", "Z", "K"),
        norm_name="gaussian",
        observable_family=(f"transported_local_r{scale}",),
        certificate_schema=("analytic", "interface", "observable", "error"),
        discrepancy_to_stable=InterfaceDiscrepancy(
            discrepancy, discrepancy, discrepancy, discrepancy
        ),
        chart_scale=Fraction(1) + discrepancy,
    )


def initial_interface() -> RGInterface:
    """Microscopic interface before fluctuation integration."""
    return RGInterface(
        name="uv_0",
        scale=0,
        action_responses=((RGAction.INTEGRATE_FLUCTUATION, (ResponseKind.INTEGRATED,)),),
        retained_fields=("fine_link", "fluctuation_field"),
        admissible_polymers=("fine_connected_set",),
        relevant_coordinates=("bare_coupling",),
        norm_name="polymer",
        observable_family=("microscopic_wilson",),
        certificate_schema=("integration",),
        discrepancy_to_stable=InterfaceDiscrepancy(*(Fraction(1) for _ in range(4))),
        chart_scale=Fraction(2),
    )


def verification_interface() -> RGInterface:
    """Interface where success and failure select different children."""
    return RGInterface(
        name="verify_1",
        scale=1,
        action_responses=(
            (RGAction.VERIFY_BOUNDS, (ResponseKind.VERIFIED, ResponseKind.FAILED)),
        ),
        retained_fields=("coarse_field",),
        admissible_polymers=("coarse_connected_set", "localized_polymer"),
        relevant_coordinates=("g", "m", "Z", "remainder"),
        norm_name="polymer_to_gaussian",
        observable_family=("blocked_wilson",),
        certificate_schema=("candidate_contraction", "counterexample"),
        discrepancy_to_stable=InterfaceDiscrepancy(
            Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)
        ),
        chart_scale=Fraction(3, 2),
    )


def diagnostic_interface(scale: int) -> RGInterface:
    """Failure branch preserving the counterexample as explicit data."""
    return RGInterface(
        name=f"diagnostic_{scale}",
        scale=scale,
        action_responses=(
            (
                RGAction.ABORT_WITH_COUNTEREXAMPLE,
                (ResponseKind.DIAGNOSTIC_RECORDED,),
            ),
        ),
        retained_fields=("counterexample_configuration",),
        admissible_polymers=("offending_polymer",),
        relevant_coordinates=("failed_bound",),
        norm_name="diagnostic",
        observable_family=("failure_probe",),
        certificate_schema=("counterexample",),
        discrepancy_to_stable=InterfaceDiscrepancy(*(Fraction(1) for _ in range(4))),
        chart_scale=Fraction(1),
    )


@dataclass(frozen=True)
class RGInterfaceTree:
    """Child selection for the demonstration polynomial tree."""

    def child(
        self, interface: RGInterface, action: RGAction, response: ResponseKind
    ) -> RGInterface:
        """Select the next interface after validating the response direction."""
        if response not in interface.responses_for(action):
            raise ValueError(
                f"response {response.value!r} is not legal after {action.value!r} "
                f"at {interface.name!r}"
            )
        if interface.name == "uv_0":
            return verification_interface()
        if interface.name == "verify_1":
            if response is ResponseKind.VERIFIED:
                return tail_interface(2)
            return diagnostic_interface(2)
        if interface.name.startswith("tail_"):
            return tail_interface(interface.scale + 1)
        if interface.name.startswith("diagnostic_"):
            return diagnostic_interface(interface.scale + 1)
        raise ValueError(f"no child rule for interface {interface.name!r}")


@dataclass(frozen=True)
class PolyTreeApproximation:
    """One finite observation of the interface tree."""

    interface: RGInterface
    children: tuple[tuple[RGAction, ResponseKind, PolyTreeApproximation | None], ...]


def approximate_tree(
    tree: RGInterfaceTree, interface: RGInterface, depth: int
) -> PolyTreeApproximation | None:
    """Build the executable depth-``depth`` approximant (including 1, 2, 3)."""
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    if depth == 0:
        return None
    children = tuple(
        (
            action,
            response,
            approximate_tree(tree, tree.child(interface, action, response), depth - 1),
        )
        for action, responses in interface.action_responses
        for response in responses
    )
    return PolyTreeApproximation(interface=interface, children=children)


@dataclass(frozen=True)
class RGState:
    """Numerical state tagged by the interface in which it is admissible."""

    interface_name: str
    effective_theory: tuple[Fraction, ...]
    observable: Fraction
    certificate_count: int
    cumulative_dynamic_error: Fraction
    cumulative_interface_error: Fraction


@dataclass(frozen=True)
class RGStep:
    """A checked state/interface transition with four explicit witnesses."""

    source_interface: RGInterface
    source_state: RGState
    action: RGAction
    response: ResponseKind
    next_interface: RGInterface
    next_state: RGState
    analytic_witness: bool
    observable_transport_witness: bool
    certificate_update_witness: bool
    cumulative_error_witness: bool

    def __post_init__(self) -> None:
        expected = RGInterfaceTree().child(self.source_interface, self.action, self.response)
        if self.source_state.interface_name != self.source_interface.name:
            raise ValueError("source state is invalid for its claimed interface")
        if self.next_interface != expected:
            raise ValueError("next interface is not the selected polynomial-tree child")
        if self.next_state.interface_name != self.next_interface.name:
            raise ValueError("next state is invalid for the selected child interface")
        if not all(
            (
                self.analytic_witness,
                self.observable_transport_witness,
                self.certificate_update_witness,
                self.cumulative_error_witness,
            )
        ):
            raise ValueError("every RG transition witness must be explicit and successful")


@dataclass(frozen=True)
class InterfaceTransport:
    """Exact chart transport between two compatible RG interfaces.

    The demonstration interfaces share rational coordinate payloads.  Their
    chart scales provide mutually inverse maps into a common stable chart;
    all non-coordinate state evidence is preserved verbatim.
    """

    source: RGInterface
    target: RGInterface

    def forward(self, value: Fraction) -> Fraction:
        """Move a coordinate from the source chart to the target chart."""
        return self.source.chart_scale * value / self.target.chart_scale

    def backward(self, value: Fraction) -> Fraction:
        """Move a coordinate from the target chart back to the source chart."""
        return self.target.chart_scale * value / self.source.chart_scale

    def semantics_preserved(self, value: Fraction) -> bool:
        """Check equality after interpretation in the common stable chart."""
        transported = self.forward(value)
        return self.target.chart_scale * transported == self.source.chart_scale * value

    def state_forward(self, state: RGState) -> RGState:
        """Transport a complete state while keeping error ledgers separate."""
        if state.interface_name != self.source.name:
            raise ValueError("state is invalid for the transport source interface")
        return RGState(
            interface_name=self.target.name,
            effective_theory=tuple(self.forward(value) for value in state.effective_theory),
            observable=self.forward(state.observable),
            certificate_count=state.certificate_count,
            cumulative_dynamic_error=state.cumulative_dynamic_error,
            cumulative_interface_error=state.cumulative_interface_error,
        )

    def state_backward(self, state: RGState) -> RGState:
        """Pull a complete target state back through the inverse chart map."""
        if state.interface_name != self.target.name:
            raise ValueError("state is invalid for the transport target interface")
        return RGState(
            interface_name=self.source.name,
            effective_theory=tuple(self.backward(value) for value in state.effective_theory),
            observable=self.backward(state.observable),
            certificate_count=state.certificate_count,
            cumulative_dynamic_error=state.cumulative_dynamic_error,
            cumulative_interface_error=state.cumulative_interface_error,
        )


def tail_to_stable_transport(scale: int) -> InterfaceTransport:
    """Construct the exact transport from a demo tail scale to the stable chart."""
    return InterfaceTransport(source=tail_interface(scale), target=stable_reference())


InterfaceAtOffset: TypeAlias = Callable[[int], RGInterface]
TransportAtOffset: TypeAlias = Callable[[int], InterfaceTransport]
RationalAtOffset: TypeAlias = Callable[[int], Fraction]
StabilizationModulus: TypeAlias = Callable[[Fraction], int]


@dataclass(frozen=True)
class StableTailCertificate:
    """Executable RG-I5 certificate with an explicit branch and modulus."""

    k_star: int
    stable_interface: RGInterface
    interface_at_offset: InterfaceAtOffset
    transport_at_offset: TransportAtOffset
    discrepancy_at_offset: RationalAtOffset
    tolerance_at_offset: RationalAtOffset
    modulus: StabilizationModulus

    def scale_for(self, epsilon: Fraction) -> int:
        """Return a physical scale whose whole suffix is within ``epsilon``."""
        if epsilon <= 0:
            raise ValueError("stabilization resolution must be positive")
        return self.k_star + self.modulus(epsilon)

    def validates_offset(self, offset: int) -> bool:
        """Validate interface, transport, and discrepancy data at one offset."""
        if offset < 0:
            raise ValueError("tail offset must be nonnegative")
        interface = self.interface_at_offset(offset)
        transport = self.transport_at_offset(offset)
        discrepancy = self.discrepancy_at_offset(offset)
        tolerance = self.tolerance_at_offset(offset)
        return (
            interface == transport.source
            and transport.target == self.stable_interface
            and discrepancy == interface.discrepancy_to_stable.maximum
            and Fraction(0) <= discrepancy <= tolerance
        )

    def validates_resolution(self, epsilon: Fraction, suffix_length: int = 32) -> bool:
        """Check the certified suffix beginning at the computed modulus.

        This is a finite executable regression check for the exact formula
        used by the certificate; the Lean certificate carries the universal
        suffix proof.
        """
        if epsilon <= 0:
            raise ValueError("stabilization resolution must be positive")
        if suffix_length < 1:
            raise ValueError("suffix length must be positive")
        first_offset = self.modulus(epsilon)
        return all(
            self.validates_offset(offset)
            and self.discrepancy_at_offset(offset) <= epsilon
            for offset in range(first_offset, first_offset + suffix_length)
        )


def _dyadic_stabilization_modulus(epsilon: Fraction) -> int:
    """Return the least tail offset with ``2^-(offset+2) <= epsilon``."""
    if epsilon <= 0:
        raise ValueError("stabilization resolution must be positive")
    offset = 0
    while Fraction(1, 2 ** (offset + 2)) > epsilon:
        offset += 1
    return offset


def demo_stable_tail_certificate() -> StableTailCertificate:
    """Build the exact dyadic stabilization certificate for the demo branch."""
    return StableTailCertificate(
        k_star=2,
        stable_interface=stable_reference(),
        interface_at_offset=lambda offset: tail_interface(offset + 2),
        transport_at_offset=lambda offset: tail_to_stable_transport(offset + 2),
        discrepancy_at_offset=lambda offset: tail_interface(
            offset + 2
        ).discrepancy_to_stable.maximum,
        tolerance_at_offset=lambda offset: Fraction(1, 2 ** (offset + 2)),
        modulus=_dyadic_stabilization_modulus,
    )


@dataclass(frozen=True)
class RGLogEntry:
    """Scale log with dynamic and interface distortion kept separate."""

    interface: RGInterface
    state: RGState
    operator_name: str
    contraction_q: Fraction
    dynamic_distortion: Fraction
    interface_distortion: Fraction
    observable_error: Fraction
    certificate_status: str

    @property
    def combined_distortion(self) -> Fraction:
        """Return ``C_dyn * C_int`` for this scale."""
        return self.dynamic_distortion * self.interface_distortion


def transported_update(
    source: RGInterface, target: RGInterface, x: Fraction, q: Fraction
) -> Fraction:
    """Apply an exactly ``q``-contractive map after chart transport.

    The stable coordinate is ``T_I(x) = I.chart_scale * x``.  The returned
    target-chart value is chosen so ``T_J(R(x)) = q T_I(x)``.
    """
    return q * source.chart_scale * x / target.chart_scale


def transported_contraction_ratio(
    source: RGInterface,
    target: RGInterface,
    x: Fraction,
    y: Fraction,
    q: Fraction,
) -> Fraction:
    """Evaluate the adjacent-scale contraction after common-interface transport."""
    if x == y:
        raise ValueError("the contraction ratio requires distinct states")
    rx = transported_update(source, target, x, q)
    ry = transported_update(source, target, y, q)
    numerator = abs(target.chart_scale * rx - target.chart_scale * ry)
    denominator = abs(source.chart_scale * x - source.chart_scale * y)
    return numerator / denominator


def demo_log(length: int) -> tuple[RGLogEntry, ...]:
    """Produce a finite stable-tail log with summable distortion excesses."""
    if length < 1:
        raise ValueError("length must be positive")
    entries: list[RGLogEntry] = []
    for offset in range(length):
        scale = offset + 2
        interface = tail_interface(scale)
        dynamic_excess = Fraction(1, 2 ** (scale + 2))
        interface_excess = Fraction(1, 2 ** (scale + 1))
        state = RGState(
            interface_name=interface.name,
            effective_theory=(Fraction(1, scale + 1),),
            observable=Fraction(1, scale + 2),
            certificate_count=scale,
            cumulative_dynamic_error=sum(
                (Fraction(1, 2 ** (j + 2)) for j in range(2, scale + 1)),
                Fraction(0),
            ),
            cumulative_interface_error=sum(
                (Fraction(1, 2 ** (j + 1)) for j in range(2, scale + 1)),
                Fraction(0),
            ),
        )
        entries.append(
            RGLogEntry(
                interface=interface,
                state=state,
                operator_name=f"transported_R_{scale}",
                contraction_q=Fraction(3, 4),
                dynamic_distortion=Fraction(1) + dynamic_excess,
                interface_distortion=Fraction(1) + interface_excess,
                observable_error=Fraction(1, 2 ** (scale + 2)),
                certificate_status="verified",
            )
        )
    return tuple(entries)

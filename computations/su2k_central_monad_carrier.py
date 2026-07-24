"""Finite SU(2)_k central-induction carrier and RG coherence audit.

This module implements the semisimple, decategorified pilot suggested by the
central Hopf monad/comonad formulation of Davydov--Yetter cohomology.

For the modular fusion category SU(2)_k, the Drinfeld center is equivalent at
the level of simple-object multiplicities to ``C x C^rev``.  Its forgetful
functor and left adjoint are therefore represented by

    U(a, b) = a tensor b,
    [F(V) : (a, b)] = dim Hom(a tensor b, V).

The central monad on physical objects is ``Z = U F`` and the associated
comonad on central objects is ``G = F U``.  Integer multiplicity vectors let
us test object-level adjunction and module identities exactly at every finite
level.

They do *not* contain bases or linear maps inside multiplicity spaces.  The
module pins an exact two-dimensional counit ambiguity showing where a full
F/R-symbol realization is required.  No positivity or Ocneanu-rigidity claim
is inferred from the Grothendieck-level data.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Mapping, TypeAlias

from computations.exact_haar_network import casimir4, dimension


FusionVector: TypeAlias = dict[int, int]
CentralSimple: TypeAlias = tuple[int, int]
CentralVector: TypeAlias = dict[CentralSimple, int]


def _clean_fusion_vector(vector: Mapping[int, int]) -> FusionVector:
    clean: FusionVector = {}
    for label, multiplicity in vector.items():
        if label < 0:
            raise ValueError("doubled labels must be nonnegative")
        if multiplicity < 0:
            raise ValueError("fusion multiplicities must be nonnegative")
        if multiplicity:
            clean[label] = clean.get(label, 0) + multiplicity
    return clean


def _clean_central_vector(
    vector: Mapping[CentralSimple, int],
) -> CentralVector:
    clean: CentralVector = {}
    for (left, right), multiplicity in vector.items():
        if left < 0 or right < 0:
            raise ValueError("central labels must be nonnegative")
        if multiplicity < 0:
            raise ValueError("central multiplicities must be nonnegative")
        if multiplicity:
            key = (left, right)
            clean[key] = clean.get(key, 0) + multiplicity
    return clean


def su2k_fusion_labels(level: int, left: int, right: int) -> tuple[int, ...]:
    """Multiplicity-free SU(2)_k fusion outputs in doubled labels."""

    if level < 0:
        raise ValueError("SU(2)_k level must be nonnegative")
    if left not in range(level + 1) or right not in range(level + 1):
        raise ValueError("labels must lie between zero and the level")
    upper = min(left + right, 2 * level - left - right)
    return tuple(range(abs(left - right), upper + 1, 2))


def su2k_tensor(
    level: int,
    left: Mapping[int, int],
    right: Mapping[int, int],
) -> FusionVector:
    """Tensor two finite fusion-ring vectors exactly."""

    clean_left = _clean_fusion_vector(left)
    clean_right = _clean_fusion_vector(right)
    if any(label > level for label in clean_left | clean_right):
        raise ValueError("fusion vector leaves SU(2)_k")
    out: FusionVector = {}
    for left_label, left_multiplicity in clean_left.items():
        for right_label, right_multiplicity in clean_right.items():
            for output in su2k_fusion_labels(
                level, left_label, right_label
            ):
                out[output] = out.get(output, 0) + (
                    left_multiplicity * right_multiplicity
                )
    return out


def su2k_word_channels(level: int, labels: tuple[int, ...]) -> FusionVector:
    """Complete parenthesization-independent fusion ledger of a word."""

    packet: FusionVector = {0: 1}
    for label in labels:
        packet = su2k_tensor(level, packet, {label: 1})
    return packet


def central_induction(
    level: int,
    physical: Mapping[int, int],
) -> CentralVector:
    """Object-level left adjoint ``F`` of the center forgetful functor."""

    clean = _clean_fusion_vector(physical)
    if any(label > level for label in clean):
        raise ValueError("physical vector leaves SU(2)_k")
    out: CentralVector = {}
    for left in range(level + 1):
        for right in range(level + 1):
            multiplicity = sum(
                physical_multiplicity
                for output, physical_multiplicity in clean.items()
                if output in su2k_fusion_labels(level, left, right)
            )
            if multiplicity:
                out[left, right] = multiplicity
    return out


def forget_central(
    level: int,
    central: Mapping[CentralSimple, int],
) -> FusionVector:
    """Object-level forgetful functor ``U(a,b)=a tensor b``."""

    clean = _clean_central_vector(central)
    if any(left > level or right > level for left, right in clean):
        raise ValueError("central vector leaves SU(2)_k")
    out: FusionVector = {}
    for (left, right), multiplicity in clean.items():
        for output in su2k_fusion_labels(level, left, right):
            out[output] = out.get(output, 0) + multiplicity
    return out


def central_monad(
    level: int,
    physical: Mapping[int, int],
) -> FusionVector:
    """The object multiplicities of ``Z = U F``."""

    return forget_central(level, central_induction(level, physical))


def central_comonad(
    level: int,
    central: Mapping[CentralSimple, int],
) -> CentralVector:
    """The object multiplicities of ``G = F U``."""

    return central_induction(level, forget_central(level, central))


def hom_dimension_physical(
    source: Mapping[int, int],
    target: Mapping[int, int],
) -> int:
    """Semisimple Hom dimension between physical multiplicity vectors."""

    clean_source = _clean_fusion_vector(source)
    clean_target = _clean_fusion_vector(target)
    return sum(
        source_multiplicity * clean_target.get(label, 0)
        for label, source_multiplicity in clean_source.items()
    )


def hom_dimension_central(
    source: Mapping[CentralSimple, int],
    target: Mapping[CentralSimple, int],
) -> int:
    """Semisimple Hom dimension between central multiplicity vectors."""

    clean_source = _clean_central_vector(source)
    clean_target = _clean_central_vector(target)
    return sum(
        source_multiplicity * clean_target.get(simple, 0)
        for simple, source_multiplicity in clean_source.items()
    )


def degree_zero_adjunction_holds(
    level: int,
    physical: Mapping[int, int],
    central: Mapping[CentralSimple, int],
) -> bool:
    """Check ``Hom_Z(F(V),M) = Hom_C(V,U(M))`` exactly."""

    return hom_dimension_central(
        central_induction(level, physical), central
    ) == hom_dimension_physical(
        physical, forget_central(level, central)
    )


def central_left_action(
    level: int,
    label: int,
    central: Mapping[CentralSimple, int],
) -> CentralVector:
    """Act on the left factor of ``C x C^rev`` by one simple label."""

    if label not in range(level + 1):
        raise ValueError("action label leaves SU(2)_k")
    clean = _clean_central_vector(central)
    out: CentralVector = {}
    for (left, right), multiplicity in clean.items():
        for output in su2k_fusion_labels(level, label, left):
            key = (output, right)
            out[key] = out.get(key, 0) + multiplicity
    return out


def pure_fusion_transport_is_module_morphism(
    level: int,
    label: int,
    physical: Mapping[int, int],
) -> bool:
    """Check the object-level module naturality of central induction."""

    acted_physical = su2k_tensor(level, {label: 1}, physical)
    return central_induction(
        level, acted_physical
    ) == central_left_action(
        level, label, central_induction(level, physical)
    )


def heat_weight_vector(
    physical: Mapping[int, int],
    heat_coordinate: Fraction,
) -> dict[int, Fraction]:
    """Apply the physical heat coefficient to every retained output."""

    if heat_coordinate < 0:
        raise ValueError("heat coordinate must be nonnegative")
    clean = _clean_fusion_vector(physical)
    return {
        label: Fraction(multiplicity * dimension(label))
        * heat_coordinate ** casimir4(label)
        for label, multiplicity in clean.items()
    }


def heat_transport_module_defect(
    level: int,
    action_label: int,
    physical_label: int,
    heat_coordinate: Fraction,
) -> tuple[dict[int, Fraction], dict[int, Fraction]]:
    """Return both sides of the heat-weighted module-naturality test.

    The first vector weights after fusion.  The second weights the input and
    then fuses.  Their inequality is the precise obstruction to treating the
    physical heat-weighted block map as an ordinary module morphism.
    """

    if action_label not in range(level + 1):
        raise ValueError("action label leaves SU(2)_k")
    if physical_label not in range(level + 1):
        raise ValueError("physical label leaves SU(2)_k")
    fused = su2k_tensor(
        level, {action_label: 1}, {physical_label: 1}
    )
    weight_after = heat_weight_vector(fused, heat_coordinate)
    input_weight = heat_weight_vector(
        {physical_label: 1}, heat_coordinate
    )[physical_label]
    fuse_after_weight: dict[int, Fraction] = {
        output: input_weight
        for output in su2k_fusion_labels(
            level, action_label, physical_label
        )
    }
    return weight_after, fuse_after_weight


def comonad_counit_diagonal_multiplicity(
    level: int, simple: CentralSimple
) -> int:
    """Multiplicity of ``simple`` inside ``G(simple)``.

    A value greater than one means that object multiplicities do not specify
    the counit map from that multiplicity space back to the simple object.
    """

    central = {simple: 1}
    return central_comonad(level, central).get(simple, 0)


def central_vacuum_basis(level: int) -> CentralVector:
    """The central induction of the physical tensor unit."""

    return central_induction(level, {0: 1})


def fusion_word_is_classically_stable(
    level: int, labels: tuple[int, ...]
) -> bool:
    """Check the sufficient stable range ``sum(labels) <= level``.

    Inside this range no reflected affine-wall channel can occur, so the
    SU(2)_k ledger agrees with the ordinary SU(2) character-product ledger.
    """

    if any(label < 0 for label in labels):
        raise ValueError("doubled labels must be nonnegative")
    if sum(labels) > level:
        return False

    ordinary: FusionVector = {0: 1}
    for label in labels:
        following: FusionVector = {}
        for intermediate, multiplicity in ordinary.items():
            for output in range(
                abs(intermediate - label),
                intermediate + label + 1,
                2,
            ):
                following[output] = (
                    following.get(output, 0) + multiplicity
                )
        ordinary = following
    return su2k_word_channels(level, labels) == ordinary


@dataclass(frozen=True)
class CentralMonadCampaignAudit:
    """Finite exact verdicts separating stable and finite-only content."""

    level: int
    ledger: FusionVector
    central_basis: CentralVector
    degree_zero_adjunction: bool
    pure_transport_module_morphism: bool
    heat_transport_module_morphism: bool
    counit_diagonal_multiplicity: int
    vacuum_basis_rank: int
    stable_fusion_ledger: bool

    def validates(self) -> bool:
        return (
            self.level >= 3
            and bool(self.ledger)
            and bool(self.central_basis)
            and self.degree_zero_adjunction
            and self.pure_transport_module_morphism
            and not self.heat_transport_module_morphism
            and self.counit_diagonal_multiplicity == 2
            and self.vacuum_basis_rank == self.level + 1
            and self.stable_fusion_ledger
        )


def central_monad_campaign_audit(
    level: int,
) -> CentralMonadCampaignAudit:
    """Run the campaign on the first multiplicity-bearing fusion word."""

    if level < 3:
        raise ValueError("the pinned word (1,1,1) requires level at least three")
    labels = (1, 1, 1)
    ledger = su2k_word_channels(level, labels)
    central_basis = central_induction(level, ledger)
    probe_central: CentralVector = {(1, 1): 1, (0, 2): 2}
    heat_left, heat_right = heat_transport_module_defect(
        level, 1, 0, Fraction(1, 2)
    )
    audit = CentralMonadCampaignAudit(
        level=level,
        ledger=ledger,
        central_basis=central_basis,
        degree_zero_adjunction=degree_zero_adjunction_holds(
            level, ledger, probe_central
        ),
        pure_transport_module_morphism=(
            pure_fusion_transport_is_module_morphism(
                level, 1, {1: 1, 2: 2}
            )
        ),
        heat_transport_module_morphism=heat_left == heat_right,
        counit_diagonal_multiplicity=(
            comonad_counit_diagonal_multiplicity(level, (1, 1))
        ),
        vacuum_basis_rank=len(central_vacuum_basis(level)),
        stable_fusion_ledger=fusion_word_is_classically_stable(
            level, labels
        ),
    )
    if not audit.validates():
        raise AssertionError("the SU(2)_k central-monad campaign drifted")
    return audit

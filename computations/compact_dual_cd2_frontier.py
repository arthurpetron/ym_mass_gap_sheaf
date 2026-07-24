"""Executable CD-2 frontier after corrected-slab normalization.

The repository now contains all finite algebra surrounding a physical block:
normalized corrected-slab laws, single-scale reflection positivity, a local
source-dependent character/fusion kernel, a closed cutoff-one cube projector,
reflection-compatible composition for link-separated cubes, automatic
zero-mass remainder cancellation, and the universal probability bound
``||R||_1 <= 2``.

The first missing object is not another normalization identity.  It is the
globally coupled kernel for genuinely overlapping blocks with shared fine
links, followed by its all-cutoff identification with the physical
corrected-slab pushforward.  The vanishing quadratic norm belongs to CD-3.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction


class CD2Subgate(Enum):
    """Ordered construction gates inside the physical CD-2 block."""

    NORMALIZED_SLAB_LAWS = "normalized corrected-slab physical laws"
    LOCAL_FUSION_KERNEL = "source-dependent local character/fusion kernel"
    CLOSED_COMPONENT = "closed projected cube component"
    SEPARATED_COMPOSITION = "link-separated physical composition"
    OVERLAPPING_LINK_ASSEMBLY = "genuinely overlapping shared-link assembly"
    ALL_CUTOFF_GLOBAL_KERNEL = "all-cutoff whole-slab kernel"
    PHYSICAL_PUSHFORWARD = "physical Gibbs pushforward identification"


CD2_LEAN_THEOREMS = (
    "CompactDualSlabPhysicalData.SlabPhysicalData.normalizedMass_total",
    "CompactDualSlabPhysicalData.SlabPhysicalData."
    "fullReflectionQuadratic_nonnegative",
    "Z4DyadicSlabCharacterFusionConditionalKernel."
    "packetPairChannelConditionalKernel_source_dependent",
    "Z4DyadicSlabCharacterFusionConditionalKernel."
    "dyadicSlabPairChannelConditionalKernel_reflection_equivariant",
    "Z4DyadicSlabCubeCoupledConditionalKernel."
    "cubeCoupledConditionalKernel_row_normalized",
    "Z4DyadicSlabCubeFineSupportProjectedKernel."
    "closedCubeFineSlotKernel_row_normalized",
    "Z4DyadicSlabCubeKernelProductComposition."
    "bridgedProjectedTwoCubeRawProduct_eqv_unionProductionSummand",
    "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
    "remainder_total_eqv_zero",
    "CompactDualFiniteBlockRemainder.SlabScalePair.FiniteSlabKernel."
    "remainderL1_le_two",
)


@dataclass(frozen=True)
class CD2Frontier:
    """Fail-closed ledger for the physical block construction."""

    normalized_slab_laws: bool
    local_fusion_kernel: bool
    closed_component: bool
    separated_composition: bool
    overlapping_link_assembly: bool
    all_cutoff_global_kernel: bool
    physical_pushforward: bool
    zero_mass_remainder_derived: bool
    universal_l1_cap: Fraction | None

    def gate_results(self) -> tuple[tuple[CD2Subgate, bool], ...]:
        """Return every construction subgate in dependency order."""

        return (
            (CD2Subgate.NORMALIZED_SLAB_LAWS, self.normalized_slab_laws),
            (CD2Subgate.LOCAL_FUSION_KERNEL, self.local_fusion_kernel),
            (CD2Subgate.CLOSED_COMPONENT, self.closed_component),
            (CD2Subgate.SEPARATED_COMPOSITION, self.separated_composition),
            (
                CD2Subgate.OVERLAPPING_LINK_ASSEMBLY,
                self.overlapping_link_assembly,
            ),
            (
                CD2Subgate.ALL_CUTOFF_GLOBAL_KERNEL,
                self.all_cutoff_global_kernel,
            ),
            (CD2Subgate.PHYSICAL_PUSHFORWARD, self.physical_pushforward),
        )

    def first_open_subgate(self) -> CD2Subgate | None:
        """Return the first physical construction subgate still open."""

        for gate, closed in self.gate_results():
            if not closed:
                return gate
        return None

    def finite_remainder_algebra_closed(self) -> bool:
        """Check the now-derived normalization consequences."""

        return (
            self.normalized_slab_laws
            and self.zero_mass_remainder_derived
            and self.universal_l1_cap == 2
        )

    def physical_cd2_closed(self) -> bool:
        """Require every physical construction subgate."""

        return self.first_open_subgate() is None

    def cd3_smallness_closed(self) -> bool:
        """The universal cap two is not a vanishing RG defect estimate."""

        return False


def current_cd2_frontier() -> CD2Frontier:
    """Return the exact current frontier without promoting local sectors."""

    return CD2Frontier(
        normalized_slab_laws=True,
        local_fusion_kernel=True,
        closed_component=True,
        separated_composition=True,
        overlapping_link_assembly=False,
        all_cutoff_global_kernel=False,
        physical_pushforward=False,
        zero_mass_remainder_derived=True,
        universal_l1_cap=Fraction(2),
    )

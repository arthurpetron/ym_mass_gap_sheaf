/-
# Dependent recoupling rows for disconnected paired support

Every disconnected paired-support source determines two switched physical
fields.  Above that fixed pair lies one complete whole-slab SU(2) recoupling
matrix, and the source's switched auxiliary assignments select one literal
row.  This module exposes the matrix targets as the source-dependent choice
carrier and its selected entries as a normalized stochastic row.

No physical target is reconstructed here.  Realization and column capacity
are the next, separate steps.

Constructive contract: exact finite `Q'` matrices and literal source rows
only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One literal common-matrix row per separated source -/

def SlabObservablePairedSupportSeparatedSource.toContributor
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId
      (slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId source.1)
      (slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId source.1) where
  pair := source.1
  pair_mem := source.pair_mem_fourCell
  disconnected := source.disconnected
  leftPhysical_eq := rfl
  rightPhysical_eq := rfl

/-- The complete whole-slab target carrier over the switched physical pair
selected by one separated source. -/
abbrev SlabObservablePairedSupportRecouplingChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :=
  SlabPhysicalPairRecouplingTargetAssignment D.extent
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)

def slabObservablePairedSupportRecouplingChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :=
  (slabPhysicalPairRecouplingKernel D.extent
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)).targets

def slabObservablePairedSupportRecouplingWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) : Q' :=
  slabObservablePairedSupportContributorColumnWeight
    D rootFaceId targetFaceId
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    htarget choice
    (SlabObservablePairedSupportSeparatedSource.toContributor source)

/-! ## 2. Exact stochasticity -/

theorem slabObservablePairedSupportRecouplingWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (0 : Q') ≤ slabObservablePairedSupportRecouplingWeight
      D rootFaceId targetFaceId htarget source choice :=
  slabObservablePairedSupportContributorColumnWeight_nonnegative
    D rootFaceId targetFaceId
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    htarget choice
    (SlabObservablePairedSupportSeparatedSource.toContributor source)

/-- Every separated paired-support source carries one exact normalized row
of its common physical-pair product matrix. -/
theorem slabObservablePairedSupportRecouplingWeight_row_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    listQSum
        (slabObservablePairedSupportRecouplingWeight
          D rootFaceId targetFaceId htarget source)
        (slabObservablePairedSupportRecouplingChoices
          D rootFaceId targetFaceId source) ≈ 1 := by
  exact slabPhysicalPairRecouplingProductionSource_row_normalized
    D.cutoff D.extent
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment_mem htarget)
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment_mem htarget)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow.SlabObservablePairedSupportSeparatedSource.toContributor
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow.slabObservablePairedSupportRecouplingWeight_nonnegative
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow.slabObservablePairedSupportRecouplingWeight_row_normalized

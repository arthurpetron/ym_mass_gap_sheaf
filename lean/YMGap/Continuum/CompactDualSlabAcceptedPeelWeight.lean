/-
# Arbitrary-coupling weight of one accepted canonical component peel

An accepted expanded source at a positive physical face has a canonical
rooted component and an accepted lowered target.  The existing high-spin
split pays the exterior copies at the strict anchor rate and records every
remaining finite-core copy at the explicit coarse rate two.  This module
specializes that comparison to the accepted-source API used by the canonical
peeling recursion.

This is a one-step theorem.  Iterating the displayed costs to the accepted
vacuum and summing inverse fibers are subsequent modules.

Constructive contract: specialization of explicit accepted witnesses and
finite rational inequalities only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedPeel

namespace YMGap.Continuum.CompactDualSlabAcceptedPeelWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Exact step-cost counters -/

/-- Number of component copies paid by the strict high-spin exterior rate. -/
def acceptedExpandedSourceExteriorPeelSizeAt
    (D : SlabPhysicalData) (threshold faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) : Nat :=
  (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
    (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)
    threshold).length

/-- Number of component copies left for the explicit finite-core rate two. -/
def acceptedExpandedSourceCoreResidualSizeAt
    (D : SlabPhysicalData) (threshold faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) : Nat :=
  (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
    (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)
    threshold).length

/-! ## 2. Accepted one-step comparison -/

/-- One actual accepted canonical component peel has the sharp exterior rate
and the fully explicit finite-core residual rate. -/
theorem slabExpandedFineEntryWeight_lowerAt_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    slabExpandedFineEntryWeight D entry <=
      (anchorFaceCoefficient ^
          acceptedExpandedSourceExteriorPeelSizeAt D
            (anchorPaidExteriorThreshold D.coupling)
            faceId hface entry hpositive *
        (Q'.ofNat 2) ^
          acceptedExpandedSourceCoreResidualSizeAt D
            (anchorPaidExteriorThreshold D.coupling)
            faceId hface entry hpositive) *
        slabExpandedFineEntryWeight D
          (acceptedExpandedSourceLowerAt
            D faceId hface entry hpositive) := by
  have hphysical := acceptedExpandedSourcePhysical_mem entry
  have hbounded : SlabFaceLabellingBounded
      D.cutoff D.extent entry.1.1 := by
    intro selectedFaceId hselected
    exact Nat.le_of_lt_succ
      ((boundedEdgeLabellings_sound D.cutoff D.faceEdges
        entry.1.1 hphysical).1 selectedFaceId
          (by simpa only [SlabPhysicalData.faceEdges] using hselected))
  have hstep := expandedFiberWeight_coreCompleted_le
    hw0 hw1 D.cutoff D.half
      (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)
      hbounded
  simpa only [slabExpandedFineEntryWeight, slabExpandedFineSourceWeight,
    acceptedExpandedSourceExteriorPeelSizeAt,
    acceptedExpandedSourceCoreResidualSizeAt,
    acceptedExpandedSourceLowerAt] using hstep

#print axioms acceptedExpandedSourceExteriorPeelSizeAt
#print axioms acceptedExpandedSourceCoreResidualSizeAt
#print axioms slabExpandedFineEntryWeight_lowerAt_le

end YMGap.Continuum.CompactDualSlabAcceptedPeelWeight

/-
# The normalized crossed recoupling product on the actual slab-link list

The paired-face component supplies one common face mask and, at every actual
boundary-complete slab link, two accepted source auxiliaries together with
the partner-closed local selections needed by the cross-replica switch.  The
all-valence compiler supplies a normalized recoupling row at each such link.

This module joins those two constructions on the literal production link
enumeration.  Each local datum is indexed by its computed incident-face
degree, so the dependent product retains the correct valence-specific target
type at every position.

Constructive contract: literal production lists and witnesses, exact `Q'`,
no `Classical`, no choice, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
import YMGap.Continuum.FiniteNormalizedQKernelProduct

namespace YMGap.Continuum.SU2SlabGlobalCrossedSchurProduct

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteNormalizedQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The production switch datum at one actual link -/

def slabObservablePairCrossedSwitchDataAtLinkWithMask
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent})
    (mask : Nat → Bool)
    (leftConstant : ∀ copy,
      (slabObservablePairLeftSelectionAtLink
        D rootFaceId targetFaceId htarget pair hpair linked).selected copy =
          mask copy.faceId)
    (rightConstant : ∀ copy,
      (slabObservablePairRightSelectionAtLink
        D rootFaceId targetFaceId htarget pair hpair linked).selected copy =
          mask copy.faceId) :
    CrossedSlabSwitchData D.cutoff D.extent
      (slabIncidentPlaqIds D.extent linked.1).length where
  physical :=
    { leftPhysical := pair.1.1.1
      rightPhysical := pair.2.1.1
      mask := mask }
  link := linked.1
  leftAuxiliary := slabFusionWitnessAssignmentAt linked.1 pair.1.1.2
  rightAuxiliary := slabFusionWitnessAssignmentAt linked.1 pair.2.1.2
  leftAuxiliary_mem := slabFusionWitnessAssignmentAt_mem_local
    D.cutoff D.extent pair.1.1.1
    (boundaryCompleteSlabLinks D.extent) pair.1.1.2
    pair.1.assignment_mem linked.1 linked.2
  rightAuxiliary_mem := slabFusionWitnessAssignmentAt_mem_local
    D.cutoff D.extent pair.2.1.1
    (boundaryCompleteSlabLinks D.extent) pair.2.1.2
    (slabExpandedFineSourceEntryAssignment_mem pair.2)
    linked.1 linked.2
  leftBounded := SlabObservablePositiveSourceEntry.physical_bounded pair.1
  rightBounded := SlabExpandedFineSourceEntry.physical_bounded pair.2
  leftSelection := slabObservablePairLeftSelectionAtLink
    D rootFaceId targetFaceId htarget pair hpair linked
  rightSelection := slabObservablePairRightSelectionAtLink
    D rootFaceId targetFaceId htarget pair hpair linked
  leftConstant := leftConstant
  rightConstant := rightConstant
  degree_eq := rfl

theorem slabObservablePairCrossedSwitchDataAtLinkWithMask_leftPhysical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent})
    (mask : Nat → Bool) (leftConstant rightConstant) :
    higherCrossedLeftPhysical
        (slabObservablePairCrossedSwitchDataAtLinkWithMask
          D rootFaceId targetFaceId htarget pair hpair linked mask
            leftConstant rightConstant) =
      twoReplicaFaceSwapLeft mask pair.1.1.1 pair.2.1.1 := rfl

theorem slabObservablePairCrossedSwitchDataAtLinkWithMask_rightPhysical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent})
    (mask : Nat → Bool) (leftConstant rightConstant) :
    higherCrossedRightPhysical
        (slabObservablePairCrossedSwitchDataAtLinkWithMask
          D rootFaceId targetFaceId htarget pair hpair linked mask
            leftConstant rightConstant) =
      twoReplicaFaceSwapRight mask pair.1.1.1 pair.2.1.1 := rfl

/-- The paired-face construction provides every field of the all-valence
local compiler at an actual member of the slab-link enumeration. -/
def slabObservablePairCrossedSwitchDataAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    CrossedSlabSwitchData D.cutoff D.extent
      (slabIncidentPlaqIds D.extent linked.1).length :=
  slabObservablePairCrossedSwitchDataAtLinkWithMask
    D rootFaceId targetFaceId htarget pair hpair linked
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    (by
      intro copy
      simp [slabObservablePairLeftSelectionAtLink])
    (by
      intro copy
      simp [slabObservablePairRightSelectionAtLink])

/-! ## 2. Map the local compiler over the literal slab enumeration -/

/-- The exact valence-sensitive local row at one attached production link. -/
def slabObservablePairCrossedKernelAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    FiniteNormalizedQKernel :=
  crossedLinkRecouplingKernel
    (slabIncidentPlaqIds D.extent linked.1).length
    (slabObservablePairCrossedSwitchDataAtLink
      D rootFaceId targetFaceId htarget pair hpair linked)

/-- The local analytic rows in the exact production link order. -/
def slabObservablePairCrossedKernels
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) : List FiniteNormalizedQKernel :=
  (boundaryCompleteSlabLinks D.extent).attach.map fun linked =>
    slabObservablePairCrossedKernelAtLink
      D rootFaceId targetFaceId htarget pair hpair linked

abbrev SlabObservablePairCrossedRecouplingAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :=
  FiniteKernelAssignment
    (slabObservablePairCrossedKernels
      D rootFaceId targetFaceId htarget pair hpair)

/-! ## 3. One global normalized analytic row -/

/-- **The exact product recoupling law over every actual slab link has total
mass one.** -/
theorem slabObservablePairCrossedKernelProduct_row_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    listQSum finiteKernelAssignmentWeight
        (finiteKernelAssignments
          (slabObservablePairCrossedKernels
            D rootFaceId targetFaceId htarget pair hpair)) ≈ 1 :=
  finiteKernelProduct_row_normalized
    (slabObservablePairCrossedKernels
      D rootFaceId targetFaceId htarget pair hpair)

theorem slabObservablePairCrossedKernelProduct_weight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (assignment : SlabObservablePairCrossedRecouplingAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    (0 : Q') ≤ finiteKernelAssignmentWeight assignment :=
  finiteKernelAssignmentWeight_nonnegative assignment

#print axioms slabObservablePairCrossedSwitchDataAtLink
#print axioms slabObservablePairCrossedKernelAtLink
#print axioms slabObservablePairCrossedKernels
#print axioms slabObservablePairCrossedKernelProduct_row_normalized
#print axioms slabObservablePairCrossedKernelProduct_weight_nonnegative

end YMGap.Continuum.SU2SlabGlobalCrossedSchurProduct

/-
# The complete crossed recoupling matrix on the actual slab-link list

Every production slab link now carries a complete crossed bistochastic
recoupling matrix at its actual degree.  The source and target carrier types
vary with that degree.  This module maps the all-valence matrix package over
the literal boundary-complete link enumeration and applies the heterogeneous
product theorem.

The result is one finite matrix with exact row and column mass one on the
full dependent source and target carriers.  It is still pure SU(2)
recoupling transport, not a Gibbs or Osterwalder--Schrader kernel.

Constructive contract: literal production lists, exact `Q'`, no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabGlobalCrossedSchurProduct
import YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel

namespace YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabGlobalCrossedSchurProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Complete matrix packages in production link order -/

def slabObservablePairCrossedPointedBistochasticPackageAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    PointedFiniteBistochasticQKernelPackage :=
  crossedLinkPointedBistochasticKernelPackage
    (slabObservablePairCrossedSwitchDataAtLink
      D rootFaceId targetFaceId htarget pair hpair linked)

def slabObservablePairCrossedBistochasticPackageAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    FiniteBistochasticQKernelPackage :=
  (slabObservablePairCrossedPointedBistochasticPackageAtLink
    D rootFaceId targetFaceId htarget pair hpair linked).package

def slabObservablePairCrossedPointedBistochasticPackages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    List PointedFiniteBistochasticQKernelPackage :=
  (boundaryCompleteSlabLinks D.extent).attach.map fun linked =>
    slabObservablePairCrossedPointedBistochasticPackageAtLink
      D rootFaceId targetFaceId htarget pair hpair linked

/-- Complete local matrices in the literal slab-link enumeration. -/
def slabObservablePairCrossedBistochasticPackages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    List FiniteBistochasticQKernelPackage :=
  finiteBistochasticPackagesOfPointed
    (slabObservablePairCrossedPointedBistochasticPackages
      D rootFaceId targetFaceId htarget pair hpair)

abbrev SlabObservablePairCrossedBistochasticSourceAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :=
  FiniteBistochasticSourceAssignment
    (slabObservablePairCrossedBistochasticPackages
      D rootFaceId targetFaceId htarget pair hpair)

abbrev SlabObservablePairCrossedBistochasticTargetAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :=
  FiniteBistochasticTargetAssignment
    (slabObservablePairCrossedBistochasticPackages
      D rootFaceId targetFaceId htarget pair hpair)

/-! ## 2. One complete whole-slab matrix -/

def slabObservablePairCrossedBistochasticKernel
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    FiniteBistochasticQKernel
      (SlabObservablePairCrossedBistochasticSourceAssignment
        D rootFaceId targetFaceId htarget pair hpair)
      (SlabObservablePairCrossedBistochasticTargetAssignment
        D rootFaceId targetFaceId htarget pair hpair) :=
  finiteBistochasticKernelProduct
    (slabObservablePairCrossedBistochasticPackages
      D rootFaceId targetFaceId htarget pair hpair)

/-- The complete dependent source obtained from the actual production fusion
witness at every slab link. -/
def slabObservablePairCrossedBistochasticProductionSource
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    SlabObservablePairCrossedBistochasticSourceAssignment
      D rootFaceId targetFaceId htarget pair hpair :=
  pointedFiniteBistochasticSourceAssignment
    (slabObservablePairCrossedPointedBistochasticPackages
      D rootFaceId targetFaceId htarget pair hpair)

theorem slabObservablePairCrossedBistochasticKernel_weight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (source : SlabObservablePairCrossedBistochasticSourceAssignment
      D rootFaceId targetFaceId htarget pair hpair)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    (0 : Q') ≤
      (slabObservablePairCrossedBistochasticKernel
        D rootFaceId targetFaceId htarget pair hpair).weight source target :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget pair hpair).weight_nonnegative
      source target

theorem slabObservablePairCrossedBistochasticKernel_row_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (source : SlabObservablePairCrossedBistochasticSourceAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    listQSum
        ((slabObservablePairCrossedBistochasticKernel
          D rootFaceId targetFaceId htarget pair hpair).weight source)
        (slabObservablePairCrossedBistochasticKernel
          D rootFaceId targetFaceId htarget pair hpair).targets ≈ 1 :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget pair hpair).row_normalized source

theorem slabObservablePairCrossedBistochasticProductionSource_row_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    listQSum
        ((slabObservablePairCrossedBistochasticKernel
          D rootFaceId targetFaceId htarget pair hpair).weight
          (slabObservablePairCrossedBistochasticProductionSource
            D rootFaceId targetFaceId htarget pair hpair))
        (slabObservablePairCrossedBistochasticKernel
          D rootFaceId targetFaceId htarget pair hpair).targets ≈ 1 :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget pair hpair).row_normalized
      (slabObservablePairCrossedBistochasticProductionSource
        D rootFaceId targetFaceId htarget pair hpair)

theorem slabObservablePairCrossedBistochasticKernel_column_normalized
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (target : SlabObservablePairCrossedBistochasticTargetAssignment
      D rootFaceId targetFaceId htarget pair hpair) :
    listQSum
        (fun source =>
          (slabObservablePairCrossedBistochasticKernel
            D rootFaceId targetFaceId htarget pair hpair).weight
              source target)
        (slabObservablePairCrossedBistochasticKernel
          D rootFaceId targetFaceId htarget pair hpair).sources ≈ 1 :=
  (slabObservablePairCrossedBistochasticKernel
    D rootFaceId targetFaceId htarget pair hpair).column_normalized target

end YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct

#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticPackageAtLink
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedPointedBistochasticPackages
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticPackages
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticKernel
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticProductionSource
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticKernel_weight_nonnegative
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticKernel_row_normalized
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticProductionSource_row_normalized
#print axioms YMGap.Continuum.SU2SlabGlobalCrossedSchurBistochasticProduct.slabObservablePairCrossedBistochasticKernel_column_normalized

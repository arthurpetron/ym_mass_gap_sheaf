/-
# Column no-overload for one paired-support physical fiber

Contributors with one fixed switched physical output inject into enumerated
rows of one complete whole-slab bistochastic matrix.  Constructive equality
on that heterogeneous source carrier lets the finite weighted-injection
theorem compare any duplicate-free contributor list with one literal matrix
column.  Exact column normalization then gives total mass at most one.

This is the finite SU(2) no-overload argument.  It does not yet enumerate the
physical fibers of the production four-cell or compare recoupling weights
with Gibbs/OS weights.

Constructive contract: exact finite lists and `Q'` only; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The selected entry in one common column -/

def slabObservablePairedSupportContributorColumnWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) : Q' :=
  (slabPhysicalPairRecouplingKernel
    D.extent leftPhysical rightPhysical).weight
    (slabObservablePairedSupportContributorProductionRow
      D rootFaceId targetFaceId leftPhysical rightPhysical
      htarget contributor)
    target

theorem slabObservablePairedSupportContributorColumnWeight_nonnegative
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (contributor : SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical) :
    (0 : Q') ≤
      slabObservablePairedSupportContributorColumnWeight
        D rootFaceId targetFaceId leftPhysical rightPhysical
        htarget target contributor :=
  (slabPhysicalPairRecouplingKernel
    D.extent leftPhysical rightPhysical).weight_nonnegative _ _

/-! ## 2. Injective row accounting -/

/-- Any duplicate-free list of contributors in one fixed physical fiber has
total weight at a fixed target column bounded by that complete column. -/
theorem slabObservablePairedSupportContributorColumnWeight_sum_le_column
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (contributors : List (SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical))
    (hcontributors : contributors.Nodup) :
    listQSum
        (slabObservablePairedSupportContributorColumnWeight
          D rootFaceId targetFaceId leftPhysical rightPhysical
          htarget target)
        contributors ≤
      listQSum
        (fun source =>
          (slabPhysicalPairRecouplingKernel
            D.extent leftPhysical rightPhysical).weight source target)
        (slabPhysicalPairRecouplingKernel
          D.extent leftPhysical rightPhysical).sources := by
  letI : DecidableEq
      (SlabPhysicalPairRecouplingSourceAssignment
        D.extent leftPhysical rightPhysical) :=
    slabPhysicalPairRecouplingSourceAssignmentDecidableEq
      D.extent leftPhysical rightPhysical
  apply listQSum_le_of_injective
    contributors
    (slabPhysicalPairRecouplingKernel
      D.extent leftPhysical rightPhysical).sources
    (slabObservablePairedSupportContributorColumnWeight
      D rootFaceId targetFaceId leftPhysical rightPhysical
      htarget target)
    (fun source =>
      (slabPhysicalPairRecouplingKernel
        D.extent leftPhysical rightPhysical).weight source target)
    (slabObservablePairedSupportContributorProductionRow
      D rootFaceId targetFaceId leftPhysical rightPhysical htarget)
    hcontributors
  · intro contributor _
    exact slabObservablePairedSupportContributorProductionRow_mem
      D rootFaceId targetFaceId leftPhysical rightPhysical
      htarget contributor
  · intro left _ right _ heq
    exact slabObservablePairedSupportContributorProductionRow_injective
      D rootFaceId targetFaceId leftPhysical rightPhysical
      htarget left right heq
  · intro contributor _
    exact Q'.le_refl' _
  · intro source _
    exact (slabPhysicalPairRecouplingKernel
      D.extent leftPhysical rightPhysical).weight_nonnegative source target

/-- Exact column normalization contracts the same contributor mass to one. -/
theorem slabObservablePairedSupportContributorColumnWeight_sum_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (contributors : List (SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical))
    (hcontributors : contributors.Nodup) :
    listQSum
        (slabObservablePairedSupportContributorColumnWeight
          D rootFaceId targetFaceId leftPhysical rightPhysical
          htarget target)
        contributors ≤ 1 := by
  exact Q'.le_trans' _ _ _
    (slabObservablePairedSupportContributorColumnWeight_sum_le_column
      D rootFaceId targetFaceId leftPhysical rightPhysical
      htarget target contributors hcontributors)
    (Q'.le_of_eqv
      (slabPhysicalPairRecouplingKernel_column_normalized
        D.extent leftPhysical rightPhysical target))

end YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload.slabObservablePairedSupportContributorColumnWeight_nonnegative
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload.slabObservablePairedSupportContributorColumnWeight_sum_le_column
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload.slabObservablePairedSupportContributorColumnWeight_sum_le_one

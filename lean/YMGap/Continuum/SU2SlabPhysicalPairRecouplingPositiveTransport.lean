/-
# Positivity is invariant under recoupling-row transport

The whole-slab SU(2) recoupling matrix is indexed by physical face labels and
accepted auxiliary assignments.  Observable packaging can replace those
indices by propositionally equal copies.  This module proves the missing
invariance principle directly: simultaneous equality transport of the two
physical labels and the two source assignments preserves coordinatewise
strict positivity of any displayed target column.  Consequently the exact
finite product entry remains strictly positive.

The theorem changes no matrix, source row, or target column; it only removes
dependent presentation noise.  It is therefore reusable by concrete positive
channel constructions without exposing their complete target tuples.

Constructive contract: equality elimination, proof irrelevance, and finite
positive products only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingPositiveTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Coordinatewise positivity depends only on the represented physical labels
and accepted source assignments, not on propositionally equal dependent
presentations of them. -/
theorem productionSource_coordinatewisePositive_transport
    (K extent : Nat)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (leftAssignment₁ rightAssignment₁ leftAssignment₂ rightAssignment₂ :
      SlabFusionWitnessAssignment)
    (hleftAssignment : leftAssignment₁ = leftAssignment₂)
    (hrightAssignment : rightAssignment₁ = rightAssignment₂)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₂
        (boundaryCompleteSlabLinks extent))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₂
        (boundaryCompleteSlabLinks extent))
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₁ rightPhysical₁)
    (hpositive : FiniteBistochasticCoordinatewisePositive
      (slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₁ rightPhysical₁ leftAssignment₁ rightAssignment₁
        left_mem₁ right_mem₁)
      target) :
    FiniteBistochasticCoordinatewisePositive
      (slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₂ rightPhysical₂ leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂)
      (transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright target) := by
  cases hleft
  cases hright
  cases hleftAssignment
  cases hrightAssignment
  exact hpositive

/-- Contract transported coordinatewise positivity to strict positivity of
the exact heterogeneous product entry. -/
theorem productionSource_productWeight_pos_transport
    (K extent : Nat)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (leftAssignment₁ rightAssignment₁ leftAssignment₂ rightAssignment₂ :
      SlabFusionWitnessAssignment)
    (hleftAssignment : leftAssignment₁ = leftAssignment₂)
    (hrightAssignment : rightAssignment₁ = rightAssignment₂)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₂
        (boundaryCompleteSlabLinks extent))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₂
        (boundaryCompleteSlabLinks extent))
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₁ rightPhysical₁)
    (hpositive : FiniteBistochasticCoordinatewisePositive
      (slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₁ rightPhysical₁ leftAssignment₁ rightAssignment₁
        left_mem₁ right_mem₁)
      target) :
    (0 : Q') < finiteBistochasticProductWeight
      (slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₂ rightPhysical₂ leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂)
      (transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright target) :=
  finiteBistochasticProductWeight_pos_of_coordinatewise _ _
    (productionSource_coordinatewisePositive_transport K extent
      hleft hright leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ hleftAssignment hrightAssignment
      left_mem₁ right_mem₁ left_mem₂ right_mem₂ target hpositive)

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingPositiveTransport

#print axioms
  YMGap.Continuum.SU2SlabPhysicalPairRecouplingPositiveTransport.productionSource_coordinatewisePositive_transport
#print axioms
  YMGap.Continuum.SU2SlabPhysicalPairRecouplingPositiveTransport.productionSource_productWeight_pos_transport

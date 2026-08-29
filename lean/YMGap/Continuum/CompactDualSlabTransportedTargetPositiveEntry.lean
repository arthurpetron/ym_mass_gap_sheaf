/-
# Positive whole-slab entries survive target-package transport

Observable recoupling choices are often stored in a target package indexed by
physical labels propositionally equal to the labels where positivity was
proved.  The lower transport theorem already shows that simultaneous label
and source-assignment transport preserves positivity.  This module contracts
that result through the repository's literal `TransportedTargetPackage`.

Thus a coordinatewise-positive reference column gives a strictly positive
entry for the actual transported target package.  The statement keeps the
target package, source row, and physical equalities definitionally linked; it
does not postulate aggregate posterior positivity.

Constructive contract: equality transport and finite positive products only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingPositiveTransport
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

namespace YMGap.Continuum.CompactDualSlabTransportedTargetPositiveEntry

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingPositiveTransport
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableRealizationBridge

/-- A positive reference entry remains positive for the literal target stored
in the transported package over the propositionally equal physical pair. -/
theorem transportedTargetPackage_productWeight_pos
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
    (rightPackages : List FiniteBistochasticQKernelPackage)
    (hpackages₁ : slabPhysicalPairRecouplingPackages extent
      leftPhysical₁ rightPhysical₁ = rightPackages)
    (hpackages₂ : slabPhysicalPairRecouplingPackages extent
      leftPhysical₂ rightPhysical₂ = rightPackages)
    (sourceTarget : TargetMembershipPackage rightPackages)
    (hpositive : FiniteBistochasticCoordinatewisePositive
      (slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₁ rightPhysical₁ leftAssignment₁ rightAssignment₁
        left_mem₁ right_mem₁)
      (transportFiniteBistochasticTargetAssignment
        hpackages₁ sourceTarget.target)) :
    (0 : Q') < finiteBistochasticProductWeight
      (slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₂ rightPhysical₂ leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂)
      (transportedTargetPackage hpackages₂ sourceTarget).target := by
  rw [transportedTarget_eq_physicalTransport hleft hright rightPackages
    hpackages₁ hpackages₂ sourceTarget]
  exact productionSource_productWeight_pos_transport K extent
    hleft hright leftAssignment₁ rightAssignment₁
    leftAssignment₂ rightAssignment₂ hleftAssignment hrightAssignment
    left_mem₁ right_mem₁ left_mem₂ right_mem₂
    (transportFiniteBistochasticTargetAssignment
      hpackages₁ sourceTarget.target) hpositive

end YMGap.Continuum.CompactDualSlabTransportedTargetPositiveEntry

#print axioms
  YMGap.Continuum.CompactDualSlabTransportedTargetPositiveEntry.transportedTargetPackage_productWeight_pos

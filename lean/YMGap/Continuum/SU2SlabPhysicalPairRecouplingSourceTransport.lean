/-
# Exact transport of a slab recoupling production row

The product package list depends only on the two physical labellings, while a
distinguished production row also depends on the two accepted auxiliary
assignments.  Simultaneous equality transport of those four inputs identifies
the exact heterogeneous source assignment without inspecting any concrete
product coordinate.

Constructive contract: equality elimination and proof irrelevance only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Canonical equality of the physical-only package lists. -/
def slabPhysicalPairRecouplingPackages_transport
    (extent : Nat)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂) :
    slabPhysicalPairRecouplingPackages extent
        leftPhysical₁ rightPhysical₁ =
      slabPhysicalPairRecouplingPackages extent
        leftPhysical₂ rightPhysical₂ := by
  cases hleft
  cases hright
  rfl

/-- Transport a heterogeneous source assignment along the canonical physical
package equality. -/
def transportSlabPhysicalPairRecouplingSourceAssignment
    (extent : Nat)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (source : SlabPhysicalPairRecouplingSourceAssignment
      extent leftPhysical₁ rightPhysical₁) :
    SlabPhysicalPairRecouplingSourceAssignment
      extent leftPhysical₂ rightPhysical₂ :=
  transportFiniteBistochasticSourceAssignment
    (slabPhysicalPairRecouplingPackages_transport extent hleft hright)
    source

/-- The distinguished product row is invariant under simultaneous equality
transport of both physical labellings and both accepted assignments. -/
theorem slabPhysicalPairRecouplingProductionSource_transport
    (K extent : Nat)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ : SlabFusionWitnessAssignment)
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
        (boundaryCompleteSlabLinks extent)) :
    transportSlabPhysicalPairRecouplingSourceAssignment extent hleft hright
        (slabPhysicalPairRecouplingProductionSource K extent
          leftPhysical₁ rightPhysical₁ leftAssignment₁ rightAssignment₁
          left_mem₁ right_mem₁) =
      slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical₂ rightPhysical₂ leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂ := by
  cases hleft
  cases hright
  cases hleftAssignment
  cases hrightAssignment
  rfl

#print axioms slabPhysicalPairRecouplingPackages_transport
#print axioms transportSlabPhysicalPairRecouplingSourceAssignment
#print axioms slabPhysicalPairRecouplingProductionSource_transport

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceTransport

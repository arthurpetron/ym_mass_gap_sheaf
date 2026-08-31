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

/-- Canonical package equality when both the extent and physical pair are
transported.  Keeping the extent as an independent natural number avoids
dependent elimination on a bundled `SlabPhysicalData`. -/
def slabPhysicalPairRecouplingPackages_transport_extent
    (extent₁ extent₂ : Nat) (hextent : extent₁ = extent₂)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂) :
    slabPhysicalPairRecouplingPackages extent₁
        leftPhysical₁ rightPhysical₁ =
      slabPhysicalPairRecouplingPackages extent₂
        leftPhysical₂ rightPhysical₂ := by
  cases hextent
  cases hleft
  cases hright
  rfl

/-- The distinguished production row is invariant under simultaneous
transport of the extent, both physical labellings, and both auxiliary
assignments. -/
theorem slabPhysicalPairRecouplingProductionSource_transport_extent
    (K extent₁ extent₂ : Nat) (hextent : extent₁ = extent₂)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ : SlabFusionWitnessAssignment)
    (hleftAssignment : leftAssignment₁ = leftAssignment₂)
    (hrightAssignment : rightAssignment₁ = rightAssignment₂)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent₁ leftPhysical₁
        (boundaryCompleteSlabLinks extent₁))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent₁ rightPhysical₁
        (boundaryCompleteSlabLinks extent₁))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent₂ leftPhysical₂
        (boundaryCompleteSlabLinks extent₂))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent₂ rightPhysical₂
        (boundaryCompleteSlabLinks extent₂)) :
    transportFiniteBistochasticSourceAssignment
        (slabPhysicalPairRecouplingPackages_transport_extent
          extent₁ extent₂ hextent hleft hright)
        (slabPhysicalPairRecouplingProductionSource K extent₁
          leftPhysical₁ rightPhysical₁ leftAssignment₁ rightAssignment₁
          left_mem₁ right_mem₁) =
      slabPhysicalPairRecouplingProductionSource K extent₂
        leftPhysical₂ rightPhysical₂ leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂ := by
  cases hextent
  simpa only [transportSlabPhysicalPairRecouplingSourceAssignment] using
    (slabPhysicalPairRecouplingProductionSource_transport K extent₁
      hleft hright leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ hleftAssignment hrightAssignment
      left_mem₁ right_mem₁ left_mem₂ right_mem₂)

/-- Restricting the written link row is functorial in equality of the written
link list.  The theorem stays parametric in the list, so no concrete
heterogeneous product is normalized. -/
theorem slabPhysicalPairRecouplingProductionSourceFrom_transport_links
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (sourceLinks targetLinks : List
      {link // link ∈ boundaryCompleteSlabLinks extent})
    (hlinks : sourceLinks = targetLinks) :
    transportFiniteBistochasticSourceAssignment
        (congrArg (fun links => links.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink extent
            leftPhysical rightPhysical linked) hlinks)
        (slabPhysicalPairRecouplingProductionSourceFrom K extent
          leftPhysical rightPhysical leftAssignment rightAssignment
          left_mem right_mem sourceLinks) =
      slabPhysicalPairRecouplingProductionSourceFrom K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem targetLinks := by
  cases hlinks
  rfl

/-- Simultaneously transport the canonical full production row across an
extent/physical/assignment identification and then restrict it to a
propositionally equal written link list. -/
theorem slabPhysicalPairRecouplingProductionSource_transport_extent_to_links
    (K extent₁ extent₂ : Nat) (hextent : extent₁ = extent₂)
    {leftPhysical₁ rightPhysical₁ leftPhysical₂ rightPhysical₂ :
      SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ : SlabFusionWitnessAssignment)
    (hleftAssignment : leftAssignment₁ = leftAssignment₂)
    (hrightAssignment : rightAssignment₁ = rightAssignment₂)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent₁ leftPhysical₁
        (boundaryCompleteSlabLinks extent₁))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent₁ rightPhysical₁
        (boundaryCompleteSlabLinks extent₁))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent₂ leftPhysical₂
        (boundaryCompleteSlabLinks extent₂))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent₂ rightPhysical₂
        (boundaryCompleteSlabLinks extent₂))
    (targetLinks : List
      {link // link ∈ boundaryCompleteSlabLinks extent₂})
    (hlinks : (boundaryCompleteSlabLinks extent₂).attach = targetLinks) :
    transportFiniteBistochasticSourceAssignment
        ((slabPhysicalPairRecouplingPackages_transport_extent
          extent₁ extent₂ hextent hleft hright).trans
          (congrArg (fun links => links.map fun linked =>
            slabPhysicalPairRecouplingPackageAtLink extent₂
              leftPhysical₂ rightPhysical₂ linked) hlinks))
        (slabPhysicalPairRecouplingProductionSource K extent₁
          leftPhysical₁ rightPhysical₁ leftAssignment₁ rightAssignment₁
          left_mem₁ right_mem₁) =
      slabPhysicalPairRecouplingProductionSourceFrom K extent₂
        leftPhysical₂ rightPhysical₂ leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂ targetLinks := by
  cases hextent
  cases hleft
  cases hright
  cases hleftAssignment
  cases hrightAssignment
  cases hlinks
  rfl

#print axioms slabPhysicalPairRecouplingPackages_transport
#print axioms transportSlabPhysicalPairRecouplingSourceAssignment
#print axioms slabPhysicalPairRecouplingProductionSource_transport
#print axioms slabPhysicalPairRecouplingPackages_transport_extent
#print axioms slabPhysicalPairRecouplingProductionSource_transport_extent
#print axioms slabPhysicalPairRecouplingProductionSourceFrom_transport_links
#print axioms slabPhysicalPairRecouplingProductionSource_transport_extent_to_links

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceTransport

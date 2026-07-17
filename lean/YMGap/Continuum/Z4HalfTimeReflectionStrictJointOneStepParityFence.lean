/-
# One-step parity fence for the strict half-time reflection carrier

The even-shift covariance proof uses the existing odd reflection extent
`2r+1`.  A one-step exchange would have to send the reflected lower query of
an observable to the upper query translated forward by one lattice unit.
At the raw plaquette level this is possible, but only after changing the
reflection extent to the adjacent even value `2r+2`.

This file proves that exact adjacent-extent exchange and machine-refutes the
same identity for the existing odd carrier.  It also records the geometric
reason: the even carrier fixes a central spatial plaquette, whereas the odd
carrier exchanges the two adjacent spatial slices.  Thus one-step covariance
cannot be obtained by silently reusing the current finite entry recoding; an
even-parity/interface kernel (or an equivalent half-step embedding) is a real
additional construction.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepParityFence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

/-! ## 1. Odd carrier versus the adjacent even carrier -/

/-- The reflection extent which exchanges a lower query with its one-step
translated upper query. -/
def oneStepReflectionExtent (radius : Nat) : Nat :=
  centralExtent radius + 1

theorem oneStepReflectionExtent_eq_even (radius : Nat) :
    oneStepReflectionExtent radius = (radius + 1) + (radius + 1) := by
  unfold oneStepReflectionExtent centralExtent
  omega

/-- On a query plaquette lying within the strict margin, reflection in the
adjacent even slab sends the existing lower query exactly to the upper query
translated by one. -/
theorem adjacentEvenReflection_exchanges_raw_oneStep
    (radius : Nat) (plaquette : Z4Plaq)
    (htime : plaquette.1.2.2.2 + 3 ≤ radius) :
    timeReflectPlaquette (oneStepReflectionExtent radius)
        (rawStrictLowerQueryPlaquette radius plaquette) =
      strictJointRawUpperQueryPlaquette radius
        (timeShiftPlaquette 1 plaquette) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change d + 3 ≤ radius at htime
  cases plane <;>
    simp [oneStepReflectionExtent, rawStrictLowerQueryPlaquette,
      strictJointRawUpperQueryPlaquette, centralExtent,
      timeReflectPlaquette, uniformShiftPlaquette, uniformShiftVertex,
      timeShiftPlaquette, timeShiftVertex] <;>
    omega

/-- The current odd reflection simply returns the unshifted upper query; it
does not perform the one-step exchange. -/
theorem existingOddReflection_returns_raw_upper
    (radius : Nat) (plaquette : Z4Plaq)
    (htime : plaquette.1.2.2.2 + 3 ≤ radius) :
    timeReflectPlaquette (centralExtent radius)
        (rawStrictLowerQueryPlaquette radius plaquette) =
      strictJointRawUpperQueryPlaquette radius plaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  change d + 3 ≤ radius at htime
  cases plane <;>
    simp [rawStrictLowerQueryPlaquette,
      strictJointRawUpperQueryPlaquette, centralExtent,
      timeReflectPlaquette, uniformShiftPlaquette, uniformShiftVertex] <;>
    omega

def oneStepFencePlaquette : Z4Plaq :=
  (((0, 0, 0, 0), .p01) : Z4Plaq)

/-- Closed refutation of the literal one-step query identity in the existing
odd carrier. -/
theorem existingOddReflection_raw_oneStep_counterexample :
    timeReflectPlaquette (centralExtent 5)
        (rawStrictLowerQueryPlaquette 5 oneStepFencePlaquette) ≠
      strictJointRawUpperQueryPlaquette 5
        (timeShiftPlaquette 1 oneStepFencePlaquette) := by
  decide

/-- Universal formulation ruled out by the preceding closed finite query. -/
def ExistingOddCarrierRawOneStepExchange : Prop :=
  ∀ radius plaquette,
    plaquette.1.2.2.2 + 3 ≤ radius →
      timeReflectPlaquette (centralExtent radius)
          (rawStrictLowerQueryPlaquette radius plaquette) =
        strictJointRawUpperQueryPlaquette radius
          (timeShiftPlaquette 1 plaquette)

theorem not_existingOddCarrierRawOneStepExchange :
    ¬ ExistingOddCarrierRawOneStepExchange := by
  intro hexchange
  exact existingOddReflection_raw_oneStep_counterexample
    (hexchange 5 oneStepFencePlaquette (by decide))

/-! ## 2. A finite-entry event fence -/

def rawPlaquetteOccurrenceEvent
    (marked : Z4Plaq) (family : List Z4Plaq) : Bool :=
  decide (marked ∈ family)

def existingOddReflectedFencePlaquette : Z4Plaq :=
  timeReflectPlaquette (centralExtent 5)
    (rawStrictLowerQueryPlaquette 5 oneStepFencePlaquette)

def oneStepUpperFencePlaquette : Z4Plaq :=
  strictJointRawUpperQueryPlaquette 5
    (timeShiftPlaquette 1 oneStepFencePlaquette)

/-- The two literal singleton occurrence events already differ.  Hence the
one-step entry cannot be obtained by an exact current-carrier event rewrite. -/
theorem existingOddCarrier_oneStepFiniteEntryEvent_ne :
    rawPlaquetteOccurrenceEvent existingOddReflectedFencePlaquette ≠
      rawPlaquetteOccurrenceEvent oneStepUpperFencePlaquette := by
  intro hevent
  have hevaluation := congrArg
    (fun event : List Z4Plaq → Bool =>
      event [oneStepUpperFencePlaquette]) hevent
  change false = true at hevaluation
  exact Bool.noConfusion hevaluation

/-! ## 3. The parity-changing fixed spatial slice -/

def oneStepCentralSpatialPlaquette (radius : Nat) : Z4Plaq :=
  (((0, 0, 0, radius + 1), .p01) : Z4Plaq)

/-- The adjacent even reflection has a fixed central spatial plaquette. -/
theorem oneStepCentralSpatialPlaquette_fixed (radius : Nat) :
    timeReflectPlaquette (oneStepReflectionExtent radius)
        (oneStepCentralSpatialPlaquette radius) =
      oneStepCentralSpatialPlaquette radius := by
  simp [oneStepReflectionExtent, oneStepCentralSpatialPlaquette,
    centralExtent, timeReflectPlaquette]
  omega

/-- That fixed plaquette is a genuine member of the adjacent boundary-complete
slab, not an off-carrier artifact. -/
theorem oneStepCentralSpatialPlaquette_mem_evenSlab (radius : Nat) :
    oneStepCentralSpatialPlaquette radius ∈
      boundaryCompleteSlabPlaquettes
        (oneStepReflectionExtent radius) := by
  rw [mem_boundaryCompleteSlabPlaquettes]
  constructor
  · rw [mem_boxPlaquettes]
    simp [oneStepCentralSpatialPlaquette, oneStepReflectionExtent,
      centralExtent]
    omega
  · simp [oneStepCentralSpatialPlaquette, oneStepReflectionExtent,
      centralExtent, plaquetteTimeAdmissible]
    omega

/-- In the existing odd carrier the same spatial plaquette is exchanged with
the adjacent lower slice rather than fixed. -/
theorem existingOddReflection_moves_oneStepCentralSpatialPlaquette
    (radius : Nat) :
    timeReflectPlaquette (centralExtent radius)
        (oneStepCentralSpatialPlaquette radius) =
      (((0, 0, 0, radius), .p01) : Z4Plaq) := by
  simp [oneStepCentralSpatialPlaquette, centralExtent,
    timeReflectPlaquette]

#print axioms oneStepReflectionExtent_eq_even
#print axioms adjacentEvenReflection_exchanges_raw_oneStep
#print axioms existingOddReflection_returns_raw_upper
#print axioms existingOddReflection_raw_oneStep_counterexample
#print axioms not_existingOddCarrierRawOneStepExchange
#print axioms existingOddCarrier_oneStepFiniteEntryEvent_ne
#print axioms oneStepCentralSpatialPlaquette_fixed
#print axioms oneStepCentralSpatialPlaquette_mem_evenSlab
#print axioms existingOddReflection_moves_oneStepCentralSpatialPlaquette

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepParityFence

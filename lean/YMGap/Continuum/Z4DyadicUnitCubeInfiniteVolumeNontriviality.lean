/-
# Positive infinite-volume occurrence of the dyadic unit cube

The canonical cofinal construction already gives a constructive-real
thermodynamic limit for every fixed cutoff-one polymer occurrence.  The
volume-uniform rational floor for the transported dyadic cube holds at every
term of that cofinal sequence, so it passes directly to the constructive-real
limit and supplies an `IsPositive` witness.

This is strong-coupling infinite-volume non-triviality for one explicit local
lattice excitation.  It does not identify a continuum local field.
-/

import YMGap.Continuum.Z4CanonicalOccurrenceCofinal
import YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor

namespace YMGap.Continuum.Z4DyadicUnitCubeInfiniteVolumeNontriviality

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalOccurrenceCofinal
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor

/-- The actual constructive thermodynamic limit of the explicit 24-face
cube-occurrence probabilities. -/
def dyadicUnitCubeInfiniteVolumeOccurrence : CReal :=
  anchorPolymerOccurrenceCofinalLimit
    dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers

/-- The same exact positive rational that bounds every finite box also bounds
the constructive-real thermodynamic limit. -/
theorem dyadicUnitCubeUniformOccurrenceFloor_le_infiniteVolume :
    CReal.ofQ' dyadicUnitCubeUniformOccurrenceFloor ≤
      dyadicUnitCubeInfiniteVolumeOccurrence := by
  unfold dyadicUnitCubeInfiniteVolumeOccurrence
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  change dyadicUnitCubeUniformOccurrenceFloor ≤
    anchorPolymerOccurrenceProbability (4 + stage)
      (transportPolymer 4 (4 + stage) dyadicUnitCubeSupportIds)
  have hfloor := dyadicUnitCubeUniformOccurrenceFloor_le_probability
    (n := 4 + stage) (by omega)
  simpa only [dyadicUnitCubeSupportIdsAt] using hfloor

/-- A machine-checked constructive strict-positivity certificate for one
explicit interacting local occurrence in the infinite-volume anchor state. -/
theorem dyadicUnitCubeInfiniteVolumeOccurrence_pos :
    CReal.IsPositive dyadicUnitCubeInfiniteVolumeOccurrence :=
  ⟨dyadicUnitCubeUniformOccurrenceFloor,
    dyadicUnitCubeUniformOccurrenceFloor_pos,
    dyadicUnitCubeUniformOccurrenceFloor_le_infiniteVolume⟩

end YMGap.Continuum.Z4DyadicUnitCubeInfiniteVolumeNontriviality

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4DyadicUnitCubeInfiniteVolumeNontriviality.dyadicUnitCubeInfiniteVolumeOccurrence
#print axioms YMGap.Continuum.Z4DyadicUnitCubeInfiniteVolumeNontriviality.dyadicUnitCubeUniformOccurrenceFloor_le_infiniteVolume
#print axioms YMGap.Continuum.Z4DyadicUnitCubeInfiniteVolumeNontriviality.dyadicUnitCubeInfiniteVolumeOccurrence_pos

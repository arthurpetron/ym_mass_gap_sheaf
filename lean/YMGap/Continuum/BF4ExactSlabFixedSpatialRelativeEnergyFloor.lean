/-
# Relative-Ward floor for the original temporal plaquette energy

The predictor is the literal upper-time copy of the lower plaquette.
Apply the relative prediction theorem to the complete original joint
window action, then use the exact SAME-partition temporal-energy pin.
No one-slice marginal is substituted for this joint action.
-/

import YMGap.Continuum.BF4ExactSlabRelativePredictionError
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeEnergyFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabRelativePredictionError
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteEnergyFloor
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

attribute [local irreducible] plaquette normalizedEnergy

private theorem stage_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n stage : Nat) (hK : relativeCutoff w 2048 ≤ headCutoff w+stage)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    relativePredictionFloor w ≤ (2 : Q') * normalizedEnergy hw0 hw1
      (headCutoff w+stage) width (Nat.le_add_right _ _) n
      (characterPolynomial (plaquette width p).scalar 1) := by
  let E := width+(n+(1+n))+1
  let lower := timeShiftPlaquette n p
  let upper := timeShiftPlaquette (n+1) p
  let ids := chainIds E width 0 (n+(1+n))
  have hface : lower ∈ boundaryCompleteSlabPlaquettes E :=
    spatialFaces_shift_physical (by dsimp [E]; omega) (by dsimp [E]; omega) hp
  have hfree : faceLinkA lower ∉ edgesOf upper := lower_link_misses_upper p hp n
  have hfloor := finite_prediction_floor hw0 hw1 E ids
    (fun _ hi => chainIds_physical hi) (chainIds_nodup _ _ _ _) stage hK hface
    (faceCharacter E upper) (faceCharacter_supported E upper) (edgesOf upper)
    ((face_scalar_local E upper).character 1) hfree
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.ge_of_eqv (plaquette_jump_originalFiniteValue hw0 hw1 width n stage p hp))

/-- An explicit original temporal-energy floor for every physical spatial
plaquette, all widths and depths, and every displayed late heat cutoff.
The coefficient depends on nome but has no global heat-minimum factor. -/
theorem plaquette_relative_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 2048 ≤ K) (n : Nat)
    (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    relativePredictionFloor w ≤ (2 : Q') * normalizedEnergy hw0 hw1 K width
      (Nat.le_trans (headCutoff_le_relativeCutoff w 2048) hK) n
      (characterPolynomial (plaquette width p).scalar 1) := by
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 2048) hK
  have h := stage_energy_floor hw0 hw1 width n (K-headCutoff w)
    (by simpa only [Nat.add_sub_of_le hhead] using hK) p hp
  simpa only [Nat.add_sub_of_le hhead] using h

#print axioms plaquette_relative_energy_floor

end YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeEnergyFloor

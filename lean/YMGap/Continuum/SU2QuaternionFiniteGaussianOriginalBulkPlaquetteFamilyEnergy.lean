/-
# Original interacting temporal-energy floor for the rational bulk source

The exact bulk face list and rational coefficient profile are specialized in
the existing canonical original plaquette-family energy theorem.  Thus the
same finite source pays the established coefficient-mass floor in the actual
normalized interacting temporal energy, with no face recoding or coefficient
replacement.

This is a lower energy bound.  It is not the denominator-relative upper bound
needed to transfer the free-reference radial-ratio floor, and it does not
compare the free product-Gaussian law with the original interacting law or
assert a continuum or Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkPlaquetteFamilyLabels
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkPlaquetteFamilyEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow (lower upper)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy (family_energy_floor)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge

/-- The literal rational bulk family pays the established cutoff- and
volume-uniform coefficient floor in the ACTUAL original normalized temporal
energy.  The source width is the canonical containing width `s^2`. -/
theorem bulkSource_original_energy_floor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (K : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    lower w * listQSum
        (fun face =>
          bulkSourceCoefficient s hs face * bulkSourceCoefficient s hs face)
        (bulkSourceFaces s) ≤
      (600 * upper w) *
        normalizedEnergy hw0 hw1 K (s * s) hK n
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)) :=
  family_energy_floor hw0 hw1 K (s * s) hK n
    (bulkSourceFaces s) (bulkSourceFaces_nodup s)
    (bulkSourceFaces_spatial s) (bulkSourceCoefficient s hs)

#print axioms bulkSource_original_energy_floor

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkPlaquetteFamilyEnergy

/-
# Original adjacent-time labels for the rational bulk source

The formula-level bulk source is instantiated directly in the canonical
original plaquette-family label schedule.  The lower and upper copies retain
the same face list and coefficients, with only the required upper-sign change.
The resulting doubled list is duplicate-free, physical in every displayed
ambient slab, and has exactly twice the source coefficient-square mass.

This is the label and coefficient part of the original-source join.  It does
not identify the finite Gaussian law with the original interacting law, prove
a denominator-relative comparison, or assert a continuum or Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkPlaquetteFamilyLabels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyLabels
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge

local infix:50 " ≈ " => Q'.eqv

/-- The canonical adjacent-time original labels retain every bulk source face
exactly once on each of the two time slices. -/
theorem bulkSourceDoubledLabels_nodup (s n : Nat) :
    (doubledLabels n (bulkSourceFaces s)).Nodup :=
  doubledLabels_nodup n (bulkSourceFaces s) (bulkSourceFaces_nodup s)
    (bulkSourceFaces_spatial s)

/-- Every doubled bulk label is a literal physical original plaquette under
the same room guards used by the original family consumer. -/
theorem bulkSourceDoubledLabels_physical
    {s extent n : Nat}
    (hwidth : s * s ≤ extent) (htime : n + 1 ≤ extent)
    {face : Z4Plaq}
    (hface : face ∈ doubledLabels n (bulkSourceFaces s)) :
    face ∈ boundaryCompleteSlabPlaquettes extent :=
  doubledLabels_physical hwidth htime (bulkSourceFaces s)
    (bulkSourceFaces_spatial s) hface

/-- The lower original copy carries the unchanged rational bulk coefficient. -/
theorem bulkSourceDoubledCoeff_lower
    {s : Nat} (hs : 0 < s) (n : Nat) {face : Z4Plaq}
    (hface : face ∈ bulkSourceFaces s) :
    doubledCoeff n (bulkSourceCoefficient s hs) (timeShiftPlaquette n face) =
      bulkSourceCoefficient s hs face :=
  doubledCoeff_lower n (bulkSourceCoefficient s hs)
    (bulkSourceFace_mem_spatialFaces_square hface)

/-- The upper original copy carries exactly the negative rational bulk
coefficient required by the canonical adjacent-time difference. -/
theorem bulkSourceDoubledCoeff_upper
    {s : Nat} (hs : 0 < s) (n : Nat) {face : Z4Plaq}
    (hface : face ∈ bulkSourceFaces s) :
    doubledCoeff n (bulkSourceCoefficient s hs) (timeShiftPlaquette (n + 1) face) =
      -(bulkSourceCoefficient s hs face) :=
  doubledCoeff_upper n (bulkSourceCoefficient s hs)
    (bulkSourceFace_mem_spatialFaces_square hface)

/-- The canonical doubled original family has exactly twice the complete
bulk coefficient-square mass, with all multiplicities and signs retained. -/
theorem bulkSourceDoubled_square_sum
    {s : Nat} (hs : 0 < s) (n : Nat) :
    listQSum
        (fun face =>
          doubledCoeff n (bulkSourceCoefficient s hs) face *
            doubledCoeff n (bulkSourceCoefficient s hs) face)
        (doubledLabels n (bulkSourceFaces s)) ≈
      2 * listQSum
        (fun face =>
          bulkSourceCoefficient s hs face * bulkSourceCoefficient s hs face)
        (bulkSourceFaces s) :=
  doubled_square_sum n (bulkSourceCoefficient s hs) (bulkSourceFaces s)
    (bulkSourceFaces_spatial s)

/-- The canonical doubled original label family is quantitatively nonzero at
every positive source side.  This is coefficient mass, not an interacting
expectation or OS norm. -/
theorem bulkSourceDoubled_square_sum_pos
    {s : Nat} (hs : 0 < s) (n : Nat) :
    (0 : Q') <
      listQSum
        (fun face =>
          doubledCoeff n (bulkSourceCoefficient s hs) face *
            doubledCoeff n (bulkSourceCoefficient s hs) face)
        (doubledLabels n (bulkSourceFaces s)) := by
  have hright :
      (0 : Q') <
        2 * listQSum
          (fun face =>
            bulkSourceCoefficient s hs face * bulkSourceCoefficient s hs face)
          (bulkSourceFaces s) :=
    Q'.mul_pos (by decide) (bulkSourceCoefficientMass_pos s hs)
  exact Q'.pos_of_lt_of_le hright
    (Q'.ge_of_eqv (bulkSourceDoubled_square_sum hs n))

#print axioms bulkSourceDoubledLabels_nodup
#print axioms bulkSourceDoubledLabels_physical
#print axioms bulkSourceDoubledCoeff_lower
#print axioms bulkSourceDoubledCoeff_upper
#print axioms bulkSourceDoubled_square_sum
#print axioms bulkSourceDoubled_square_sum_pos

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkPlaquetteFamilyLabels

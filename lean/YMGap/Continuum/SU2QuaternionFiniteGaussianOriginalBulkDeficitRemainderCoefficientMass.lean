/-
# Normalized coefficient mass of the original bulk square remainder

The local scalar-square remainder carries exactly one quarter of the bulk
profile coefficient.  Its coefficient-square mass is therefore exactly one
sixteenth of the finite Gaussian source coefficient-square mass, before and
after normalization by the literal face count `3*s^3`.  The existing dyadic
profile floor consequently transfers with no extra side dependence.

This is a coefficient normalization result.  It does not compare the
ORIGINAL and FREE laws, bound the geometric covariance amplitude, prove a
neighboring sign, remove a cutoff, construct a Hamiltonian, or prove the Clay
mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance

local infix:50 " ≈ " => Q'.eqv

/-- Squaring the literal quarter weight costs exactly `1/16`. -/
def originalBulkScalarSquareRemainderQuarterSquare : Q' :=
  Q'.mkPos 1 16 (by decide)

private theorem faceWeight_square_scale
    (s : Nat) (hs : 0 < s) (face : Z4Plaq) :
    originalBulkScalarSquareRemainderFaceWeight s hs face *
        originalBulkScalarSquareRemainderFaceWeight s hs face ≈
      originalBulkScalarSquareRemainderQuarterSquare *
        (bulkSourceCoefficient s hs face *
          bulkSourceCoefficient s hs face) := by
  let quarter : Q' := Q'.mkPos 1 4 (by decide)
  let coefficient := bulkSourceCoefficient s hs face
  have hregroup :
      (quarter * coefficient) * (quarter * coefficient) ≈
        (quarter * quarter) * (coefficient * coefficient) := by
    ring_qeqv
  have hscale :
      quarter * quarter ≈
        originalBulkScalarSquareRemainderQuarterSquare := by
    unfold quarter originalBulkScalarSquareRemainderQuarterSquare
    decide
  exact Q'.eqv_trans _ _ _ hregroup
    (Q'.mul_eqv_congr_right _ _ (coefficient * coefficient) hscale)

/-- The complete remainder coefficient-square mass is exactly one sixteenth
of the existing finite Gaussian source coefficient-square mass. -/
theorem originalBulkScalarSquareRemainderFaceWeightSquareMass_eqv
    (s : Nat) (hs : 0 < s) :
    originalBulkScalarSquareRemainderFaceWeightSquareMass s hs ≈
      originalBulkScalarSquareRemainderQuarterSquare *
        listQSum
          (fun face =>
            bulkSourceCoefficient s hs face *
              bulkSourceCoefficient s hs face)
          (bulkSourceFaces s) := by
  unfold originalBulkScalarSquareRemainderFaceWeightSquareMass
  exact Q'.eqv_trans _ _ _
    (listQSum_congr (faceWeight_square_scale s hs) (bulkSourceFaces s))
    (listQSum_mul_left
      originalBulkScalarSquareRemainderQuarterSquare
      (fun face =>
        bulkSourceCoefficient s hs face *
          bulkSourceCoefficient s hs face)
      (bulkSourceFaces s))

private theorem bulkFaceCount_pos (s : Nat) (hs : 0 < s) :
    (0 : Q') < Q'.ofNat (3 * s ^ 3) := by
  change (0 : Int) * 1 < ((3 * s ^ 3 : Nat) : Int) * 1
  rw [Int.zero_mul, Int.mul_one]
  exact_mod_cast Nat.mul_pos (by decide) (Nat.pow_pos hs)

/-- Exact remainder coefficient-square mass per listed bulk face. -/
def normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass
    (s : Nat) (hs : 0 < s) : Q' :=
  Q'.divPos
    (originalBulkScalarSquareRemainderFaceWeightSquareMass s hs)
    (Q'.ofNat (3 * s ^ 3))
    (bulkFaceCount_pos s hs)

/-- Normalization by the same face count preserves the exact `1/16` factor. -/
theorem normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass_eqv
    (s : Nat) (hs : 0 < s) :
    normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass s hs ≈
      originalBulkScalarSquareRemainderQuarterSquare *
        normalizedBulkSourceCoefficientMassAtSide s hs := by
  unfold normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass
    normalizedBulkSourceCoefficientMassAtSide Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (originalBulkScalarSquareRemainderFaceWeightSquareMass_eqv s hs))
    (Q'.mul_assoc_eqv
      originalBulkScalarSquareRemainderQuarterSquare
      (listQSum
        (fun face =>
          bulkSourceCoefficient s hs face *
            bulkSourceCoefficient s hs face)
        (bulkSourceFaces s))
      (Q'.recipPos (Q'.ofNat (3 * s ^ 3)) (bulkFaceCount_pos s hs)))

/-- Dyadic normalized remainder-mass floor, exactly `1/16` of the existing
normalized bulk coefficient-mass floor. -/
def normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor : Q' :=
  Q'.mkPos 1 (128 * 3 ^ 36) (by decide)

theorem normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor_eqv :
    normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor ≈
      originalBulkScalarSquareRemainderQuarterSquare *
        normalizedBulkCoefficientMassFloor := by
  decide

theorem normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass_dyadic_floor
    (scale : Nat) :
    normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor ≤
      normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass
        (2 ^ scale) (Nat.pow_pos (by decide)) := by
  have hsource := normalizedBulkSourceCoefficientMassAtSide_dyadic_floor scale
  have hscaled :
      originalBulkScalarSquareRemainderQuarterSquare *
          normalizedBulkCoefficientMassFloor ≤
        originalBulkScalarSquareRemainderQuarterSquare *
          normalizedBulkSourceCoefficientMassAtSide
            (2 ^ scale) (Nat.pow_pos (by decide)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsource (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor_eqv)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass_eqv
            (2 ^ scale) (Nat.pow_pos (by decide))))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.originalBulkScalarSquareRemainderQuarterSquare
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.originalBulkScalarSquareRemainderFaceWeightSquareMass_eqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass_eqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.normalizedOriginalBulkScalarSquareRemainderCoefficientMassFloor_eqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCoefficientMass.normalizedOriginalBulkScalarSquareRemainderFaceWeightSquareMass_dyadic_floor

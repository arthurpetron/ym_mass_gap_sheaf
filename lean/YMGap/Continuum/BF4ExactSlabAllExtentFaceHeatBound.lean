/-
# Cutoff-independent bounds on the ORIGINAL finite face heat polynomials

The bound is computed from the original prefix at the polynomial-dependent
starting label plus its closed tail. It covers every representation cutoff
K at a fixed rational 0 < w < 1, extent and face. All these dependencies
remain explicit; this is not a volume- or spacing-uniform bound.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail

namespace YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
open YMGap.Continuum.SU2HeatCharacterPolynomialTail

local infix:50 " ≈ " => Q'.eqv

theorem faceHeat_coefficientL1_monotone (w : Q') (extent id K J : Nat) (hKJ : K ≤ J) :
    polynomialCoefficientL1 (faceHeatPolynomial w K extent id) ≤
      polynomialCoefficientL1 (faceHeatPolynomial w J extent id) := by
  have hj : J = K + (J - K) := (Nat.add_sub_of_le hKJ).symm
  rw [hj, faceHeatPolynomial_cutoff_append]
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (polynomialCoefficientL1_nonnegative _))
    (Q'.le_of_eqv (Q'.eqv_symm (coefficientL1_add _ _)))

def faceHeatBound (w : Q') (extent id : Nat) : Q' :=
  polynomialCoefficientL1 (faceHeatPolynomial w (polynomialLabelCutoff w (faceScalar extent id)) extent id) +
    polynomialClosedTail w (faceScalar extent id) 1

theorem faceHeatBound_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (extent id : Nat) :
    (0 : Q') ≤ faceHeatBound w extent id :=
  Q'.zero_le_add _ _ (polynomialCoefficientL1_nonnegative _)
    (HKConvGen.geoTailBase_nonneg (heatCharacterMajorant_nonnegative hw _ _) HalfPow.half_nonneg 1)

theorem faceHeat_coefficientL1_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id K : Nat) :
    polynomialCoefficientL1 (faceHeatPolynomial w K extent id) ≤ faceHeatBound w extent id := by
  let N := polynomialLabelCutoff w (faceScalar extent id)
  by_cases hN : N ≤ K
  · have he : K = N + (K - N) := (Nat.add_sub_of_le hN).symm
    rw [he, faceHeatPolynomial_cutoff_append]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _))
      (Q'.add_le_add_left _ _ _ (faceHeatTail_coefficientL1 hw0 hw1 extent id 0 (K - N)))
  · exact Q'.le_trans' _ _ _ (faceHeat_coefficientL1_monotone w extent id K N (by omega))
      (Q'.add_le_self_of_nonneg _ _
        (HKConvGen.geoTailBase_nonneg (heatCharacterMajorant_nonnegative (Q'.le_of_lt hw0) _ _) HalfPow.half_nonneg 1))

end YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound.faceHeat_coefficientL1_monotone
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound.faceHeatBound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound.faceHeatBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound.faceHeat_coefficientL1_bound

/-
# Matrix elements of the original signed Cayley tangent

Pairing the actual two-sided orbit tangent against any vector gives a
two-sided scalar matrix-element tangent with the same source-computed squared
error radius. A unit-ball test-vector corollary is included. This is only
numerical-time differentiation on the fixed original carrier; it does not
provide physical calibration or a continuum/QFT conclusion.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyOrbitTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
import YMGap.Continuum.ScaledGNSCompletionEstimates
import YMGap.Continuum.SignedRealTimeData
import YMGap.Continuum.PositiveTimeReciprocalData

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMatrixTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.SignedRealTimeData (SignedTimeValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance inner inner_nonnegative value value_injective inner_value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency (cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyOrbitTangent
  (forwardQuotientAt backwardQuotientAt ofPointOrbitTangent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph (signedGraphMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeRealTangent
  (negativeClock)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
  (realScalar)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
  (fullSmul_realScalar)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData (slope)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime (inner_add_right inner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexification
  (ComplexValue valueAdd valueMul scalarValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz (inner_cauchySchwarz)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (value_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_realSmul bondValue_sub)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedZero_add completedAdd_zero completedNeg_add completedSmul_zero)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (completedSub_zero)
open YMGap.Continuum.ScaledGNSCompletionEstimates (mul_mono_left mul_mono_right)
open YMGap.Continuum.PositiveTimeReciprocalData (reciprocalReal reciprocalRealCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def minusOneScalar : ComplexValue := scalarValue (ofQ' (-1)) (ofQ' 0)

/-- Complex subtraction expressed using only the existing value addition and
scalar multiplication operations. -/
def valueSub (z u : ComplexValue) : ComplexValue :=
  valueAdd z (valueMul minusOneScalar u)

def valueNormSq (z : ComplexValue) : RC :=
  RCadd (RCmul z.1 z.1) (RCmul z.2 z.2)

private theorem cneg_smul_minus_one (x : H) :
    cneg hw0 hw1 x =
      BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1
        (ofQ' (-1)) (ofQ' 0) (rationalCauchy (-1)) (rationalCauchy 0) x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [cneg, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate, bondValue_sub, bondValue_realSmul,
      completedRealSmul_ofQ', completedSmul_zero]
    change BF4WilsonAllNomeLinear.completedNeg hw0 hw1 (bondValue hw0 hw1 x.1) =
      BF4WilsonAllNomeLinear.completedAdd hw0 hw1
        (BF4WilsonAllNomeLinear.completedNeg hw0 hw1 (bondValue hw0 hw1 x.1))
        (BF4WilsonAllNomeLinear.completedNeg hw0 hw1
          (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width))
    have hz : BF4WilsonAllNomeLinear.completedNeg hw0 hw1
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) =
        BF4WilsonAllNomeLinear.completedZero hw0 hw1 width := by
      have h := completedNeg_add hw0 hw1
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width)
      rw [completedAdd_zero] at h
      exact h
    rw [hz, completedAdd_zero]
  · apply bondValue_injective hw0 hw1
    simp only [cneg, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate, bondValue_add, bondValue_realSmul,
      completedRealSmul_ofQ', completedSmul_zero]
    exact (completedZero_add hw0 hw1 _).symm

theorem inner_diff_right (x y z : H) :
    inner hw0 hw1 x (diff hw0 hw1 y z) =
      valueSub (inner hw0 hw1 x y) (inner hw0 hw1 x z) := by
  unfold diff valueSub
  rw [inner_add_right, cneg_smul_minus_one, inner_smul_right]
  rfl

theorem forward_quotient_matrix_pin (p : P) (y : H) (s : SignedTimeValue)
    (D : PositiveTime) :
    inner hw0 hw1 y (forwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p))) =
      valueMul (scalarValue (reciprocalReal D) (ofQ' 0))
        (valueSub
          (inner hw0 hw1 y
            (BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction hw0 hw1
              (SignedRealTimeData.addTime s
                (SignedRealTimeData.positiveTime (timeValue D)))
              (In (ofPoint hw0 hw1 p))))
          (inner hw0 hw1 y
            (BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction hw0 hw1 s
              (In (ofPoint hw0 hw1 p))))) := by
  unfold forwardQuotientAt
  rw [← fullSmul_realScalar, inner_smul_right, inner_diff_right]
  rfl

theorem backward_quotient_matrix_pin (p : P) (y : H) (s : SignedTimeValue)
    (D : PositiveTime) :
    inner hw0 hw1 y (backwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p))) =
      valueMul (scalarValue (reciprocalReal D) (ofQ' 0))
        (valueSub
          (inner hw0 hw1 y
            (BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction hw0 hw1 s
              (In (ofPoint hw0 hw1 p))))
          (inner hw0 hw1 y
            (BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction hw0 hw1
            (SignedRealTimeData.addTime s
                (negativeClock D))
              (In (ofPoint hw0 hw1 p))))) := by
  unfold backwardQuotientAt
  rw [← fullSmul_realScalar, inner_smul_right, inner_diff_right]

/-- Squared modulus of the scalar matrix element of the actual vector error
is bounded by test-vector squared norm times vector squared error. -/
theorem matrixElement_error_le (y q tangent : H) (e : Q')
    (_he : (0 : Q') < e)
    (herror : RCle (distance hw0 hw1 q tangent) (rat e)) :
    RCle (valueNormSq (inner hw0 hw1 y (diff hw0 hw1 q tangent)))
      (RCmul (normSq hw0 hw1 y) (rat e)) := by
  have hcs := inner_cauchySchwarz hw0 hw1 width
    (value hw0 hw1 y) (value hw0 hw1 (diff hw0 hw1 q tangent))
  rw [← inner_value, ← inner_value, ← inner_value] at hcs
  have hdist : RCle (normSq hw0 hw1 (diff hw0 hw1 q tangent)) (rat e) := by
    rw [← distance_eq_norm_difference]
    exact herror
  have hmono := mul_mono_left (inner_nonnegative hw0 hw1 y) hdist
  change RCle
    (RCadd
      (RCmul (inner hw0 hw1 y (diff hw0 hw1 q tangent)).1
        (inner hw0 hw1 y (diff hw0 hw1 q tangent)).1)
      (RCmul (inner hw0 hw1 y (diff hw0 hw1 q tangent)).2
        (inner hw0 hw1 y (diff hw0 hw1 q tangent)).2))
    (RCmul (normSq hw0 hw1 y) (rat e))
  exact RCle_trans hcs (by simpa [normSq] using hmono)

theorem forward_matrix_tangent_error_le (p : P) (y : H) (e : Q')
    (he : (0 : Q') < e) (s : SignedTimeValue) (D : PositiveTime)
    (htime : RCle (realValue (timeValue D))
      (rat ((ofPointOrbitTangent hw0 hw1 p).radius e he))) :
    RCle (valueNormSq
      (inner hw0 hw1 y
        (diff hw0 hw1
          (forwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p)))
          (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))))))
      (RCmul (normSq hw0 hw1 y) (rat e)) := by
  apply matrixElement_error_le hw0 hw1 y _ _ e he
  exact (ofPointOrbitTangent hw0 hw1 p).bound e he s D htime |>.1

theorem backward_matrix_tangent_error_le (p : P) (y : H) (e : Q')
    (he : (0 : Q') < e) (s : SignedTimeValue) (D : PositiveTime)
    (htime : RCle (realValue (timeValue D))
      (rat ((ofPointOrbitTangent hw0 hw1 p).radius e he))) :
    RCle (valueNormSq
      (inner hw0 hw1 y
        (diff hw0 hw1
          (backwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p)))
          (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))))))
      (RCmul (normSq hw0 hw1 y) (rat e)) := by
  apply matrixElement_error_le hw0 hw1 y _ _ e he
  exact (ofPointOrbitTangent hw0 hw1 p).bound e he s D htime |>.2

private theorem rat_nonnegative {e : Q'} (he : (0 : Q') < e) : RCnonneg (rat e) := by
  apply CReal.leEv_ofQ'_of_approx_ge
  intro n
  exact Q'.le_of_lt he

private theorem rc_mul_one_right (a : RC) :
    RCmul a (Quotient.mk crealSetoid CReal.cone) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  rw [RCmul_mk]
  exact Quotient.sound (YMGap.Constructive.CRealAlg.cmul_cone x)

private theorem rc_mul_one_left (a : RC) :
    RCmul (Quotient.mk crealSetoid CReal.cone) a = a := by
  rw [RCmul_comm]
  exact rc_mul_one_right a

theorem forward_matrix_tangent_error_unit_ball (p : P) (y : H) (e : Q')
    (he : (0 : Q') < e) (s : SignedTimeValue) (D : PositiveTime)
    (htime : RCle (realValue (timeValue D))
      (rat ((ofPointOrbitTangent hw0 hw1 p).radius e he)))
    (hy : RCle (normSq hw0 hw1 y) (Quotient.mk crealSetoid CReal.cone)) :
    RCle (valueNormSq
      (inner hw0 hw1 y
        (diff hw0 hw1
          (forwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p)))
          (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))))))
      (rat e) := by
  have h := forward_matrix_tangent_error_le hw0 hw1 p y e he s D htime
  have hscaled := mul_mono_right (rat_nonnegative he) hy
  have hscaled' := hscaled
  rw [rc_mul_one_left] at hscaled'
  exact RCle_trans h hscaled'

theorem backward_matrix_tangent_error_unit_ball (p : P) (y : H) (e : Q')
    (he : (0 : Q') < e) (s : SignedTimeValue) (D : PositiveTime)
    (htime : RCle (realValue (timeValue D))
      (rat ((ofPointOrbitTangent hw0 hw1 p).radius e he)))
    (hy : RCle (normSq hw0 hw1 y) (Quotient.mk crealSetoid CReal.cone)) :
    RCle (valueNormSq
      (inner hw0 hw1 y
        (diff hw0 hw1
          (backwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p)))
          (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))))))
      (rat e) := by
  have h := backward_matrix_tangent_error_le hw0 hw1 p y e he s D htime
  have hscaled := mul_mono_right (rat_nonnegative he) hy
  have hscaled' := hscaled
  rw [rc_mul_one_left] at hscaled'
  exact RCle_trans h hscaled'

#print axioms valueSub
#print axioms valueNormSq
#print axioms inner_diff_right
#print axioms forward_quotient_matrix_pin
#print axioms backward_quotient_matrix_pin
#print axioms matrixElement_error_le
#print axioms forward_matrix_tangent_error_le
#print axioms backward_matrix_tangent_error_le
#print axioms forward_matrix_tangent_error_unit_ball
#print axioms backward_matrix_tangent_error_unit_ball

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMatrixTangent

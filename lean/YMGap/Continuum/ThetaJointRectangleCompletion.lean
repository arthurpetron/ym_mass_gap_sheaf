/-
# Actual completed parity rectangles meet the original theta box

The unbalanced signed odd series are completed with their actual boundaries.
The separately completed endpoint-frequency rectangle equals the signed
numerator of the SAME bare theta series. At y=1 the value rectangle equals
that series squared. The finite rectangle lives at N+1 whereas the box lives
at N: this offset is paid by the rectangle's constructed Cauchy proof, not
erased by a finite equality. No Jacobi radial-cost limit pin, curvature
ceiling or physical estimate is assumed or proved here.
-/

import YMGap.Continuum.ThetaOddSeriesCompletion
import YMGap.Continuum.ThetaJointFrequencyCompletion
import YMGap.Continuum.ThetaParityDiamondTail

namespace YMGap.Continuum.ThetaJointRectangleCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaEvenSeriesCompletion
open YMGap.Continuum.ThetaOddSeriesCompletion
open YMGap.Continuum.ThetaJointFrequencyCompletion
open YMGap.Continuum.ThetaParityDiamondTail
open YMGap.Continuum.ThetaParityWeights
open YMGap.Continuum.ThetaParityConvolution (signedIndices boxIndices)
open YMGap.Continuum.ThetaJointValuePin (theta_box_endpoint_value_pin)
open YMGap.Continuum.JacobiTripleProductOnBox
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ g)

/-- Actual parity value rectangle at the endpoint y=1. -/
def valueRectangleCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  CReal.add
    (CReal.mul (evenCReal hw0 hw1 hx0 hx1) (evenCReal hw0 hw1 (by decide) (Q'.le_refl' 1)))
    (CReal.mul (CReal.ofQ' w)
      (CReal.mul (oddSignedCReal hw0 hw1 hx0 hx1)
        (oddSignedCReal hw0 hw1 (by decide) (Q'.le_refl' 1))))

/-- Actual parity endpoint-frequency rectangle, independently completed. -/
def frequencyRectangleCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  CReal.add
    (CReal.mul (evenCReal hw0 hw1 hx0 hx1) (evenEndpointCReal hw0 hw1))
    (CReal.mul (CReal.ofQ' w)
      (CReal.mul (oddSignedCReal hw0 hw1 hx0 hx1) (oddSignedEndpointCReal hw0 hw1)))

private theorem frequencyRectangle_approx_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (frequencyRectangleCReal hw0 hw1 hx0 hx1).approx N ≈
      listQSum (evenThetaTerm w x) (signedIndices N)*
        listQSum (fun k : Int => Q'.ofNat ((2*k).natAbs*(2*k).natAbs)*
          w^(2*(k.natAbs*k.natAbs))) (signedIndices N) +
      w*(listQSum (oddThetaTerm w x) (signedIndices N)*
        listQSum (fun k : Int => Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)*
          w^(2*(k*(k+1)).toNat)) (signedIndices N)) :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ (listQSum_congr (fun _ => Q'.mul_comm_eqv _ _) _))
    (Q'.mul_eqv_congr_left w _ _
      (Q'.mul_eqv_congr_left _ _ _ (listQSum_congr (fun _ => Q'.mul_comm_eqv _ _) _)))

private theorem equiv_of_succ_close (A B : CReal) (cutoff : Q' → Nat)
    (hclose : ∀ epsilon, (0 : Q') < epsilon → ∀ N, cutoff epsilon ≤ N →
      Q'.abs (A.approx (N+1) + -B.approx N) ≤ epsilon) : CReal.Equiv A B := by
  intro epsilon he
  let delta := HalfPow.half*epsilon
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos epsilon he
  obtain ⟨M, hM⟩ := A.cauchy delta hd
  refine ⟨max M (cutoff delta), fun N hN => ?_⟩
  have hm : M ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have ht : cutoff delta ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hs := hM N (N+1) hm (by omega)
  have hc := hclose delta hd N ht
  have hf := ExpNeg.le_add_of_abs_sub_le hc
  have hb := ExpNeg.le_add_of_abs_sub_le
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hc)
  have pay : ∀ z : Q', (z+delta)+delta ≈ z+epsilon := fun z =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z delta delta)
      (Q'.add_eqv_congr_left z _ _ (ExpNeg.two_halves epsilon))
  exact ⟨Q'.le_trans' _ _ _ hs.1
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ delta hf) (Q'.le_of_eqv (pay _))),
    Q'.le_trans' _ _ _ hb
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ delta hs.2) (Q'.le_of_eqv (pay _)))⟩

/-- Completed ACTUAL parity value rectangle at y=1 equals the original
full bare theta series square, with the central one and factor two retained. -/
theorem completed_value_rectangle_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (valueRectangleCReal hw0 hw1 hx0 hx1)
      (CReal.mul (fullThetaSeries hw0 hw1 hx1 hx0) (fullThetaSeries hw0 hw1 hx1 hx0)) := by
  apply equiv_of_succ_close _ _ (rectangleTailCutoff w)
  intro epsilon he N hN
  have hp : ((fullThetaSeries hw0 hw1 hx1 hx0).approx N)*
      ((fullThetaSeries hw0 hw1 hx1 hx0).approx N) ≈
      listQSum (thetaCell w x 1) (boxIndices N) :=
    Q'.eqv_trans _ _ _ (mul_congr (fullThetaSeries_approx hw0 hw1 hx1 hx0 N)
      (fullThetaSeries_approx hw0 hw1 hx1 hx0 N))
      (Q'.eqv_symm (theta_box_endpoint_value_pin w x N))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hp))))
    (theta_box_factored_error_close hw0 hw1 hx0 hx1 (by decide) (Q'.le_refl' 1) he N hN)

/-- Completed ACTUAL endpoint-frequency rectangle equals the original
signed numerator assembled from separately constructed value/first/angular
series. This supplies the same-series pin, not a Jacobi radial-cost pin. -/
theorem completed_frequency_rectangle_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (frequencyRectangleCReal hw0 hw1 hx0 hx1)
      (frequencyNumeratorCReal hw0 hw1 hx0 hx1) := by
  apply equiv_of_succ_close _ _ (rectangleTailCutoff w)
  intro epsilon he N hN
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
    (Q'.add_eqv_congr' (frequencyRectangle_approx_pin hw0 hw1 hx0 hx1 (N+1))
      (Q'.neg_eqv_congr _ _ (frequencyNumeratorCReal_box_pin hw0 hw1 hx0 hx1 N)))))
    (frequency_box_factored_error_close hw0 hw1 hx0 hx1 he N hN)

end YMGap.Continuum.ThetaJointRectangleCompletion

#print axioms YMGap.Continuum.ThetaJointRectangleCompletion.valueRectangleCReal
#print axioms YMGap.Continuum.ThetaJointRectangleCompletion.frequencyRectangleCReal
#print axioms YMGap.Continuum.ThetaJointRectangleCompletion.completed_value_rectangle_pin
#print axioms YMGap.Continuum.ThetaJointRectangleCompletion.completed_frequency_rectangle_pin

/-
# Actual Haar cutoff control with the negative completed square retained

The actual cubic-minus-omitted estimate is applied BEFORE taking the full
cancelled remainder's upper bound. It is not a comparison of mixed absolute
leaf budgets. The original angular-pair debt and the negative completed
square remain; the existing regularized projection gain is paid from that
same square. No interacting-variance or changing-family estimate is assumed.
-/

import YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
import YMGap.Continuum.SU2QuaternionCompleteRemainderProjection

namespace YMGap.Continuum.SU2QuaternionCompleteRemainderHaarProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
open YMGap.Continuum.SU2QuaternionCompleteRemainderProjection
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)

local infix:50 " ≈ " => Q'.eqv

/-- Both omitted costs use actual Haar norms; cubic and angular costs remain. -/
def haarSquareCeiling (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let h := (1 : Q')-w
  (HalfPow.half*(h*h))*(squareQuarter*sourceSquareMass tail q f) +
    sourceHaarErrorBudget tail w K q f +
      h*((h*h)*pairBudget tail q (polyMul q (angularSquare tail f)))

/-- The COMPLETE original remainder, including its negative completed square.
Only the actual cubic-minus-omitted numerator is bounded by the new norm cap. -/
theorem completeRemainder_le_haar_completedSquare (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    completeRemainder tail w K q f ≤ haarSquareCeiling tail w K q f -
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
        squareCompletionMass tail q f := by
  let h := (1 : Q')-w
  let alpha := HalfPow.half*(h*h)
  let S := squareCompletionMass tail q f
  let B := sourceSquareMass tail q f
  let A := alpha*(quarter*B-S)
  let E := sourceHaarErrorBudget tail w K q f
  let R := pairRemainder tail w K q (polyMul q (angularSquare tail f))
  let T := (h*h)*pairBudget tail q (polyMul q (angularSquare tail f))
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have he := sourceError_le_haar tail hw0 (Q'.le_of_lt hw1) K q f hq hf
  have hr := neg_pairRemainder_le_quadratic tail hw0 hw1 K hK
    q (polyMul q (angularSquare tail f))
  have hscaled : -(h*R) ≤ h*T :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.neg (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.neg (.var 1)))
        (by decide) (fun | 0 => h | _ => R)))
      (Q'.mul_le_mul_of_nonneg_left _ _ h hr hh)
  have hsum := Q'.add_le_add (Q'.add_le_add_left A _ _ he) hscaled
  have hleft : completedRemainder tail w K q f ≈
      (A+(sourceCubic tail w q f-sourceOmitted tail w K q f)) + -(h*R) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
        (.neg (.mul (.var 3) (.var 4))))
      (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.neg (.mul (.var 3) (.var 4))))
      (by decide) (fun
        | 0 => A
        | 1 => sourceCubic tail w q f
        | 2 => sourceOmitted tail w K q f
        | 3 => h
        | _ => R)
  have hright : (A+E)+h*T ≈ haarSquareCeiling tail w K q f-alpha*S :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0)
        (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))) (.var 4)) (.var 5))
      (.add (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.var 4)) (.var 5)) (.neg (.mul (.var 0) (.var 3))))
      (by decide) (fun
        | 0 => alpha
        | 1 => quarter
        | 2 => B
        | 3 => S
        | 4 => E
        | _ => h*T)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (completeRemainder_square_completion tail w K q f hq hf))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hright)))

/-- The EXISTING computed gain is retained on the SAME completed square.
No old mixed absolute budget is compared with the new actual norm bound. -/
theorem completeRemainder_le_haar_projectionCeiling (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (epsilon : Q') (hε : (0 : Q') < epsilon) :
    completeRemainder tail w K q f ≤ haarSquareCeiling tail w K q f -
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
        projectionGain tail q f epsilon hε hq hf := by
  let alpha := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have halpha : (0 : Q') ≤ alpha :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hgain := projectionGain_le_squareCompletionMass tail q f epsilon hε hq hf
  exact Q'.le_trans' _ _ _
    (completeRemainder_le_haar_completedSquare tail hw0 hw1 K hK q f hq hf)
    (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg
      (Q'.mul_le_mul_of_nonneg_left _ _ alpha hgain halpha)))

#print axioms haarSquareCeiling
#print axioms completeRemainder_le_haar_completedSquare
#print axioms completeRemainder_le_haar_projectionCeiling

end YMGap.Continuum.SU2QuaternionCompleteRemainderHaarProjection

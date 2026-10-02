/-
# Actual cubic Casimir norms with the existing projection gain retained

The negative cubic remainder is a positive form. Young's inequality pays its
mixed source term with three actual diagonals, each bounded by h^3/6 times
the literal FULL third Casimir moment H[(Cp)(C^2p)]. The omitted-mode Haar
bound is unchanged. Both estimates are inserted into the COMPLETE original
remainder before retaining the EXISTING projection gain.

No active-only replacement, comparison with the old absolute-leaf budget,
interacting-variance calibration or useful changing-family rate is asserted.
-/

import YMGap.Continuum.SU2QuaternionCyclicCasimirCube
import YMGap.Continuum.SU2QuaternionCyclicCubicOperator
import YMGap.Continuum.SU2QuaternionCompleteRemainderProjection

namespace YMGap.Continuum.SU2QuaternionCyclicSobolevProjection

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
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
open YMGap.Continuum.SU2QuaternionCyclicCasimirCube
open YMGap.Continuum.SU2QuaternionCyclicCubicOperator
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
open YMGap.Continuum.SU2QuaternionCompleteRemainderProjection
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Computed FULL third Casimir costs, not absolute leaf coefficients. -/
def sourceSobolevCubicBudget (tail : Nat) (w : Q') (q f : RatPoly) : Q' :=
  (sixth*((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)))*
    (HalfPow.half*(thirdMoment tail q+thirdMoment tail (polyMul q (polyMul f f)))+
      thirdMoment tail (polyMul q f))

/-- The complete signed source cubic term is paid by actual third moments. -/
theorem sourceCubic_le_thirdMoments (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceCubic tail w q f ≤ sourceSobolevCubicBudget tail w q f := by
  let c := sixth*((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))
  have hqf := supported_polyMul hq hf
  have hqf2 := supported_polyMul hq (supported_polyMul hf hf)
  have hsum := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (Q'.add_le_add
        (neg_pairCubic_diagonal_le_thirdMoment tail hw0 (Q'.le_of_lt hw1) q hq)
        (neg_pairCubic_diagonal_le_thirdMoment tail hw0 (Q'.le_of_lt hw1)
          (polyMul q (polyMul f f)) hqf2)) HalfPow.half_nonneg)
    (neg_pairCubic_diagonal_le_thirdMoment tail hw0 (Q'.le_of_lt hw1) (polyMul q f) hqf)
  have hcollect : HalfPow.half*(c*thirdMoment tail q+
      c*thirdMoment tail (polyMul q (polyMul f f)))+
      c*thirdMoment tail (polyMul q f) ≈ sourceSobolevCubicBudget tail w q f :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.var 4)))
      (.mul (.var 1) (.add (.mul (.var 0) (.add (.var 2) (.var 3))) (.var 4)))
      (by decide) (fun
        | 0 => HalfPow.half
        | 1 => c
        | 2 => thirdMoment tail q
        | 3 => thirdMoment tail (polyMul q (polyMul f f))
        | _ => thirdMoment tail (polyMul q f))
  exact Q'.le_trans' _ _ _ (sourceCubic_le_diagonalNorms tail hw0 hw1 q f hq hf)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcollect))

/-- Actual cubic norm cap plus the existing omitted-mode Haar cap. -/
def sourceSobolevErrorBudget (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  sourceSobolevCubicBudget tail w q f + omittedRate w K *
    (HalfPow.half*(H (tail+1) (polyMul q q)+
      H (tail+1) (polyMul (polyMul q (polyMul f f)) (polyMul q (polyMul f f))))+
      H (tail+1) (polyMul (polyMul q f) (polyMul q f)))

/-- No numerical ordering against the old absolute budget is needed. -/
theorem sourceError_le_sobolev (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceCubic tail w q f-sourceOmitted tail w K q f ≤
      sourceSobolevErrorBudget tail w K q f := by
  have hc := sourceCubic_le_thirdMoments tail hw0 hw1 q f hq hf
  have ho := Q'.add_le_add
    (neg_pairOmitted_le_haar tail hw0 (Q'.le_of_lt hw1) K q (polyMul q (polyMul f f)) hq
      (supported_polyMul hq (supported_polyMul hf hf)))
    (pairOmitted_diagonal_le_haar tail hw0 (Q'.le_of_lt hw1) K (polyMul q f)
      (supported_polyMul hq hf))
  have hleft : sourceCubic tail w q f-sourceOmitted tail w K q f ≈
      sourceCubic tail w q f+(-(pairOmitted tail w K q (polyMul q (polyMul f f)))+
        pairOmitted tail w K (polyMul q f) (polyMul q f)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.add (.neg (.var 1)) (.var 2))) (by decide)
      (fun
        | 0 => sourceCubic tail w q f
        | 1 => pairOmitted tail w K q (polyMul q (polyMul f f))
        | _ => pairOmitted tail w K (polyMul q f) (polyMul q f))
  have hright : sourceSobolevCubicBudget tail w q f+
      (HalfPow.half*(omittedRate w K*(H (tail+1) (polyMul q q)+
        H (tail+1) (polyMul (polyMul q (polyMul f f)) (polyMul q (polyMul f f)))))+
        omittedRate w K*H (tail+1) (polyMul (polyMul q f) (polyMul q f))) ≈
      sourceSobolevErrorBudget tail w K q f :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.mul (.var 1) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 4))))
      (.add (.var 0) (.mul (.var 2) (.add (.mul (.var 1) (.var 3)) (.var 4))))
      (by decide) (fun
        | 0 => sourceSobolevCubicBudget tail w q f
        | 1 => HalfPow.half
        | 2 => omittedRate w K
        | 3 => H (tail+1) (polyMul q q)+
          H (tail+1) (polyMul (polyMul q (polyMul f f)) (polyMul q (polyMul f f)))
        | _ => H (tail+1) (polyMul (polyMul q f) (polyMul q f)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ (Q'.add_le_add hc ho) (Q'.le_of_eqv hright))

/-- Cubic Sobolev norms and Haar cutoff norms; the angular pair debt remains. -/
def sobolevSquareCeiling (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let h := (1 : Q')-w
  (HalfPow.half*(h*h))*(squareQuarter*sourceSquareMass tail q f) +
    sourceSobolevErrorBudget tail w K q f +
      h*((h*h)*pairBudget tail q (polyMul q (angularSquare tail f)))

/-- The COMPLETE original remainder retains its negative completed square. -/
theorem completeRemainder_le_sobolev_completedSquare (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    completeRemainder tail w K q f ≤ sobolevSquareCeiling tail w K q f -
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*squareCompletionMass tail q f := by
  let h := (1 : Q')-w
  let alpha := HalfPow.half*(h*h)
  let S := squareCompletionMass tail q f
  let B := sourceSquareMass tail q f
  let A := alpha*(quarter*B-S)
  let E := sourceSobolevErrorBudget tail w K q f
  let R := pairRemainder tail w K q (polyMul q (angularSquare tail f))
  let T := (h*h)*pairBudget tail q (polyMul q (angularSquare tail f))
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have he := sourceError_le_sobolev tail hw0 hw1 K q f hq hf
  have hr := neg_pairRemainder_le_quadratic tail hw0 hw1 K hK
    q (polyMul q (angularSquare tail f))
  have hscaled : -(h*R) ≤ h*T :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.neg (.mul (.var 0) (.var 1))) (.mul (.var 0) (.neg (.var 1)))
      (by decide) (fun | 0 => h | _ => R)))
      (Q'.mul_le_mul_of_nonneg_left _ _ h hr hh)
  have hsum := Q'.add_le_add (Q'.add_le_add_left A _ _ he) hscaled
  have hleft : completedRemainder tail w K q f ≈
      (A+(sourceCubic tail w q f-sourceOmitted tail w K q f)) + -(h*R) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 2))) (.neg (.mul (.var 3) (.var 4))))
      (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2)))) (.neg (.mul (.var 3) (.var 4))))
      (by decide) (fun
        | 0 => A
        | 1 => sourceCubic tail w q f
        | 2 => sourceOmitted tail w K q f
        | 3 => h
        | _ => R)
  have hright : (A+E)+h*T ≈ sobolevSquareCeiling tail w K q f-alpha*S :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))) (.var 4)) (.var 5))
      (.add (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 4)) (.var 5))
        (.neg (.mul (.var 0) (.var 3))))
      (by decide) (fun | 0 => alpha | 1 => quarter | 2 => B | 3 => S | 4 => E | _ => h*T)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (completeRemainder_square_completion tail w K q f hq hf))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hright)))

/-- SAME square and EXISTING computed gain; no positivity of the gain size assumed. -/
theorem completeRemainder_le_sobolev_projectionCeiling (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (epsilon : Q') (hε : (0 : Q') < epsilon) :
    completeRemainder tail w K q f ≤ sobolevSquareCeiling tail w K q f -
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
        projectionGain tail q f epsilon hε hq hf := by
  let alpha := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have halpha : (0 : Q') ≤ alpha :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hgain := projectionGain_le_squareCompletionMass tail q f epsilon hε hq hf
  exact Q'.le_trans' _ _ _
    (completeRemainder_le_sobolev_completedSquare tail hw0 hw1 K hK q f hq hf)
    (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg
      (Q'.mul_le_mul_of_nonneg_left _ _ alpha hgain halpha)))

#print axioms sourceSobolevCubicBudget
#print axioms sourceCubic_le_thirdMoments
#print axioms sourceSobolevErrorBudget
#print axioms sourceError_le_sobolev
#print axioms sobolevSquareCeiling
#print axioms completeRemainder_le_sobolev_completedSquare
#print axioms completeRemainder_le_sobolev_projectionCeiling

end YMGap.Continuum.SU2QuaternionCyclicSobolevProjection

/-
# The coupled score in the finite reciprocal gradient

The score A*Db-b*DA is kept intact. A certificate comparing its square
with L^2*A^2*Noise, together with the certified finite multiplier A*G,
bounds (G*score)^2 by L^2*Noise without division or a lower floor for A.
The exact reciprocal gradient consists of this coupled term and one
explicit finite reciprocal correction. Every weighted form uses the SAME
weight. No Noise/surviving-variance comparison or scaling limit is asserted.
-/

import YMGap.Continuum.QuaternionHaarReciprocalRatioGradientBound

namespace YMGap.Continuum.QuaternionHaarConditionalScoreGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left sumBound)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal reciprocal_supported)
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity
open YMGap.Continuum.QuaternionHaarReciprocalRatioGradientBound
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

local infix:50 " ≈ " => Q'.eqv

/-- The vacuum-subtracted derivative, before any reciprocal approximation. -/
def conditionalScore (i j : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (polyMul A (angularDerivative i j b))
    (polyNeg (polyMul b (angularDerivative i j A)))

/-- The literal finite reciprocal correction, not a new permanent DA cost. -/
def reciprocalScoreCorrection (i j : Nat) (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) : RatPoly :=
  polyMul b (polyMul
    (polyAdd (reciprocal A u hu k)
      (polyNeg (polyMul A (reciprocalSlope A u hu k))))
    (angularDerivative i j A))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- A nonconstant positive noise budget is transported through a certified
multiplier. The factor A^2 cancels algebraically, never by division. -/
def scoreMultiplierCertificate {blocks : Nat} {A S noise J : RatPoly} {L : Q'}
    (hJ : SupportedQuaternionBlocks blocks J)
    (PN : Certificate blocks noise)
    (PS : Certificate blocks (polyAdd
      (polyMul (cap (L*L)) (polyMul (polyMul A A) noise))
      (polyNeg (polyMul S S))))
    (M : Certificate blocks (polyAdd polyOne
      (polyNeg (polyMul (polyMul A J) (polyMul A J))))) :
    Certificate blocks (polyAdd (polyMul (cap (L*L)) noise)
      (polyNeg (polyMul (polyMul J S) (polyMul J S)))) := by
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (cap (L*L)) noise)
        (polyNeg (polyMul (polyMul J S) (polyMul J S))))
      (polyAdd
        (polyMul (polyMul J J)
          (polyAdd (polyMul (cap (L*L)) (polyMul (polyMul A A) noise))
            (polyNeg (polyMul S S))))
        (polyMul (polyMul (cap (L*L)) noise)
          (polyAdd polyOne
            (polyNeg (polyMul (polyMul A J) (polyMul A J)))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))
      (.add
        (.mul (.mul (.var 2) (.var 2))
          (.add (.mul (.var 0) (.mul (.mul (.var 4) (.var 4)) (.var 1)))
            (.neg (.mul (.var 3) (.var 3)))))
        (.mul (.mul (.var 0) (.var 1))
          (.add (.const 1)
            (.neg (.mul (.mul (.var 4) (.var 2)) (.mul (.var 4) (.var 2)))))))
      (by decide) (fun | 0 => cap (L*L) | 1 => noise | 2 => J | 3 => S | _ => A)
  exact Certificate.ofCoeff hid
    (((Certificate.square J hJ).mul PS).add
      (((Certificate.constant blocks (L*L) (SumOfSquares.q_mul_self_nonneg L)).mul PN).mul M))

/-- Exact cancellation-preserving Leibniz rule for the finite reciprocal. -/
theorem reciprocal_score_cleared_derivative (i j : Nat) (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv
      (polyMul A (angularDerivative i j (polyMul (reciprocal A u hu k) b)))
      (polyAdd (polyMul (reciprocal A u hu k) (conditionalScore i j A b))
        (reciprocalScoreCorrection i j A b u hu k)) := by
  refine (reciprocal_ratio_cleared_derivative i j A b u hu k).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.neg (.mul (.mul (.mul (.var 0) (.var 3)) (.var 4)) (.var 5))))
    (.add
      (.mul (.var 1) (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 4) (.var 5)))))
      (.mul (.var 4) (.mul
        (.add (.var 1) (.neg (.mul (.var 0) (.var 3)))) (.var 5))))
    (by decide) (fun
      | 0 => A | 1 => reciprocal A u hu k | 2 => angularDerivative i j b
      | 3 => reciprocalSlope A u hu k | 4 => b | _ => angularDerivative i j A)

/-- The leading coupled score is bounded by actual noise for EVERY degree,
with the original positive weight retained exactly. -/
theorem reciprocal_score_weighted_square_le {blocks : Nat}
    {W A S noise : RatPoly} {u L : Q'}
    (MW : Certificate blocks W) (hA : SupportedQuaternionBlocks blocks A)
    (hu : (0 : Q') < u) (PA : Certificate blocks A)
    (UA : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (PN : Certificate blocks noise)
    (PS : Certificate blocks (polyAdd
      (polyMul (cap (L*L)) (polyMul (polyMul A A) noise))
      (polyNeg (polyMul S S)))) (k : Nat) :
    quaternionHaar blocks (polyMul W
      (polyMul (polyMul (reciprocal A u hu k) S) (polyMul (reciprocal A u hu k) S))) ≤
      (L*L)*quaternionHaar blocks (polyMul W noise) := by
  have C := scoreMultiplierCertificate (reciprocal_supported hA u hu k) PN PS
    (reciprocalMultiplierSquareCertificate hu PA UA k)
  have hn := (MW.mul C).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd
        (polyMul W (polyMul (polyMul (reciprocal A u hu k) S)
          (polyMul (reciprocal A u hu k) S)))
        (polyMul W (polyAdd (polyMul (cap (L*L)) noise)
          (polyNeg (polyMul (polyMul (reciprocal A u hu k) S)
            (polyMul (reciprocal A u hu k) S))))))
      (polyMul (cap (L*L)) (polyMul W noise)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.var 0) (.add (.mul (.var 2) (.var 3)) (.neg (.var 1)))))
      (.mul (.var 2) (.mul (.var 0) (.var 3)))
      (by decide) (fun
        | 0 => W
        | 1 => polyMul (polyMul (reciprocal A u hu k) S) (polyMul (reciprocal A u hu k) S)
        | 2 => cap (L*L) | _ => noise)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left (L*L) _)))
      (quaternionHaar_polySmul blocks (L*L) _))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- The complete finite gradient pays the coupled noise and one explicit
reciprocal correction, instead of two permanent separate derivative debts. -/
theorem reciprocal_score_gradient_square_le {blocks i j : Nat}
    {W A b noise : RatPoly} {u L : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (MW : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A) (hb : SupportedQuaternionBlocks blocks b)
    (hu : (0 : Q') < u) (PA : Certificate blocks A)
    (UA : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (PN : Certificate blocks noise)
    (PS : Certificate blocks (polyAdd
      (polyMul (cap (L*L)) (polyMul (polyMul A A) noise))
      (polyNeg (polyMul (conditionalScore i j A b) (conditionalScore i j A b)))))
    (k : Nat) :
    let d := polyMul A (angularDerivative i j (polyMul (reciprocal A u hu k) b))
    let e := reciprocalScoreCorrection i j A b u hu k
    quaternionHaar blocks (polyMul W (polyMul d d)) ≤
      sumBound ((L*L)*quaternionHaar blocks (polyMul W noise))
        (quaternionHaar blocks (polyMul W (polyMul e e))) := by
  dsimp only
  have hdA := angularDerivative_supported_at hi hj hA
  have hdb := angularDerivative_supported_at hi hj hb
  have hG := reciprocal_supported hA u hu k
  have hS := supported_add (supported_polyMul hA hdb)
    (support_neg (supported_polyMul hb hdA))
  have he := supported_polyMul hb (supported_polyMul
    (supported_add hG (support_neg
      (supported_polyMul hA (reciprocalSlope_supported hA u hu k)))) hdA)
  have hm := reciprocal_score_weighted_square_le MW hA hu PA UA PN PS k
  have hid := reciprocal_score_cleared_derivative i j A b u hu k
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((hid.mul hid).mul_left W)))
    (weighted_square_add_bound MW (supported_polyMul hG hS) he hm
      (Q'.le_of_eqv (Q'.eqv_refl _)))

#print axioms conditionalScore
#print axioms reciprocalScoreCorrection
#print axioms scoreMultiplierCertificate
#print axioms reciprocal_score_cleared_derivative
#print axioms reciprocal_score_weighted_square_le
#print axioms reciprocal_score_gradient_square_le

end YMGap.Continuum.QuaternionHaarConditionalScoreGradient

/-
Relative derivative certificates pay the ORIGINAL reciprocal-gradient
correction in the SAME weighted source square.  The onset uses only the
relative derivative cap, window rate and tolerance, never an inverse source
norm.  Zero-norm sources are included.  This is finite fixed-window control,
not a spacing-uniform spectral estimate.
-/
import YMGap.Continuum.QuaternionHaarRelativeAngularBound
import YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection

namespace YMGap.Continuum.QuaternionHaarRelativeReciprocalCorrection

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
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)
open YMGap.Continuum.ClusterCount (ofNat_nonneg)

private theorem remainder_derivative (i j : Nat) (A : RatPoly)
    (u : Q') (hu : (0 : Q') < u) :
    RatPolyCoeffEqv (angularDerivative i j (remainder A u hu))
      (polyMul (cap (scale u hu)) (angularDerivative i j A)) := by
  change RatPolyCoeffEqv
    (angularDerivative i j (polyAdd (polySmul (scale u hu) A) (polyNeg polyOne))) _
  exact (angularDerivative_add i j _ _).trans
    (((angularDerivative_smul i j _ A).add
      ((angularDerivative_neg i j polyOne).trans
        ((RatPolyCoeffEqv.neg (angularDerivative_one i j)).trans
          (RatPolyCoeffEqv.refl polyZero)))).trans
      ((RatPolyCoeffEqv.add_zero _).trans (cap_mul_left _ _).symm))

/-- The certified upper window and relative cone construct |D(A/u-1)|<=c.
There is no lower terminal floor and no source-dependent derivative cap. -/
def remainderAngularInterval {blocks i j : Nat} {A : RatPoly} {u c : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (hA : SupportedQuaternionBlocks blocks A) (hu : (0 : Q') < u)
    (P : RelativeBound blocks i j A c)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A))) :
    Interval blocks (angularDerivative i j (remainder A u hu)) c := by
  let alpha := scale u hu
  let R := remainder A u hu
  let dA := angularDerivative i j A
  have ha := Q'.le_of_lt (scale_positive u hu)
  have hR : RatPolyCoeffEqv R (polyAdd (polyMul (cap alpha) A) (polyNeg polyOne)) :=
    ((cap_mul_left alpha A).symm.add (RatPolyCoeffEqv.refl _))
  have d := remainder_derivative i j A u hu
  have C := (remainderNegative hu U).smul c P.nonnegative
  have hC : RatPolyCoeffEqv (polySmul c (polyNeg R))
      (polyMul (cap c) (polyNeg (polyAdd (polyMul (cap alpha) A) (polyNeg polyOne)))) :=
    (cap_mul_left c _).symm.trans ((RatPolyCoeffEqv.neg hR).mul_left _)
  refine ⟨angularDerivative_supported_at hi hj (remainder_supported hA u hu),
    P.nonnegative, ?_, ?_⟩
  · have he := (hC.add (cap_mul_left alpha _).symm).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.neg (.add (.mul (.var 1) (.var 2)) (.neg (.const 1)))))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3)))))
        (.add (.var 0) (.neg (.mul (.var 1) (.var 3))))
        (by decide) (fun | 0 => cap c | 1 => cap alpha | 2 => A | _ => dA))
    exact .ofCoeff
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg d)).trans he.symm)
      (C.add (P.upper.smul alpha ha))
  · have he := (hC.add (cap_mul_left alpha _).symm).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.neg (.add (.mul (.var 1) (.var 2)) (.neg (.const 1)))))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3))))
        (.add (.var 0) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => cap c | 1 => cap alpha | 2 => A | _ => dA))
    exact .ofCoeff (((RatPolyCoeffEqv.refl _).add d).trans he.symm)
      (C.add (P.lower.smul alpha ha))

/-- The signed source and weight are unchanged.  Both zero source norm and
zero relative derivative cap are covered without division. -/
theorem reciprocalScoreCorrection_relative_square_le
    {blocks i j : Nat} {W A b : RatPoly} {u rho c : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks) (M : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A) (hb : SupportedQuaternionBlocks blocks b)
    (hu : (0 : Q') < u) (P : RelativeBound blocks i j A c)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (S : SquareBound blocks (remainder A u hu) (rho*rho)) (k : Nat) :
    let e := reciprocalScoreCorrection i j A b u hu (k+1)
    quaternionHaar blocks (polyMul W (polyMul e e)) ≤
      (((Q'.ofNat (k+1)*Q'.ofNat (k+1))*(rho^k*rho^k))*(c*c))*
        quaternionHaar blocks (polyMul W (polyMul b b)) := by
  dsimp only
  have D := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (remainderAngularInterval hi hj hA hu P U)
  have hbD := weighted_multiplier_square_le M D hb
  have hbD' := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff
      (((RatPolyCoeffEqv.mul_comm b _).mul (RatPolyCoeffEqv.mul_comm b _)).mul_left W))) hbD
  have hf : (0 : Q') ≤ (Q'.ofNat (k+1)*Q'.ofNat (k+1))*(rho^k*rho^k) :=
    Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (ofNat_nonneg (k+1)) (ofNat_nonneg (k+1)))
    (SumOfSquares.q_mul_self_nonneg (rho^k))
  exact Q'.le_trans' _ _ _ (reciprocalScoreCorrection_square_le hi hj M hA hb hu S k)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hbD' hf)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

#print axioms remainderAngularInterval
#print axioms reciprocalScoreCorrection_relative_square_le

end YMGap.Continuum.QuaternionHaarRelativeReciprocalCorrection

/-
# Original-weight prediction floor from relative angular control

The predictor may be any supported polynomial independent of the selected
head quaternion. Signed full-weight Ward identities and positive weighted
squares yield a floor without a global density minimum or fiber reciprocal.
The physical caller supplies the actual plaquette kinematics and constructs
the relative derivative certificates for the SAME weight.
-/

import YMGap.Continuum.RationalRelativeWardPrediction
import YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.QuaternionHaarRelativePredictionFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
open YMGap.Continuum.RationalRelativeWardPrediction
open YMGap.Continuum.QuaternionHaarDensityVariance

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    H blocks (polyNeg p) ≈ -(H blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | x::xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv x.2 (quaternionHaarMono blocks x.1))
        (haar_neg blocks xs)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- The positive weighted square `(t*a-b)^2` retains all mixed signs. -/
theorem weighted_square_young {blocks : Nat} {W a b : RatPoly}
    (P : Certificate blocks W) (ha : SupportedQuaternionBlocks blocks a)
    (hb : SupportedQuaternionBlocks blocks b) (t : Q') :
    2*t*H blocks (polyMul W (polyMul a b)) ≤
      t*t*H blocks (polyMul W (polyMul a a)) +
        H blocks (polyMul W (polyMul b b)) := by
  let G := weightedGNSData blocks W P
  have h := G.toPreInnerForm.nonnegQuad t (-1) ⟨a,ha⟩ ⟨b,hb⟩
  have hA : G.B ⟨a,ha⟩ ⟨a,ha⟩ ≈ H blocks (polyMul W (polyMul a a)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hB : G.B ⟨a,ha⟩ ⟨b,hb⟩ ≈ H blocks (polyMul W (polyMul a b)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hF : G.B ⟨b,hb⟩ ⟨b,hb⟩ ≈ H blocks (polyMul W (polyMul b b)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have he := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (t*t) _ _ hA)
      (Q'.mul_eqv_congr_left (2*(t*(-1))) _ _ hB))
    (Q'.mul_eqv_congr_left ((-1)*(-1)) _ _ hF)
  have hn := Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
        (.mul (.mul (.const 2) (.mul (.var 0) (.const (-1)))) (.var 2)))
        (.mul (.mul (.const (-1)) (.const (-1))) (.var 3)))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 3))
        (.neg (.mul (.mul (.const 2) (.var 0)) (.var 2))))
      (by decide) (fun
        | 0 => t
        | 1 => H blocks (polyMul W (polyMul a a))
        | 2 => H blocks (polyMul W (polyMul a b))
        | _ => H blocks (polyMul W (polyMul b b))))))

/-- Kinematics is tested under the full original density, not bare Haar. -/
theorem kinematic_mass {blocks : Nat} (W f : RatPoly)
    (hkin : HaarCarrierEqv blocks (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f)))) :
    H blocks (polyMul W (angularSquare f)) + H blocks (polyMul W (polyMul f f)) ≈
      4*H blocks W := by
  have he : H blocks (polyMul W (angularSquare f)) ≈
      4*H blocks W + -(H blocks (polyMul W (polyMul f f))) :=
    Q'.eqv_trans _ _ _ (hkin W) (Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => W | 1 => cap 4 | _ => polyMul f f)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left 4 W))
            (quaternionHaar_polySmul blocks 4 W)) (haar_neg blocks _))))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => 4*H blocks W | _ => H blocks (polyMul W (polyMul f f))))

/-- Every supported head-independent polynomial predictor pays the explicit
same-weight floor. The conclusion is partition-cleared and division-free. -/
theorem raw_prediction_floor {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hlinear : HasQuaternionBlockDegree 0 1 f)
    (hkin : HaarCarrierEqv (tail+1) (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))))
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hfree : HasQuaternionBlockDegree 0 0 q) :
    H (tail+1) W ≤ predictionFactor C * H (tail+1)
      (polyMul W (polyMul (polyAdd f (polySmul (-1) q))
        (polyAdd f (polySmul (-1) q)))) := by
  let g := polyAdd f (polySmul (-1) q)
  let E := H (tail+1) (polyMul W (angularSquare f))
  let F := H (tail+1) (polyMul W (polyMul f f))
  let A := H (tail+1) (polyMul W (polyMul g g))
  let B := H (tail+1) (polyMul W (polyMul g f))
  let Rf := generalizedResidual tail W f f
  let Rg := generalizedResidual tail W g f
  have hg : SupportedQuaternionBlocks (tail+1) g :=
    supported_add hf (polySmul_supported hq (-1))
  have hwf : E+Rf ≈ 3*F := Q'.eqv_trans _ _ _ (self_ward tail W f hlinear)
    (Q'.mul_eqv_congr_left 3 _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W f f)))
  have hFE : 3*F ≤ 2*(1+C*C)*E := square_le_energy C E F Rf hC hwf
    (residual_upper_scaled hC R hf hf (2*(C*C)))
  have hwg : E+Rg ≈ 3*B := Q'.eqv_trans _ _ _
    (independent_shift_ward tail W f q hlinear hfree)
    (Q'.mul_eqv_congr_left 3 _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W g f)))
  have hy : -(2*Rg) ≤ 6*(C*C)*A+E := by
    have hh := residual_lower_scaled hC R hg hf 1
    have hl : -(2*Rg) ≈ -(2*1*Rg) := Q'.neg_eqv_congr _ _
      (Q'.eqv_symm (Q'.mul_eqv_congr_right _ _ Rg (Q'.mul_one_eqv 2)))
    have hr : 6*(C*C)*A+(1*1)*E ≈ 6*(C*C)*A+E :=
      Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ E (by decide)) (Q'.one_mul_eqv E))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv hr))
  have hc := weighted_square_young (R 0 1 (by decide) (by decide)).positive
    hg hf (4*(1+C*C))
  have hEA := energy_le_prediction C E F A B Rg hFE hwg hy hc
  exact prediction_bound C E F A (H (tail+1) W) hFE hEA (kinematic_mass W f hkin)

/-- The explicit rational floor after cancellation of the SAME positive
original partition. There is no conditional/fiber normalization in the proof. -/
theorem normalized_prediction_floor {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hlinear : HasQuaternionBlockDegree 0 1 f)
    (hkin : HaarCarrierEqv (tail+1) (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))))
    (hZ : (0 : Q') < H (tail+1) W)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hfree : HasQuaternionBlockDegree 0 0 q) :
    predictionFloor C ≤ normalizedMoment (tail+1) W
      (polyMul (polyAdd f (polySmul (-1) q)) (polyAdd f (polySmul (-1) q))) hZ :=
  normalized_prediction_bound C _ _ hZ
    (raw_prediction_floor hC R hf hlinear hkin q hq hfree)

#print axioms weighted_square_young
#print axioms kinematic_mass
#print axioms raw_prediction_floor
#print axioms normalized_prediction_floor

end YMGap.Continuum.QuaternionHaarRelativePredictionFloor

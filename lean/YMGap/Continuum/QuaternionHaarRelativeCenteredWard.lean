/-
# Signed Ward control by relative derivatives of the SAME weight

The six signed derivative terms are bounded by positive-cone Young
certificates. Combining their lower bound with exact centered integration
by parts controls angular energy by the original interacting variance.
No minimum of the weight, independence, or replacement density is used.
-/

import YMGap.Continuum.QuaternionHaarRelativeAngularYoung
import YMGap.Continuum.QuaternionHaarCenteredLinearWard

namespace YMGap.Continuum.QuaternionHaarRelativeCenteredWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativeAngularYoung
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarCenteredLinearWard

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sixValue_affine (a : Q') (b : Nat → Nat → Q') :
    sixValue (fun i j => a + b i j) ≈ 6*a + sixValue b :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.add (.add (.var 0) (.var 2))
        (.add (.add (.var 0) (.var 3))
          (.add (.add (.var 0) (.var 4))
            (.add (.add (.var 0) (.var 5)) (.add (.var 0) (.var 6)))))))
    (.add (.mul (.const 6) (.var 0))
      (.add (.var 1) (.add (.var 2) (.add (.var 3)
        (.add (.var 4) (.add (.var 5) (.var 6)))))))
    (by decide) (fun
      | 0 => a
      | 1 => b 0 1
      | 2 => b 0 2
      | 3 => b 0 3
      | 4 => b 1 2
      | 5 => b 1 3
      | _ => b 2 3)

/-- A lower bound on the actual signed Ward residual. It does not assume
that the residual is nonnegative or that the weight ignores the head link. -/
theorem residual_lower {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f) (c : Q') :
    -(2 * centeredLinearWardResidual tail W f c) ≤
      6*(C*C)*H (tail+1) (polyMul W
        (polyMul (polyAdd f (polySmul (-c) polyOne))
          (polyAdd f (polySmul (-c) polyOne)))) +
        H (tail+1) (polyMul W (angularSquare f)) := by
  let a := polyAdd f (polySmul (-c) polyOne)
  let A := H (tail+1) (polyMul W (polyMul a a))
  let r := fun i j => H (tail+1)
    (polyMul (polyMul a (angularDerivative i j W)) (angularDerivative i j f))
  let e := fun i j => H (tail+1)
    (polyMul W (polyMul (angularDerivative i j f) (angularDerivative i j f)))
  have ha : SupportedQuaternionBlocks (tail+1) a :=
    supported_add hf (polySmul_supported (supported_one (tail+1)) (-c))
  have hp (i j : Nat) (hi : i < 4) (hj : j < 4) :
      -(2*r i j) ≤ (C*C)*A + e i j := by
    have hy := relative_young_lower (R i j hi hj) hC ha
      (angularDerivative_supported (Nat.zero_lt_succ tail) hi hj hf)
    have he : H (tail+1)
        (polyMul (angularDerivative i j W) (polyMul a (angularDerivative i j f))) ≈
        r i j := haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => angularDerivative i j W | 1 => a | _ => angularDerivative i j f))
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ he))) hy
  have hs := sixValue_mono _ _ hp
  have hl : -(2*centeredLinearWardResidual tail W f c) ≈
      sixValue (fun i j => -(2*r i j)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv 2 (sixValue r)))
      (Q'.eqv_trans _ _ _ (sixValue_mul_left (-2) r)
        (sixValue_congr _ _ (fun i j _ _ => Q'.neg_mul_eqv 2 (r i j))))
  have hr : sixValue (fun i j => (C*C)*A+e i j) ≈
      6*(C*C)*A + H (tail+1) (polyMul W (angularSquare f)) :=
    Q'.eqv_trans _ _ _ (sixValue_affine ((C*C)*A) e)
      (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.mul_assoc_eqv 6 (C*C) A))
        (Q'.eqv_symm (haar_six (tail+1) W
          (fun i j => polyMul (angularDerivative i j f) (angularDerivative i j f)))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

private theorem own_mean_square (tail : Nat) (W f : RatPoly)
    (P : Certificate (tail+1) W) (hf : SupportedQuaternionBlocks (tail+1) f)
    (hZ : (0 : Q') < H (tail+1) W) :
    let c := normalizedMoment (tail+1) W f hZ
    H (tail+1) (polyMul W (polyMul (polyAdd f (polySmul (-c) polyOne))
      (polyAdd f (polySmul (-c) polyOne)))) ≈
      H (tail+1) W * normalizedVariance (tail+1) W f hZ := by
  let c := normalizedMoment (tail+1) W f hZ
  let a := polyAdd f (polySmul (-c) polyOne)
  let A := H (tail+1) (polyMul W (polyMul a a))
  let Z := H (tail+1) W
  let v := normalizedVariance (tail+1) W f hZ
  let inv := Q'.recipPos Z hZ
  have hone : RatPolyCoeffEqv (polySmul 1 f) f := by
    intro weight
    exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 1 f) (Q'.one_mul_eqv _)
  have he : RatPolyCoeffEqv (shifted f c) a :=
    hone.add (RatPolyCoeffEqv.refl _)
  have hn : A*inv ≈ v := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ inv
      (haar_of_coeff ((he.symm.mul he.symm).mul_left W))) (own_mean_pin P hf hZ)
  have hc : A ≈ Z*(A*inv) := Q'.eqv_symm (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => Z | 1 => A | _ => inv))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv A)))
  exact Q'.eqv_trans _ _ _ hc (Q'.mul_eqv_congr_left Z _ _ hn)

/-- Relative derivative certificates control the centered angular energy in
the SAME interacting weight. The coefficient is independent of the weight's
minimum. All dependence on the supplied score bound C remains explicit. -/
theorem energy_le_variance {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hlinear : HasQuaternionBlockDegree 0 1 f)
    (hZ : (0 : Q') < H (tail+1) W) :
    H (tail+1) (polyMul W (angularSquare f)) ≤
      (6*(1+C*C)) * (H (tail+1) W * normalizedVariance (tail+1) W f hZ) := by
  let c := normalizedMoment (tail+1) W f hZ
  let E := H (tail+1) (polyMul W (angularSquare f))
  let V := H (tail+1) W * normalizedVariance (tail+1) W f hZ
  let S := centeredLinearWardResidual tail W f c
  have ha := own_mean_square tail W f (R 0 1 (by decide) (by decide)).positive hf hZ
  have hy : -(2*S) ≤ 6*(C*C)*V+E := Q'.le_trans' _ _ _
    (residual_lower hC R hf c)
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (6*(C*C)) _ _ ha) (Q'.eqv_refl E)))
  have hw : E+S ≈ 3*V := centered_linear_ward_own_mean tail W f hZ hlinear
  have hz : (0 : Q') ≤ (6*(1+C*C))*V + -E := by
    have hb := Q'.sub_nonneg_of_le hy
    have he : (6*(C*C)*V+E)+ -(-(2*S)) ≈
        6*(C*C)*V+2*(E+S)+ -E := poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 6) (.mul (.var 0) (.var 0))) (.var 1)) (.var 2))
        (.neg (.neg (.mul (.const 2) (.var 3)))))
      (.add (.add (.mul (.mul (.const 6) (.mul (.var 0) (.var 0))) (.var 1))
        (.mul (.const 2) (.add (.var 2) (.var 3)))) (.neg (.var 2)))
      (by decide) (fun | 0 => C | 1 => V | 2 => E | _ => S)
    exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_left 2 _ _ hw)) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.mul (.const 6) (.mul (.var 0) (.var 0))) (.var 1))
            (.mul (.const 2) (.mul (.const 3) (.var 1)))) (.neg (.var 2)))
          (.add (.mul (.mul (.const 6) (.add (.const 1) (.mul (.var 0) (.var 0)))) (.var 1))
            (.neg (.var 2)))
          (by decide) (fun | 0 => C | 1 => V | _ => E)))))
  exact Q'.le_of_sub_nonneg hz

#print axioms residual_lower
#print axioms energy_le_variance

end YMGap.Continuum.QuaternionHaarRelativeCenteredWard

/-
# Centered linear Ward identity under an arbitrary full weight

For a head-linear observable, angular integration by parts converts its
six-direction energy into three times its centered first moment.  The term
where the angular derivative hits the complete supplied weight is retained
with its actual sign.  The weight may depend on the selected quaternion
block; no positivity, independence, or estimate of the residual is used.
-/

import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.QuaternionHaarNormalizedMomentLinear

namespace YMGap.Continuum.QuaternionHaarCenteredLinearWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The signed term in which the angular derivative hits the complete weight. -/
def centeredLinearWardResidual (tail : Nat) (W f : RatPoly) (c : Q') : Q' :=
  sixValue (fun i j => H (tail+1)
    (polyMul (polyMul (polyAdd f (polySmul (-c) polyOne))
      (angularDerivative i j W)) (angularDerivative i j f)))

private theorem sixValue_add (a b : Nat → Nat → Q') :
    sixValue a + sixValue b ≈ sixValue (fun i j => a i j + b i j) :=
  poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | 5 => a 2 3
      | 6 => b 0 1 | 7 => b 0 2 | 8 => b 0 3
      | 9 => b 1 2 | 10 => b 1 3 | _ => b 2 3)

private theorem sixValue_neg (a : Nat → Nat → Q') :
    sixValue (fun i j => -(a i j)) ≈ -(sixValue a) := by
  exact poly_identity_of_normal_eq
    (.add (.neg (.var 0)) (.add (.neg (.var 1)) (.add (.neg (.var 2))
      (.add (.neg (.var 3)) (.add (.neg (.var 4)) (.neg (.var 5)))))))
    (.neg (.add (.var 0) (.add (.var 1) (.add (.var 2)
      (.add (.var 3) (.add (.var 4) (.var 5)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | _ => a 2 3)

private theorem plane_identity (tail : Nat) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (W f : RatPoly) (c : Q') :
    H (tail+1) (polyMul W
        (polyMul (angularDerivative i j f) (angularDerivative i j f))) +
      H (tail+1) (polyMul
        (polyMul (polyAdd f (polySmul (-c) polyOne)) (angularDerivative i j W))
        (angularDerivative i j f)) ≈
      -(H (tail+1) (polyMul
        (polyMul W (polyAdd f (polySmul (-c) polyOne)))
        (angularDerivative i j (angularDerivative i j f)))) := by
  let fc := polyAdd f (polySmul (-c) polyOne)
  let df := angularDerivative i j f
  let dW := angularDerivative i j W
  let ddf := angularDerivative i j df
  have hfc := angularDerivative_centered hi hj c f
  have hd : RatPolyCoeffEqv
      (polyMul (angularDerivative i j (polyMul W fc)) df)
      (polyAdd (polyMul (polyMul fc dW) df) (polyMul W (polyMul df df))) := by
    exact (((angularDerivative_mul i j W fc).trans
      ((RatPolyCoeffEqv.refl _).add (hfc.mul_left W))).mul_right df).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 3))
        (.add (.mul (.mul (.var 2) (.var 0)) (.var 3))
          (.mul (.var 1) (.mul (.var 3) (.var 3))))
        (by decide) (fun | 0 => dW | 1 => W | 2 => fc | _ => df))
  have hzero := quaternionHaar_weighted_angular_at
    (n := tail+1) (block := 0) (Nat.zero_lt_succ tail) hi hj (polyMul W fc) df
  simp only [Nat.mul_zero, Nat.zero_add] at hzero
  have hsum :
      (H (tail+1) (polyMul (polyMul fc dW) df) +
        H (tail+1) (polyMul W (polyMul df df))) +
          H (tail+1) (polyMul (polyMul W fc) ddf) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (haar_of_coeff hd)
          (quaternionHaar_append (tail+1) _ _))
        (Q'.eqv_refl _)))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (quaternionHaar_append (tail+1) _ _)) hzero)
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 0)) (.neg (.neg (.var 2))))
      (.add (.add (.var 0) (.var 1)) (.var 2)) (by decide)
      (fun | 0 => H (tail+1) (polyMul (polyMul fc dW) df)
           | 1 => H (tail+1) (polyMul W (polyMul df df))
           | _ => H (tail+1) (polyMul (polyMul W fc) ddf))) hsum

/-- Exact centered Ward identity.  The residual is deliberately signed and
retains the derivative of the full, possibly head-dependent weight. -/
theorem centered_linear_ward (tail : Nat) (W f : RatPoly) (c : Q')
    (hf : HasQuaternionBlockDegree 0 1 f) :
    H (tail+1) (polyMul W (angularSquare f)) +
        centeredLinearWardResidual tail W f c ≈
      3 * H (tail+1) (polyMul (polyMul W
        (polyAdd f (polySmul (-c) polyOne))) f) := by
  let energy := fun i j => H (tail+1) (polyMul W
    (polyMul (angularDerivative i j f) (angularDerivative i j f)))
  let residual := fun i j => H (tail+1) (polyMul
    (polyMul (polyAdd f (polySmul (-c) polyOne)) (angularDerivative i j W))
    (angularDerivative i j f))
  let second := fun i j => H (tail+1) (polyMul
    (polyMul W (polyAdd f (polySmul (-c) polyOne)))
    (angularDerivative i j (angularDerivative i j f)))
  have he := haar_six (tail+1) W
    (fun i j => polyMul (angularDerivative i j f) (angularDerivative i j f))
  have hp := sixValue_congr (fun i j => energy i j + residual i j)
    (fun i j => -(second i j))
    (fun _ _ hi hj => plane_identity tail hi hj W f c)
  have hs : sixValue second ≈
      (-3) * H (tail+1) (polyMul (polyMul W
        (polyAdd f (polySmul (-c) polyOne))) f) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (haar_six (tail+1)
        (polyMul W (polyAdd f (polySmul (-c) polyOne)))
        (fun i j => angularDerivative i j (angularDerivative i j f))))
      (Q'.eqv_trans _ _ _
        (linear_angularLaplacian (Nat.zero_lt_succ tail) f hf
          (polyMul W (polyAdd f (polySmul (-c) polyOne))))
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (-3) _ f))
          (quaternionHaar_polySmul (tail+1) (-3) _)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ (sixValue_add energy residual)
      (Q'.eqv_trans _ _ _ hp
        (Q'.eqv_trans _ _ _ (sixValue_neg second)
          (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hs)
            (poly_identity_of_normal_eq
              (.neg (.mul (.const (-3)) (.var 0)))
              (.mul (.const 3) (.var 0)) (by decide)
              (fun _ => H (tail+1) (polyMul (polyMul W
                (polyAdd f (polySmul (-c) polyOne))) f)))))))

/-- At the explicitly computed mean, the normalized centered cross is exactly
the normalized variance.  No positivity certificate for `W` is required;
only its supplied positive mass is inverted. -/
theorem normalized_centered_cross_own_mean (tail : Nat) (W f : RatPoly)
    (hZ : (0 : Q') < H (tail+1) W) :
    let c := normalizedMoment (tail+1) W f hZ
    normalizedMoment (tail+1) W
        (polyMul (polyAdd f (polySmul (-c) polyOne)) f) hZ ≈
      normalizedVariance (tail+1) W f hZ := by
  let c := normalizedMoment (tail+1) W f hZ
  have hpoly : RatPolyCoeffEqv
      (polyMul (polyAdd f (polySmul (-c) polyOne)) f)
      (polyAdd (polyMul f f) (polySmul (-c) f)) := by
    exact (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.var 0))
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 0)))
      (by decide) (fun | 0 => f | _ => polySmul (-c) polyOne)).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.polyMul_smul_left (-c) polyOne f).trans
          ((RatPolyCoeffEqv.one_mul f).smul (-c))))
  have hm := normalizedMoment_congr hZ hZ (RatPolyCoeffEqv.refl W) hpoly
  exact Q'.eqv_trans _ _ _ hm
    (Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (normalizedMoment_smul hZ))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.neg (.var 1)) (.var 1)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
          (by decide)
          (fun | 0 => normalizedMoment (tail+1) W (polyMul f f) hZ
               | _ => c))))

/-- Partition-cleared own-mean Ward identity.  Its right side is the mass of
the SAME full weight times its normalized variance; the signed residual on
the left remains unchanged. -/
theorem centered_linear_ward_own_mean (tail : Nat) (W f : RatPoly)
    (hZ : (0 : Q') < H (tail+1) W)
    (hf : HasQuaternionBlockDegree 0 1 f) :
    let c := normalizedMoment (tail+1) W f hZ
    H (tail+1) (polyMul W (angularSquare f)) +
        centeredLinearWardResidual tail W f c ≈
      3 * (H (tail+1) W * normalizedVariance (tail+1) W f hZ) := by
  let Z := H (tail+1) W
  let c := normalizedMoment (tail+1) W f hZ
  let cross := H (tail+1)
    (polyMul W (polyMul (polyAdd f (polySmul (-c) polyOne)) f))
  have hward := centered_linear_ward tail W f c hf
  have hwardCross :
      H (tail+1) (polyMul W (angularSquare f)) +
          centeredLinearWardResidual tail W f c ≈ 3 * cross := by
    exact Q'.eqv_trans _ _ _ hward
      (Q'.mul_eqv_congr_left 3 _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W
          (polyAdd f (polySmul (-c) polyOne)) f)))
  have hnorm := normalized_centered_cross_own_mean tail W f hZ
  have hcrossNorm : cross * Q'.recipPos Z hZ ≈
      normalizedVariance (tail+1) W f hZ := by
    simpa only [cross, Z, c, normalizedMoment] using hnorm
  have hclear : cross ≈ Z * normalizedVariance (tail+1) W f hZ := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2)))
          (by decide)
          (fun | 0 => Z | 1 => cross | _ => Q'.recipPos Z hZ))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left cross _ _ (Q'.mul_recipPos_eqv Z hZ))
          (Q'.mul_one_eqv cross))))
      (Q'.mul_eqv_congr_left Z _ _ hcrossNorm)
  exact Q'.eqv_trans _ _ _ hwardCross (Q'.mul_eqv_congr_left 3 _ _ hclear)

end YMGap.Continuum.QuaternionHaarCenteredLinearWard

#print axioms YMGap.Continuum.QuaternionHaarCenteredLinearWard.centeredLinearWardResidual
#print axioms YMGap.Continuum.QuaternionHaarCenteredLinearWard.centered_linear_ward
#print axioms YMGap.Continuum.QuaternionHaarCenteredLinearWard.normalized_centered_cross_own_mean
#print axioms YMGap.Continuum.QuaternionHaarCenteredLinearWard.centered_linear_ward_own_mean

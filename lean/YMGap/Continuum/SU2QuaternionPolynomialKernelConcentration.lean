/-
# Exact concentration of finite quaternion polynomial kernels

On the ORIGINAL one-block polynomial Haar carrier, b=(1+x0)/2 and
Z_m=H[b^m]. Three actual angular integration-by-parts identities and the
arbitrary-insertion sphere relation produce the exact recurrence and the
normalized squared-chord moment 6/(m+3). The positive normalizer is a
computable finite product, not an assumed positivity or integration field.

This is a finite input for polynomial-kernel approximation on the SAME
completed Point carrier. It does not integrate arbitrary continuous
functions, construct compact Haar, or prove MAIN retention or a mass gap.
-/

import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
import YMGap.Continuum.QPolyHaarPositiveSubstitution
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarDensityVariance

local infix:50 " ≈ " => Q'.eqv

private def half : Q' := Q'.mkPos 1 2 (by decide)
private def halfDegree (m : Nat) : Q' := Q'.mkPos (Int.ofNat m) 2 (by decide)
private abbrev H := quaternionHaar 1
private def sq (p : RatPoly) := polyMul p p
private def three (f : Nat → RatPoly) := polyAdd (f 1) (polyAdd (f 2) (f 3))

/-- Literal finite polynomial (1+x0)/2. -/
def kernelBase : RatPoly := polySmul half (polyAdd polyOne (polyVar 0))

/-- The existing finite RatPoly power, with no degree cutoff. -/
def kernelPower (m : Nat) : RatPoly := ratPolyPow kernelBase m

/-- The ORIGINAL one-block polynomial moment, not a new Haar field. -/
def kernelMoment (m : Nat) : Q' := H (kernelPower m)

private theorem hpvar {i : Nat} (hi : i < 4) : SupportedQuaternionBlocks 1 (polyVar i) :=
  (coordinateInterval (by simpa using hi)).support

theorem kernelPower_supported : ∀ m, SupportedQuaternionBlocks 1 (kernelPower m)
  | 0 => supported_one 1
  | m+1 => supported_polyMul (kernelPower_supported m)
      (polySmul_supported (supported_add (supported_one 1) (hpvar (by decide))) half)

/-- Constructed square certificate for every actual kernel weight. -/
def kernelPower_certificate : (m : Nat) → Certificate 1 (kernelPower m)
  | 0 => Certificate.one 1
  | m+1 => (kernelPower_certificate m).mul
      (Certificate.ofCoeff
        (((RatPolyCoeffEqv.one_smul polyOne).symm.add
          (RatPolyCoeffEqv.refl (polyVar 0))).smul half)
        (.smul half (by decide)
          (coordinateInterval (blocks:=1) (coordinate:=0) (by decide)).lower))

private theorem hneg (p : RatPoly) : H (polyNeg p) ≈ -H p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 1 (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => H p)))

private theorem hcap (c : Q') (p : RatPoly) : H (polyMul (cap c) p) ≈ c * H p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c p))
    (quaternionHaar_polySmul 1 c p)

private theorem hsub (p q : RatPoly) : H (polyAdd p (polyNeg q)) ≈ H p + -H q :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append 1 p (polyNeg q))
    (Q'.add_eqv_congr_left _ _ _ (hneg q))

private theorem base_double : RatPolyCoeffEqv (polySmul 2 kernelBase)
    (polyAdd polyOne (polyVar 0)) :=
  (RatPolyCoeffEqv.smul_assoc 2 half _).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : (2:Q')*half ≈ 1) _).trans
      (RatPolyCoeffEqv.one_smul _))

private def baseEnv (i : Nat) : RatPoly := if i=0 then kernelBase else polyZero
private def scalarExpr : PolyExpr := .add (.mul (.const 2) (.var 0)) (.neg (.const 1))

private theorem scalar_shape : RatPolyCoeffEqv (polyVar 0) (coeffEvalExpr baseEnv scalarExpr) := by
  have h := ((cap_mul_left 2 kernelBase).add
    (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.one_smul polyOne))).trans
      (base_double.add (RatPolyCoeffEqv.refl (polyNeg polyOne)))
  exact ((h.trans (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
    (by decide) (fun | 0 => polyOne | _ => polyVar 0))).symm)

private theorem angular_scalar (i : Nat) (hi : i < 4) (h0 : i ≠ 0) :
    HaarCarrierEqv 1 (angularDerivative 0 i (polyVar 0)) (polySmul (-1) (polyVar i)) := by
  have hz := ((ratDerivative_polyVar_ne i 0 h0).mul_left (polyVar 0)).trans
    (RatPolyCoeffEqv.mul_zero_right _)
  have hs := derivativeFactor_self_carrier 1 i 0 (by decide) hi (by decide)
  exact (HaarCarrierEqv.add (blocks:=1) (RatPolyCoeffEqv.haarCarrier hz)
    (HaarCarrierEqv.smul (-1) hs)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _))

private theorem angular_coordinate (i : Nat) (hi : i < 4) (h0 : i ≠ 0) :
    HaarCarrierEqv 1 (angularDerivative 0 i (polyVar i)) (polyVar 0) := by
  have hz := ((ratDerivative_polyVar_ne 0 i (Ne.symm h0)).mul_left (polyVar i)).trans
    (RatPolyCoeffEqv.mul_zero_right _)
  have hs := derivativeFactor_self_carrier 1 0 i (by decide) (by decide) hi
  exact (HaarCarrierEqv.add (blocks:=1) hs
    (HaarCarrierEqv.smul (-1) (RatPolyCoeffEqv.haarCarrier hz))).trans
    (RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_zero (-1))).trans
        (RatPolyCoeffEqv.add_zero _)))

private theorem angular_base (i : Nat) (hi : i < 4) (h0 : i ≠ 0) :
    HaarCarrierEqv 1 (angularDerivative 0 i kernelBase) (polySmul (-half) (polyVar i)) := by
  have h := (RatPolyCoeffEqv.haarCarrier
      (angularDerivative_smul 0 i half (polyAdd polyOne (polyVar 0)))).trans
    (HaarCarrierEqv.smul half ((RatPolyCoeffEqv.haarCarrier
      (angularDerivative_add 0 i polyOne (polyVar 0))).trans
      ((HaarCarrierEqv.add (blocks:=1)
        (RatPolyCoeffEqv.haarCarrier (angularDerivative_one 0 i))
        (angular_scalar i hi h0)).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _)))))
  exact h.trans (RatPolyCoeffEqv.haarCarrier
    ((RatPolyCoeffEqv.smul_assoc half (-1) _).trans
    (RatPolyCoeffEqv.smul_coefficient
      (poly_identity_of_normal_eq (.mul (.var 0) (.const (-1))) (.neg (.var 0))
        (by decide) (fun _ => half)) _)))

private theorem factor_derivative (a c : Q') (p y b : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polySmul a (polyMul p y)) b)
        (polyMul (polyMul p b) (polySmul c y)))
      (polySmul (a+c) (polyMul (polyMul p b) y)) := by
  have hs : RatPolyCoeffEqv (polyMul (polyMul p y) b) (polyMul (polyMul p b) y) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => p | 1 => y | _ => b)
  exact (((RatPolyCoeffEqv.polyMul_smul_left a _ _).trans (hs.smul a)).add
    (RatPolyCoeffEqv.polyMul_smul_right c _ _)).trans
      (RatPolyCoeffEqv.add_smul_same a c _)

private theorem halfDegree_step (m : Nat) :
    -halfDegree (m+1) + -half ≈ -halfDegree (m+2) := by
  change ((-((m+1:Nat):Int))*2 + (-1)*2)*2 =
    (-((m+2:Nat):Int))*(2*2)
  omega

/-- The power rule is PROVED for the actual angular derivation. Padding of
coordinate exponent lists is retained through arbitrary-insertion equality. -/
theorem kernelPower_angular (i : Nat) (hi : i < 4) (h0 : i ≠ 0) : ∀ m,
    HaarCarrierEqv 1 (angularDerivative 0 i (kernelPower (m+1)))
      (polySmul (-halfDegree (m+1)) (polyMul (kernelPower m) (polyVar i)))
  | 0 => by
      have hp : RatPolyCoeffEqv (kernelPower 1) kernelBase := RatPolyCoeffEqv.one_mul _
      exact ((RatPolyCoeffEqv.haarCarrier (angularDerivative_congr 0 i hp)).trans
        (angular_base i hi h0)).trans
        (HaarCarrierEqv.smul (-half)
          (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul (polyVar i)))).symm
  | m+1 => by
      have h := (RatPolyCoeffEqv.haarCarrier
        (angularDerivative_mul 0 i (kernelPower (m+1)) kernelBase)).trans
        (HaarCarrierEqv.add (blocks:=1)
          (HaarCarrierEqv.mul_right kernelBase (kernelPower_angular i hi h0 m))
          (HaarCarrierEqv.mul_left (kernelPower (m+1)) (angular_base i hi h0)))
      exact h.trans (RatPolyCoeffEqv.haarCarrier
        ((factor_derivative (-halfDegree (m+1)) (-half)
        (kernelPower m) (polyVar i) kernelBase).trans
          (RatPolyCoeffEqv.smul_coefficient (halfDegree_step m) _)))

private theorem plane_moment (m i : Nat) (hi : i < 4) (h0 : i ≠ 0) :
    H (polyMul (kernelPower (m+1)) (polyVar 0)) ≈
      halfDegree (m+1) * H (polyMul (kernelPower m) (sq (polyVar i))) := by
  have hc := HaarCarrierEqv.add
    (HaarCarrierEqv.mul_right (polyVar i) (kernelPower_angular i hi h0 m))
    (HaarCarrierEqv.mul_left (kernelPower (m+1)) (angular_coordinate i hi h0))
  have hz := Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_carrier hc))
    (quaternionHaar_weighted_angular 0 (by decide) hi (kernelPower (m+1)) (polyVar i))
  have ht := (RatPolyCoeffEqv.polyMul_smul_left (-halfDegree (m+1))
      (polyMul (kernelPower m) (polyVar i)) (polyVar i)).trans
    ((RatPolyCoeffEqv.mul_assoc (kernelPower m) (polyVar i) (polyVar i)).smul
      (-halfDegree (m+1)))
  have he := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_append 1 _ _)) hz
  have hh := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul 1 _ _))
        (Q'.eqv_symm (haar_of_coeff ht)))) he
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
      (.add (.mul (.neg (.var 1)) (.var 2)) (.var 0)) (by decide)
      (fun | 0 => H (polyMul (kernelPower (m+1)) (polyVar 0))
           | 1 => halfDegree (m+1) | _ => H (polyMul (kernelPower m) (sq (polyVar i))))) hh

private def coordinates (i : Nat) : RatPoly := polyVar i
private def radiusExpr : PolyExpr :=
  .add (.mul (.var 0) (.var 0))
    (.add (.mul (.var 1) (.var 1))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
private def transverse := three (fun i => sq (polyVar i))

private theorem radius_shape : HaarCarrierEqv 1 (quaternionRadiusPolynomial 0)
    (coeffEvalExpr coordinates radiusExpr) := by
  apply carrierOfPrefix
  · intro t ht
    simp only [quaternionRadiusPolynomial, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  · exact supported_add (supported_polyMul (hpvar (by decide)) (hpvar (by decide)))
      (supported_add (supported_polyMul (hpvar (by decide)) (hpvar (by decide)))
        (supported_add (supported_polyMul (hpvar (by decide)) (hpvar (by decide)))
          (supported_polyMul (hpvar (by decide)) (hpvar (by decide)))))
  · exact quaternionPrefixPolynomialCheck_sound 1 (by rfl)

private theorem radius_unit : HaarCarrierEqv 1 (quaternionRadiusPolynomial 0) polyOne := by
  intro p
  exact Q'.eqv_trans _ _ _ (quaternionHaar_mul_radius 1 0 (by decide) p)
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))

private theorem transverse_shape : HaarCarrierEqv 1 transverse
    (coeffEvalExpr baseEnv
      (.mul (.const 4) (.add (.var 0) (.neg (.mul (.var 0) (.var 0)))))) := by
  have hu : HaarCarrierEqv 1 (polyAdd (sq (polyVar 0)) transverse) polyOne :=
    radius_shape.symm.trans radius_unit
  have hc : RatPolyCoeffEqv
      (polyAdd (polyAdd (sq (polyVar 0)) transverse) (polyNeg (sq (polyVar 0)))) transverse :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
      (fun | 0 => sq (polyVar 0) | _ => transverse)
  have h := (RatPolyCoeffEqv.haarCarrier hc).symm.trans
    (HaarCarrierEqv.add (blocks:=1) hu (HaarCarrierEqv.refl 1 (polyNeg (sq (polyVar 0)))))
  have hf := (RatPolyCoeffEqv.one_smul polyOne).symm.add
    (RatPolyCoeffEqv.neg (scalar_shape.mul scalar_shape))
  exact h.trans (RatPolyCoeffEqv.haarCarrier (hf.trans (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.const 1) (.neg (.mul scalarExpr scalarExpr)))
    (.mul (.const 4) (.add (.var 0) (.neg (.mul (.var 0) (.var 0)))))
    (by decide) baseEnv)))

private theorem scalar_moment (m : Nat) :
    H (polyMul (kernelPower m) (polyVar 0)) ≈ 2*kernelMoment (m+1) + -kernelMoment m := by
  have hc := (scalar_shape.mul_left (kernelPower m)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 1) scalarExpr)
      (.add (.mul (.const 2) (.mul (.var 1) (.var 0))) (.neg (.var 1)))
      (by decide) (fun | 0 => kernelBase | _ => kernelPower m))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (Q'.eqv_trans _ _ _ (hsub _ _)
      (Q'.add_eqv_congr_right _ _ _ (hcap 2 (kernelPower (m+1)))))

private theorem transverse_moment (m : Nat) :
    H (polyMul (kernelPower m) transverse) ≈
      4*(kernelMoment (m+1) + -kernelMoment (m+2)) := by
  have hc := (HaarCarrierEqv.mul_left (kernelPower m) transverse_shape).trans
    (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 1) (.mul (.const 4) (.add (.var 0) (.neg (.mul (.var 0) (.var 0))))))
      (.mul (.const 4) (.add (.mul (.var 1) (.var 0))
        (.neg (.mul (.mul (.var 1) (.var 0)) (.var 0)))))
      (by decide) (fun | 0 => kernelBase | _ => kernelPower m)))
  exact Q'.eqv_trans _ _ _ (haar_of_carrier hc)
    (Q'.eqv_trans _ _ _ (hcap 4 _)
      (Q'.mul_eqv_congr_left _ _ _ (hsub (kernelPower (m+1)) (kernelPower (m+2)))))

private theorem three_moment (m : Nat) :
    H (polyMul (kernelPower m) transverse) ≈
      H (polyMul (kernelPower m) (sq (polyVar 1))) +
        (H (polyMul (kernelPower m) (sq (polyVar 2))) +
          H (polyMul (kernelPower m) (sq (polyVar 3)))) := by
  have hc : RatPolyCoeffEqv (polyMul (kernelPower m) transverse)
      (polyAdd (polyMul (kernelPower m) (sq (polyVar 1)))
        (polyAdd (polyMul (kernelPower m) (sq (polyVar 2)))
          (polyMul (kernelPower m) (sq (polyVar 3))))) :=
    (RatPolyCoeffEqv.mul_add_right (kernelPower m) (sq (polyVar 1))
      (polyAdd (sq (polyVar 2)) (sq (polyVar 3)))).trans
      ((RatPolyCoeffEqv.refl (polyMul (kernelPower m) (sq (polyVar 1)))).add
        (RatPolyCoeffEqv.mul_add_right (kernelPower m) (sq (polyVar 2)) (sq (polyVar 3))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
      (Q'.add_eqv_congr_left _ _ _ (quaternionHaar_append 1 _ _)))

private theorem natCoeff (m a b : Nat) :
    Q'.ofNat (a*m+b) ≈ Q'.ofNat a * Q'.ofNat m + Q'.ofNat b := by
  change ((a*m+b:Nat):Int)*1 =
    ((a:Int)*(m:Int)*1 + (b:Int)*1)*1
  simp only [Int.natCast_add, Int.natCast_mul, Int.mul_one]

private theorem halfDegree_four (m : Nat) :
    4*halfDegree m ≈ 2*Q'.ofNat m := by
  change (4*(m:Int))*1 = (2*(m:Int))*2
  omega

private theorem positive_nat (m : Nat) (hm : 0 < m) : (0:Q') < Q'.ofNat m := by
  change 0*1 < (m:Int)*1
  omega

/-- Exact all-degree recurrence on the ORIGINAL Haar, including m=0. -/
theorem kernelMoment_recurrence (m : Nat) :
    Q'.ofNat (2*m+6)*kernelMoment (m+1) ≈ Q'.ofNat (2*m+3)*kernelMoment m := by
  cases m with
  | zero => decide
  | succ m =>
      let A := H (polyMul (kernelPower (m+1)) (polyVar 0))
      let S := fun i => H (polyMul (kernelPower m) (sq (polyVar i)))
      have hp : 3*A ≈ halfDegree (m+1)*(S 1+(S 2+S 3)) := by
        have hs := Q'.add_eqv_congr' (plane_moment m 1 (by decide) (by decide))
          (Q'.add_eqv_congr' (plane_moment m 2 (by decide) (by decide))
            (plane_moment m 3 (by decide) (by decide)))
        exact Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (.mul (.const 3) (.var 0))
            (.add (.var 0) (.add (.var 0) (.var 0))) (by decide) (fun _ => A))
          (Q'.eqv_trans _ _ _ hs
            (poly_identity_of_normal_eq
              (.add (.mul (.var 0) (.var 1))
                (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3))))
              (.mul (.var 0) (.add (.var 1) (.add (.var 2) (.var 3)))) (by decide)
              (fun | 0 => halfDegree (m+1) | 1 => S 1 | 2 => S 2 | _ => S 3)))
      have ht := Q'.eqv_trans _ _ _ hp
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (three_moment m)) (transverse_moment m)))
      have he : 3*(2*kernelMoment (m+2) + -kernelMoment (m+1)) ≈
          (2*Q'.ofNat (m+1))*(kernelMoment (m+1) + -kernelMoment (m+2)) :=
        Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_eqv_congr_left 3 _ _ (scalar_moment (m+1))))
          (Q'.eqv_trans _ _ _ ht
            (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (halfDegree_four (m+1))))))
      have hn : Q'.ofNat (2*(m+1)+6) ≈ 2*Q'.ofNat (m+1)+6 := natCoeff (m+1) 2 6
      have hk : Q'.ofNat (2*(m+1)+3) ≈ 2*Q'.ofNat (m+1)+3 := natCoeff (m+1) 2 3
      apply QPoly.q_eqv_of_sub_zero
      have hd := Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ he)
        (Q'.add_neg_self_eqv _)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hn)
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hk)))
        (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
          (.add (.mul (.add (.mul (.const 2) (.var 0)) (.const 6)) (.var 1))
            (.neg (.mul (.add (.mul (.const 2) (.var 0)) (.const 3)) (.var 2))))
          (.add (.mul (.const 3) (.add (.mul (.const 2) (.var 1)) (.neg (.var 2))))
            (.neg (.mul (.mul (.const 2) (.var 0)) (.add (.var 2) (.neg (.var 1))))))
          (by decide) (fun | 0 => Q'.ofNat (m+1) | 1 => kernelMoment (m+2) | _ => kernelMoment (m+1))) hd)

private theorem cancel_positive {a b c : Q'} (hc : (0:Q') < c) (h : c*a ≈ c*b) : a ≈ b := by
  let r := Q'.recipPos c hc
  have he (x : Q') : r*(c*x) ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r c) (Q'.mul_recipPos_eqv c hc)))
        (Q'.one_mul_eqv x))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (he a))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r _ _ h) (he b))

/-- Positive recurrence denominator, supplied for every natural exponent. -/
theorem recurrenceDenominator_positive (m : Nat) : (0:Q') < Q'.ofNat (2*m+6) :=
  positive_nat _ (by omega)

/-- Computable positive ratio; no quotient representative or choice. -/
def momentRatio (m : Nat) : Q' :=
  Q'.ofNat (2*m+3) * Q'.recipPos (Q'.ofNat (2*m+6)) (recurrenceDenominator_positive m)

theorem momentRatio_positive (m : Nat) : (0:Q') < momentRatio m :=
  Q'.mul_pos (positive_nat _ (by omega)) (Q'.recipPos_pos _ _)

private theorem ratio_cancel (m : Nat) : Q'.ofNat (2*m+6)*momentRatio m ≈ Q'.ofNat (2*m+3) :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => Q'.ofNat (2*m+6) | 1 => Q'.ofNat (2*m+3)
           | _ => Q'.recipPos (Q'.ofNat (2*m+6)) (recurrenceDenominator_positive m)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_recipPos_eqv (Q'.ofNat (2*m+6)) (recurrenceDenominator_positive m)))
      (Q'.mul_one_eqv _))

private theorem moment_step (m : Nat) : kernelMoment (m+1) ≈ momentRatio m * kernelMoment m :=
  cancel_positive (recurrenceDenominator_positive m)
    (Q'.eqv_trans _ _ _ (kernelMoment_recurrence m)
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_eqv_congr_right _ _ _ (ratio_cancel m)))))

/-- Explicit finite product normalizer. -/
def normalizer : Nat → Q'
  | 0 => 1
  | m+1 => momentRatio m * normalizer m

theorem normalizer_positive : ∀ m, (0:Q') < normalizer m
  | 0 => by decide
  | m+1 => Q'.mul_pos (momentRatio_positive m) (normalizer_positive m)

theorem kernelMoment_normalizer : ∀ m, kernelMoment m ≈ normalizer m
  | 0 => QPolyHaarPositiveSubstitution.haar_one 1
  | m+1 => Q'.eqv_trans _ _ _ (moment_step m)
      (Q'.mul_eqv_congr_left _ _ _ (kernelMoment_normalizer m))

private theorem positive_transport {a b : Q'} (ha : (0:Q') < a) (h : a ≈ b) : (0:Q') < b := by
  have hn := Q'.num_pos_of_pos ha
  have hd : (0:Int) < (b.den:Int) := by exact_mod_cast b.den_pos
  have ht : (0:Int) < b.num*(a.den:Int) := by
    rw [← h]
    exact Int.mul_pos hn hd
  have had : (0:Int) < (a.den:Int) := by exact_mod_cast a.den_pos
  have hb : (0:Int) < b.num := by
    by_cases hp : 0 < b.num
    · exact hp
    · have hle : b.num ≤ 0 := by omega
      have hc := Int.mul_nonpos_of_nonpos_of_nonneg hle (Int.le_of_lt had)
      omega
  change 0*(b.den:Int) < b.num*1
  omega

/-- Strict positivity is PRODUCED for the actual original polynomial moment. -/
theorem kernelMoment_positive (m : Nat) : (0:Q') < kernelMoment m :=
  positive_transport (normalizer_positive m) (Q'.eqv_symm (kernelMoment_normalizer m))

/-- Actual squared-chord polynomial from the identity, 2-2*x0. -/
def squaredChord : RatPoly := coeffEvalExpr coordinates
  (.add (.const 2) (.neg (.mul (.const 2) (.var 0))))

def chordMoment (m : Nat) : Q' := H (polyMul (kernelPower m) squaredChord)

/-- Computable exact concentration rate 6/(m+3), with positive denominator. -/
def concentrationRate (m : Nat) : Q' := Q'.mkPos 6 (m+3) (by omega)

theorem concentrationRate_positive (m : Nat) : (0:Q') < concentrationRate m := by
  change 0*((concentrationRate m).den:Int) < 6*1
  omega

private theorem chord_difference (m : Nat) : chordMoment m ≈
    4*(kernelMoment m + -kernelMoment (m+1)) := by
  have hc := RatPolyCoeffEqv.neg (scalar_shape.mul_left (cap 2))
  have hs := ((RatPolyCoeffEqv.refl (cap 2)).add hc).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 2) (.neg (.mul (.const 2) scalarExpr)))
      (.mul (.const 4) (.add (.const 1) (.neg (.var 0)))) (by decide) baseEnv)
  have hp := (hs.mul_left (kernelPower m)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 1) (.mul (.const 4) (.add (.const 1) (.neg (.var 0)))))
      (.mul (.const 4) (.add (.var 1) (.neg (.mul (.var 1) (.var 0)))))
      (by decide) (fun | 0 => kernelBase | _ => kernelPower m))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (hcap 4 _)
      (Q'.mul_eqv_congr_left _ _ _ (hsub (kernelPower m) (kernelPower (m+1)))))

private theorem rate_cleared (m : Nat) : Q'.ofNat (2*m+6)*concentrationRate m ≈ 12 := by
  change ((Q'.ofNat (2*m+6)*concentrationRate m).num)*1 =
    12*((Q'.ofNat (2*m+6)*concentrationRate m).den:Int)
  rw [Q'.mul_den_cast]
  have hd : (concentrationRate m).den = m+3 := Q'.mkPos_den _ _ _
  rw [hd]
  change (((2*m+6:Nat):Int)*6)*1 = 12*(1*((m+3:Nat):Int))
  omega

/-- Exact unnormalized squared-chord payment for EVERY natural exponent. -/
theorem chordMoment_exact (m : Nat) : chordMoment m ≈ concentrationRate m * kernelMoment m := by
  let d := Q'.ofNat (2*m+6)
  let a := Q'.ofNat (2*m+3)
  have hdiff : d + -a ≈ 3 := by
    change (((2*m+6:Nat):Int)*1 + (-((2*m+3:Nat):Int))*1)*1 = 3*(1*1)
    omega
  have h : d*(4*(kernelMoment m + -kernelMoment (m+1))) ≈ 12*kernelMoment m := by
    have he := poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 4) (.add (.var 2) (.neg (.var 3)))))
      (.add (.mul (.mul (.const 4) (.add (.var 0) (.neg (.var 1)))) (.var 2))
        (.mul (.const 4) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3))))))
      (by decide) (fun | 0 => d | 1 => a | 2 => kernelMoment m | _ => kernelMoment (m+1))
    have hz := Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (kernelMoment_recurrence m)))
      (Q'.add_neg_self_eqv _)
    exact Q'.eqv_trans _ _ _ he
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left 4 _ _ hdiff))
          (Q'.mul_eqv_congr_left 4 _ _ hz))
        (poly_identity_of_normal_eq
          (.add (.mul (.mul (.const 4) (.const 3)) (.var 0)) (.mul (.const 4) (.const 0)))
          (.mul (.const 12) (.var 0)) (by decide) (fun _ => kernelMoment m)))
  exact cancel_positive (recurrenceDenominator_positive m)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left d _ _ (chord_difference m))
      (Q'.eqv_trans _ _ _ h
        (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
          (Q'.mul_eqv_congr_right _ _ _ (rate_cleared m))))))

/-- The normalizer is the actual produced positive original Haar moment. -/
def normalizedChordMoment (m : Nat) : Q' := chordMoment m * Q'.recipPos (kernelMoment m) (kernelMoment_positive m)

theorem normalizedChordMoment_exact (m : Nat) : normalizedChordMoment m ≈ concentrationRate m :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (chordMoment_exact m))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ _))
        (Q'.mul_one_eqv _)))

theorem small_m_regressions : kernelMoment 0 ≈ 1 ∧ kernelMoment 1 ≈ half ∧
    kernelMoment 2 ≈ Q'.mkPos 5 16 (by decide) ∧
    chordMoment 0 ≈ 2 ∧ chordMoment 1 ≈ Q'.mkPos 3 4 (by decide) ∧
    chordMoment 2 ≈ Q'.mkPos 3 8 (by decide) := by decide

/- The following determinant identity uses only actual one-block Haar moments.
It is useful when comparing a raw radial deficit with an OWN centered
variance.  It does not identify the polynomial source with a BF4 action. -/

/-- Cleared variance determinant of the concentration kernel's scalar
coordinate. The fourth moment of the kernel is not an independent input. -/
def kernelScalarDeterminant (m : Nat) : Q' :=
  kernelMoment m * kernelMoment (m+2) -
    kernelMoment (m+1) * kernelMoment (m+1)

/-- Cleared radial deficit, before any positive mass is inverted. -/
def kernelRadialDeterminant (m : Nat) : Q' :=
  kernelMoment m * (kernelMoment (m+1) - kernelMoment (m+2))

/-- Exact all-degree radial/variance ratio, proved from the two actual
polynomial Haar recurrence instances. -/
theorem kernelRadialDeterminant_eq_variance (m : Nat) :
    kernelRadialDeterminant m ≈
      Q'.ofNat (m+3) * kernelScalarDeterminant m := by
  let A := kernelMoment m
  let B := kernelMoment (m+1)
  let C := kernelMoment (m+2)
  let M := Q'.ofNat m
  have hd : Q'.ofNat (2*m+6) ≈ 2*M+6 := natCoeff m 2 6
  have ha : Q'.ofNat (2*m+3) ≈ 2*M+3 := natCoeff m 2 3
  have he : Q'.ofNat (2*(m+1)+6) ≈ 2*M+8 := by
    have h : 2*(m+1)+6 = 2*m+8 := by omega
    rw [h]
    exact natCoeff m 2 8
  have hb : Q'.ofNat (2*(m+1)+3) ≈ 2*M+5 := by
    have h : 2*(m+1)+3 = 2*m+5 := by omega
    rw [h]
    exact natCoeff m 2 5
  have hn : Q'.ofNat (m+3) ≈ M+3 := by
    exact Q'.eqv_trans _ _ _
      (by simpa only [Nat.one_mul] using natCoeff m 1 3)
      (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.var 0)) (.const 3))
        (.add (.var 0) (.const 3)) (by decide) (fun _ => M))
  have hfirst : (2*M+6)*B ≈ (2*M+3)*A :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hd))
      (Q'.eqv_trans _ _ _ (kernelMoment_recurrence m)
        (Q'.mul_eqv_congr_right _ _ _ ha))
  have hsecond : (2*M+8)*C ≈ (2*M+5)*B :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm he))
      (Q'.eqv_trans _ _ _ (kernelMoment_recurrence (m+1))
        (Q'.mul_eqv_congr_right _ _ _ hb))
  have hzero : B*((2*M+6)*B-(2*M+3)*A)+
      A*((2*M+5)*B-(2*M+8)*C) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left B _ _
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hfirst)
            (Q'.add_neg_self_eqv _)))
        (Q'.mul_eqv_congr_left A _ _
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _ hsecond)) (Q'.add_neg_self_eqv _))))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.const 0)) (.mul (.var 1) (.const 0)))
        (.const 0) (by decide) (fun | 0 => B | _ => A))
  have halgebra :
      2*(kernelRadialDeterminant m-
        Q'.ofNat (m+3)*kernelScalarDeterminant m) ≈
      B*((2*M+6)*B-(2*M+3)*A)+
        A*((2*M+5)*B-(2*M+8)*C) := by
    have hrepl :
        2*(kernelRadialDeterminant m-
          Q'.ofNat (m+3)*kernelScalarDeterminant m) ≈
        2*(kernelRadialDeterminant m-
          (M+3)*kernelScalarDeterminant m) :=
      Q'.mul_eqv_congr_left 2 _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_right _ _ _ hn)))
    exact Q'.eqv_trans _ _ _
      hrepl
      (poly_identity_of_normal_eq
        (.mul (.const 2)
          (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
            (.neg (.mul (.add (.var 3) (.const 3))
              (.add (.mul (.var 0) (.var 2))
                (.neg (.mul (.var 1) (.var 1))))))))
        (.add (.mul (.var 1)
            (.add (.mul (.add (.mul (.const 2) (.var 3)) (.const 6)) (.var 1))
              (.neg (.mul (.add (.mul (.const 2) (.var 3)) (.const 3)) (.var 0)))))
          (.mul (.var 0)
            (.add (.mul (.add (.mul (.const 2) (.var 3)) (.const 5)) (.var 1))
              (.neg (.mul (.add (.mul (.const 2) (.var 3)) (.const 8)) (.var 2))))))
        (by decide) (fun | 0 => A | 1 => B | 2 => C | _ => M))
  have h2 : 2*(kernelRadialDeterminant m-
      Q'.ofNat (m+3)*kernelScalarDeterminant m) ≈ 0 :=
    Q'.eqv_trans _ _ _ halgebra hzero
  have hdiff : kernelRadialDeterminant m-
      Q'.ofNat (m+3)*kernelScalarDeterminant m ≈ 0 :=
    cancel_positive (by decide : (0:Q') < 2)
      (Q'.eqv_trans _ _ _ h2 (by decide : (0:Q') ≈ 2*0))
  exact QPoly.q_eqv_of_sub_zero hdiff

/-- The literal SU(2) character of the one-block scalar coordinate. -/
def kernelCharacter : RatPoly := polySmul 2 (polyVar 0)

/-- On the one-block sphere this is exactly `4-kernelCharacter²`. -/
def kernelRawRadial : RatPoly := polySmul 4 transverse

private theorem kernelCharacter_first (m : Nat) :
    H (polyMul (kernelPower m) kernelCharacter) ≈
      4*kernelMoment (m+1)-2*kernelMoment m := by
  have h : H (polyMul (kernelPower m) kernelCharacter) ≈
      2*H (polyMul (kernelPower m) (polyVar 0)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 2
        (kernelPower m) (polyVar 0)))
      (quaternionHaar_polySmul 1 2 (polyMul (kernelPower m) (polyVar 0)))
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (scalar_moment m))
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.add (.mul (.const 2) (.var 0)) (.neg (.var 1))))
        (.add (.mul (.const 4) (.var 0)) (.neg (.mul (.const 2) (.var 1))))
        (by decide) (fun | 0 => kernelMoment (m+1) | _ => kernelMoment m)))

private theorem kernelRawRadial_moment (m : Nat) :
    H (polyMul (kernelPower m) kernelRawRadial) ≈
      16*(kernelMoment (m+1)-kernelMoment (m+2)) := by
  have h : H (polyMul (kernelPower m) kernelRawRadial) ≈
      4*H (polyMul (kernelPower m) transverse) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 4
        (kernelPower m) transverse))
      (quaternionHaar_polySmul 1 4 (polyMul (kernelPower m) transverse))
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 4 _ _ (transverse_moment m))
      (poly_identity_of_normal_eq
        (.mul (.const 4) (.mul (.const 4) (.add (.var 0) (.neg (.var 1)))))
        (.mul (.const 16) (.add (.var 0) (.neg (.var 1))))
        (by decide) (fun | 0 => kernelMoment (m+1) | _ => kernelMoment (m+2))))

private theorem kernelCharacter_radial_carrier :
    HaarCarrierEqv 1
      (polyAdd (sq kernelCharacter) kernelRawRadial) (cap 4) := by
  let x := polyVar 0
  have hu : HaarCarrierEqv 1 (polyAdd (sq x) transverse) polyOne :=
    radius_shape.symm.trans radius_unit
  have hf : RatPolyCoeffEqv (sq kernelCharacter) (polySmul 4 (sq x)) :=
    ((RatPolyCoeffEqv.polyMul_smul_left 2 x kernelCharacter).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 2 x x).smul 2)).trans
      ((RatPolyCoeffEqv.smul_assoc 2 2 (sq x)).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : (2:Q')*2 ≈ 4) _))
  have hs : RatPolyCoeffEqv
      (polyAdd (sq kernelCharacter) kernelRawRadial)
      (polySmul 4 (polyAdd (sq x) transverse)) :=
    ((hf.add (RatPolyCoeffEqv.refl kernelRawRadial))).trans
      (RatPolyCoeffEqv.smul_add 4 (sq x) transverse).symm
  exact (RatPolyCoeffEqv.haarCarrier hs).trans
    ((HaarCarrierEqv.smul 4 hu).trans
      (RatPolyCoeffEqv.haarCarrier
        ((cap_mul_left 4 polyOne).symm.trans (RatPolyCoeffEqv.mul_one (cap 4)))))

private theorem kernelCharacter_second (m : Nat) :
    H (polyMul (kernelPower m) (sq kernelCharacter)) ≈
      4*kernelMoment m-
        16*(kernelMoment (m+1)-kernelMoment (m+2)) := by
  have hsum := haar_of_carrier
    (HaarCarrierEqv.mul_left (kernelPower m) kernelCharacter_radial_carrier)
  have hsplit :
      H (polyMul (kernelPower m) (sq kernelCharacter))+
        H (polyMul (kernelPower m) kernelRawRadial) ≈
      4*kernelMoment m := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
        (quaternionHaar_append 1 _ _)))
      (Q'.eqv_trans _ _ _ hsum
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm (kernelPower m) (cap 4)))
          (hcap 4 (kernelPower m))))
  have hraw := kernelRawRadial_moment m
  have hrewrite :
      H (polyMul (kernelPower m) (sq kernelCharacter))-
        (4*kernelMoment m-16*(kernelMoment (m+1)-kernelMoment (m+2))) ≈
      (H (polyMul (kernelPower m) (sq kernelCharacter))+
        16*(kernelMoment (m+1)-kernelMoment (m+2)))-4*kernelMoment m :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.add (.var 0) (.var 2)) (.neg (.var 1)))
      (by decide)
      (fun | 0 => H (polyMul (kernelPower m) (sq kernelCharacter))
           | 1 => 4*kernelMoment m
           | _ => 16*(kernelMoment (m+1)-kernelMoment (m+2)))
  have hzero :
      (H (polyMul (kernelPower m) (sq kernelCharacter))+
        16*(kernelMoment (m+1)-kernelMoment (m+2)))-4*kernelMoment m ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (Q'.add_eqv_congr_left _ _ _ hraw)))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hsplit)
        (Q'.add_neg_self_eqv _))
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _ hrewrite hzero

private theorem scalarDeterminant_cleared (m : Nat) :
    (Q'.ofNat (2*m+6)*Q'.ofNat (2*m+8))*
        kernelScalarDeterminant m ≈
      6*(kernelMoment m*kernelMoment (m+1)) := by
  let A := kernelMoment m
  let B := kernelMoment (m+1)
  let C := kernelMoment (m+2)
  let M := Q'.ofNat m
  have hd : Q'.ofNat (2*m+6) ≈ 2*M+6 := natCoeff m 2 6
  have ha : Q'.ofNat (2*m+3) ≈ 2*M+3 := natCoeff m 2 3
  have he : Q'.ofNat (2*m+8) ≈ 2*M+8 := natCoeff m 2 8
  have hb : Q'.ofNat (2*(m+1)+3) ≈ 2*M+5 := by
    have h : 2*(m+1)+3 = 2*m+5 := by omega
    rw [h]
    exact natCoeff m 2 5
  have he' : Q'.ofNat (2*(m+1)+6) ≈ Q'.ofNat (2*m+8) := by
    change (((2*(m+1)+6:Nat):Int)*1) = (((2*m+8:Nat):Int)*1)
    omega
  have hfirst := kernelMoment_recurrence m
  have hsecond : Q'.ofNat (2*m+8)*C ≈ Q'.ofNat (2*(m+1)+3)*B :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm he'))
      (kernelMoment_recurrence (m+1))
  have hrepl :
      (Q'.ofNat (2*m+6)*Q'.ofNat (2*m+8))*
          kernelScalarDeterminant m ≈
      ((2*M+6)*(2*M+8))*(A*C-B*B) :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hd)
        (Q'.mul_eqv_congr_left _ _ _ he))
  have halgebra :
      ((2*M+6)*(2*M+8))*(A*C-B*B) ≈
      (2*M+6)*A*((2*M+8)*C-(2*M+5)*B)+
      (2*M+8)*B*((2*M+3)*A-(2*M+6)*B)+6*(A*B) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.add (.mul (.const 2) (.var 0)) (.const 6))
          (.add (.mul (.const 2) (.var 0)) (.const 8)))
        (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 2)))))
      (.add
        (.add
          (.mul (.mul (.add (.mul (.const 2) (.var 0)) (.const 6)) (.var 1))
            (.add (.mul (.add (.mul (.const 2) (.var 0)) (.const 8)) (.var 3))
              (.neg (.mul (.add (.mul (.const 2) (.var 0)) (.const 5)) (.var 2)))))
          (.mul (.mul (.add (.mul (.const 2) (.var 0)) (.const 8)) (.var 2))
            (.add (.mul (.add (.mul (.const 2) (.var 0)) (.const 3)) (.var 1))
              (.neg (.mul (.add (.mul (.const 2) (.var 0)) (.const 6)) (.var 2))))))
        (.mul (.const 6) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => M | 1 => A | 2 => B | _ => C)
  have hz1 : (2*M+8)*C-(2*M+5)*B ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm he))
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hb))))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hsecond)
        (Q'.add_neg_self_eqv _))
  have hz2 : (2*M+3)*A-(2*M+6)*B ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm ha))
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hd))))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hfirst))
        (Q'.add_neg_self_eqv _))
  exact Q'.eqv_trans _ _ _ hrepl
    (Q'.eqv_trans _ _ _ halgebra
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ hz1)
            (Q'.mul_eqv_congr_left _ _ _ hz2)) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add
            (.add (.mul (.var 0) (.const 0)) (.mul (.var 1) (.const 0)))
            (.var 2))
          (.var 2) (by decide)
          (fun | 0 => (2*M+6)*A | 1 => (2*M+8)*B
               | _ => 6*(A*B)))))

/-- The cleared OWN scalar determinant is strictly positive for every
finite kernel power, including zero. -/
theorem kernelScalarDeterminant_positive (m : Nat) :
    (0:Q') < kernelScalarDeterminant m := by
  let d := Q'.ofNat (2*m+6)*Q'.ofNat (2*m+8)
  have hd : (0:Q') < d := Q'.mul_pos
    (positive_nat _ (by omega)) (positive_nat _ (by omega))
  have hp : (0:Q') < 6*(kernelMoment m*kernelMoment (m+1)) :=
    Q'.mul_pos (by decide)
      (Q'.mul_pos (kernelMoment_positive m) (kernelMoment_positive (m+1)))
  have h : kernelScalarDeterminant m ≈
      (6*(kernelMoment m*kernelMoment (m+1)))*Q'.recipPos d hd :=
    cancel_positive hd
      (Q'.eqv_trans _ _ _ (scalarDeterminant_cleared m)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2)))
            (by decide)
            (fun | 0 => d | 1 => 6*(kernelMoment m*kernelMoment (m+1))
                 | _ => Q'.recipPos d hd))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv d hd))
            (Q'.mul_one_eqv _)))))
  exact positive_transport
    (Q'.mul_pos hp (Q'.recipPos_pos d hd)) (Q'.eqv_symm h)

/-- The literal radial expectation under the actual positive polynomial
source; the inverse is of its already produced Haar mass. -/
def normalizedKernelRawRadial (m : Nat) : Q' :=
  H (polyMul (kernelPower m) kernelRawRadial) *
    Q'.recipPos (kernelMoment m) (kernelMoment_positive m)

/-- The literal OWN centered variance of the character under that source. -/
def normalizedKernelVariance (m : Nat) : Q' :=
  normalizedVariance 1 (kernelPower m) kernelCharacter (kernelMoment_positive m)

private theorem normalizedKernelRawRadial_cleared (m : Nat) :
    (kernelMoment m*kernelMoment m)*normalizedKernelRawRadial m ≈
      16*kernelRadialDeterminant m := by
  let A := kernelMoment m
  let B := kernelMoment (m+1)
  let C := kernelMoment (m+2)
  let g := Q'.recipPos A (kernelMoment_positive m)
  have hc : A*g ≈ 1 := Q'.mul_recipPos_eqv A (kernelMoment_positive m)
  have hraw := kernelRawRadial_moment m
  have hstart : (A*A)*normalizedKernelRawRadial m ≈
      (A*A)*(16*(B-C)*g) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hraw)
  have halgebra : (A*A)*(16*(B-C)*g) ≈
      (16*(A*(B-C)))*(A*g) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.const 16) (.add (.var 1) (.neg (.var 2)))) (.var 3)))
      (.mul (.mul (.const 16)
          (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))))
        (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => A | 1 => B | 2 => C | _ => g)
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ halgebra
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hc)
        (Q'.mul_one_eqv _)))

private theorem kernelVariance_algebra (A B C g : Q') (hc : A*g ≈ 1) :
    (A*A)*((4*A-16*(B-C))*g-
      ((4*B-2*A)*g)*((4*B-2*A)*g)) ≈
    16*(A*C-B*B) := by
  have halgebra :
      (A*A)*((4*A-16*(B-C))*g-
        ((4*B-2*A)*g)*((4*B-2*A)*g)) ≈
      (A*(4*A-16*(B-C)))*(A*g)-
        ((4*B-2*A)*(4*B-2*A))*((A*g)*(A*g)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.add
          (.mul (.add (.mul (.const 4) (.var 0))
              (.neg (.mul (.const 16) (.add (.var 1) (.neg (.var 2)))))) (.var 3))
          (.neg (.mul
            (.mul (.add (.mul (.const 4) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))) (.var 3))
            (.mul (.add (.mul (.const 4) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))) (.var 3))))))
      (.add
        (.mul
          (.mul (.var 0)
            (.add (.mul (.const 4) (.var 0))
              (.neg (.mul (.const 16) (.add (.var 1) (.neg (.var 2)))))))
          (.mul (.var 0) (.var 3)))
        (.neg (.mul
          (.mul (.add (.mul (.const 4) (.var 1))
              (.neg (.mul (.const 2) (.var 0))))
            (.add (.mul (.const 4) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))))
          (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3))))))
      (by decide) (fun | 0 => A | 1 => B | 2 => C | _ => g)
  have hones : (A*g)*(A*g) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        hc)
  have hcancel :
      (A*(4*A-16*(B-C)))*(A*g)-
        ((4*B-2*A)*(4*B-2*A))*((A*g)*(A*g)) ≈
      16*(A*C-B*B) := by
    have hsubs :
        (A*(4*A-16*(B-C)))*(A*g)-
          ((4*B-2*A)*(4*B-2*A))*((A*g)*(A*g)) ≈
        (A*(4*A-16*(B-C)))*1-
          ((4*B-2*A)*(4*B-2*A))*1 :=
      Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hc)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _ hones))
    have hones_cancel :
        (A*(4*A-16*(B-C)))*1-
          ((4*B-2*A)*(4*B-2*A))*1 ≈
        A*(4*A-16*(B-C))-
          (4*B-2*A)*(4*B-2*A) :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.const 1))
          (.neg (.mul (.var 1) (.const 1))))
        (.add (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => A*(4*A-16*(B-C)) | _ => (4*B-2*A)*(4*B-2*A))
    have hpoly :
        A*(4*A-16*(B-C))-
          (4*B-2*A)*(4*B-2*A) ≈ 16*(A*C-B*B) :=
      poly_identity_of_normal_eq
        (.add
          (.mul (.var 0)
            (.add (.mul (.const 4) (.var 0))
              (.neg (.mul (.const 16) (.add (.var 1) (.neg (.var 2)))))))
          (.neg (.mul
            (.add (.mul (.const 4) (.var 1))
              (.neg (.mul (.const 2) (.var 0))))
            (.add (.mul (.const 4) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))))))
        (.mul (.const 16)
          (.add (.mul (.var 0) (.var 2))
            (.neg (.mul (.var 1) (.var 1)))))
        (by decide) (fun | 0 => A | 1 => B | _ => C)
    exact Q'.eqv_trans _ _ _ hsubs (Q'.eqv_trans _ _ _ hones_cancel hpoly)
  exact Q'.eqv_trans _ _ _ halgebra hcancel

private theorem normalizedKernelVariance_cleared (m : Nat) :
    (kernelMoment m*kernelMoment m)*normalizedKernelVariance m ≈
      16*kernelScalarDeterminant m := by
  let A := kernelMoment m
  let B := kernelMoment (m+1)
  let C := kernelMoment (m+2)
  let g := Q'.recipPos A (kernelMoment_positive m)
  have hc : A*g ≈ 1 := Q'.mul_recipPos_eqv A (kernelMoment_positive m)
  have hf := kernelCharacter_first m
  have ht := kernelCharacter_second m
  have hsubst :
      (A*A)*normalizedKernelVariance m ≈
      (A*A)*((4*A-16*(B-C))*g-
        ((4*B-2*A)*g)*((4*B-2*A)*g)) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ ht)
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_right _ _ _ hf))
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_right _ _ _ hf)))))
  exact Q'.eqv_trans _ _ _ hsubst (kernelVariance_algebra A B C g hc)

/-- EXACT source-specific obstruction: normalized raw radial mass is
`m+3` times the OWN variance under the same one-block polynomial Haar law. -/
theorem normalizedKernelRawRadial_eq_variance (m : Nat) :
    normalizedKernelRawRadial m ≈
      Q'.ofNat (m+3)*normalizedKernelVariance m := by
  let A := kernelMoment m
  have hA : (0:Q') < A*A :=
    Q'.mul_pos (kernelMoment_positive m) (kernelMoment_positive m)
  apply cancel_positive hA
  exact Q'.eqv_trans _ _ _ (normalizedKernelRawRadial_cleared m)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 16 _ _ (kernelRadialDeterminant_eq_variance m))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.const 16) (.mul (.var 0) (.var 1)))
          (.mul (.var 0) (.mul (.const 16) (.var 1)))
          (by decide)
          (fun | 0 => Q'.ofNat (m+3) | _ => kernelScalarDeterminant m))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (normalizedKernelVariance_cleared m)))
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2)))
            (by decide)
            (fun | 0 => Q'.ofNat (m+3)
                 | 1 => kernelMoment m*kernelMoment m
                 | _ => normalizedKernelVariance m)))))

/-- The exact OWN variance is strictly positive at every finite degree. -/
theorem normalizedKernelVariance_positive (m : Nat) :
    (0:Q') < normalizedKernelVariance m := by
  let A := kernelMoment m
  have hA : (0:Q') < A*A :=
    Q'.mul_pos (kernelMoment_positive m) (kernelMoment_positive m)
  have hD : (0:Q') < 16*kernelScalarDeterminant m :=
    Q'.mul_pos (by decide) (kernelScalarDeterminant_positive m)
  have h : normalizedKernelVariance m ≈
      (16*kernelScalarDeterminant m)*Q'.recipPos (A*A) hA :=
    cancel_positive hA
      (Q'.eqv_trans _ _ _ (normalizedKernelVariance_cleared m)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2)))
            (by decide)
            (fun | 0 => A*A | 1 => 16*kernelScalarDeterminant m
                 | _ => Q'.recipPos (A*A) hA))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_recipPos_eqv (A*A) hA))
            (Q'.mul_one_eqv _)))))
  exact positive_transport
    (Q'.mul_pos hD (Q'.recipPos_pos (A*A) hA)) (Q'.eqv_symm h)

/-- For every natural proposed coefficient, one explicit positive polynomial
source defeats a uniform radial/variance comparison. -/
theorem no_nat_uniform_radial_variance_factor (C : Nat) :
    Q'.ofNat C * normalizedKernelVariance C < normalizedKernelRawRadial C := by
  have hv := normalizedKernelVariance_positive C
  have hc : Q'.ofNat C < Q'.ofNat (C+3) := by
    change ((C:Int)*1) < (((C+3:Nat):Int)*1)
    omega
  have hmul : Q'.ofNat C * normalizedKernelVariance C <
      Q'.ofNat (C+3) * normalizedKernelVariance C := by
    have h := Q'.mul_lt_mul_of_pos_left hv hc
    exact Q'.lt_of_le_of_lt
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (HeatKernelRGStep.lt_of_lt_of_le h
        (Q'.ge_of_eqv (Q'.mul_comm_eqv _ _)))
  exact HeatKernelRGStep.lt_of_lt_of_le hmul
    (Q'.ge_of_eqv (normalizedKernelRawRadial_eq_variance C))

end YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration

#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelPower_supported
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelPower_certificate
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelPower_angular
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelMoment_recurrence
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.recurrenceDenominator_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.momentRatio_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.normalizer_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelMoment_normalizer
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelMoment_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.concentrationRate_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.chordMoment_exact
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.normalizedChordMoment_exact
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.small_m_regressions
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelScalarDeterminant
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelRadialDeterminant
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelCharacter
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelRawRadial
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.normalizedKernelRawRadial
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.normalizedKernelVariance
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelRadialDeterminant_eq_variance
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.kernelScalarDeterminant_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.normalizedKernelRawRadial_eq_variance
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.normalizedKernelVariance_positive
#print axioms YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration.no_nat_uniform_radial_variance_factor

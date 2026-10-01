/-
# Exact norm of the symmetric source test

The difference between the squared symmetric test and the squared jump test
has four terms. The original product heat pairs them into two copies of each
one-slice source moment. No stationary-source relation is used.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSumGram
import YMGap.Continuum.SU2QuaternionProductHeatSourceYoung

namespace YMGap.Continuum.SU2QuaternionProductHeatSumNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatSumTest (sumCopy sumTest)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm (kineticPair_symm)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem cross_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (p g : RatPoly) :
    H (n+n) (polyMul (productHeat n w K ids) (polyMul p (liftBoundary n g))) ≈
      H n (polyMul g (productMap n w K ids p)) :=
  Q'.eqv_symm (productMap_pairing n w K ids p g)

private theorem fourterm_norm (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f : RatPoly) :
    let x := q
    let y := liftBoundary n q
    let u := f
    let v := liftBoundary n f
    let T := polyAdd
      (polyAdd (polyMul (polyMul x x) (polyMul u v))
        (polyMul (polyMul y y) (polyMul u v)))
      (polyAdd (polyMul (polyMul x y) (polyMul u u))
        (polyMul (polyMul x y) (polyMul v v)))
    weightedPair (n+n) (productHeat n w K ids)
        (sumTest n q f) (sumTest n q f) ≈
      sourceIncrementCost n w K ids q f +
        4*H (n+n) (polyMul (productHeat n w K ids) T) := by
  dsimp only
  let x := q
  let y := liftBoundary n q
  let u := f
  let v := liftBoundary n f
  let r := polyMul (jump n q) (jump n f)
  let T := polyAdd
    (polyAdd (polyMul (polyMul x x) (polyMul u v))
      (polyMul (polyMul y y) (polyMul u v)))
    (polyAdd (polyMul (polyMul x y) (polyMul u u))
      (polyMul (polyMul x y) (polyMul v v)))
  have hp : RatPolyCoeffEqv
      (polyMul (sumTest n q f) (sumTest n q f))
      (polyAdd (polyMul r r) (polyMul (cap 4) T)) := by
    unfold sumTest sumCopy r T x y u v jump
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul
        (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))))
      (.add
        (.mul
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))))
        (.mul (.const 4)
          (.add
            (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 3)))
              (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 3))))
            (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
              (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 3)))))))
      (by decide)
      (fun | 0 => q | 1 => liftBoundary n q | 2 => f | _ => liftBoundary n f)
  have hpoly : H (n+n) (polyMul
      (polyMul (sumTest n q f) (sumTest n q f)) (productHeat n w K ids)) ≈
      H (n+n) (polyMul (productHeat n w K ids)
        (polyAdd (polyMul r r) (polyMul (cap 4) T))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_right _))
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
  have hsplit := quaternionHaar_polyMul_add_right (n+n)
    (productHeat n w K ids) (polyMul r r) (polyMul (cap 4) T)
  have hD : H (n+n) (polyMul (productHeat n w K ids) (polyMul r r)) ≈
      sourceIncrementCost n w K ids q f := by
    unfold sourceIncrementCost weightedPair
    exact haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hscale : H (n+n)
      (polyMul (productHeat n w K ids) (polyMul (cap 4) T)) ≈
      4*H (n+n) (polyMul (productHeat n w K ids) T) := by
    have hc := cap_mul_left 4 T
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul hc))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left 4 T _))
          (Q'.eqv_trans _ _ _
            (quaternionHaar_polySmul (n+n) 4 (polyMul T (productHeat n w K ids)))
            (Q'.mul_eqv_congr_left 4 _ _
              (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))))
  exact Q'.eqv_trans _ _ _ hpoly
    (Q'.eqv_trans _ _ _ hsplit (Q'.add_eqv_congr' hD hscale))

/-- Exact second-test norm on the original finite product heat. The first
extra moment uses the observable heat image; the second is the SAME source
moment used by the interacting odd marginal. -/
theorem sumTest_norm_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (productHeat n w K ids)
        (sumTest n q f) (sumTest n q f) ≈
      sourceIncrementCost n w K ids q f +
        8*H n (polyMul (polyMul q q) (polyMul f (productMap n w K ids f))) +
        8*sourceMoment n w K ids q (polyMul f f) := by
  let W := productHeat n w K ids
  let q2f := polyMul (polyMul q q) f
  let qf2 := polyMul q (polyMul f f)
  let U := H n (polyMul q2f (productMap n w K ids f))
  let V := sourceMoment n w K ids q (polyMul f f)
  let x := q
  let y := liftBoundary n q
  let u := f
  let v := liftBoundary n f
  let t1 := polyMul (polyMul x x) (polyMul u v)
  let t2 := polyMul (polyMul y y) (polyMul u v)
  let t3 := polyMul (polyMul x y) (polyMul u u)
  let t4 := polyMul (polyMul x y) (polyMul v v)
  let T := polyAdd (polyAdd t1 t2) (polyAdd t3 t4)
  have h1 : H (n+n) (polyMul W t1) ≈ U := by
    have hpoly : RatPolyCoeffEqv t1 (polyMul q2f (liftBoundary n f)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2))
        (by decide) (fun | 0 => q | 1 => f | _ => liftBoundary n f)
    have hcross := cross_pin n w K ids q2f f
    have htarget : H n (polyMul f (productMap n w K ids q2f)) ≈ U :=
      kineticPair_symm n w K ids hids f q2f hf
        (supported_polyMul (supported_polyMul hq hq) hf)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul hpoly))
      (Q'.eqv_trans _ _ _ hcross htarget)
  have h2 : H (n+n) (polyMul W t2) ≈ U := by
    have hpoly : RatPolyCoeffEqv t2 (polyMul f (liftBoundary n q2f)) := by
      unfold t2 y v q2f
      rw [lift_product, lift_product]
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 2)))
        (by decide) (fun | 0 => liftBoundary n q | 1 => f | _ => liftBoundary n f)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul hpoly))
      (cross_pin n w K ids f q2f)
  have h3 : H (n+n) (polyMul W t3) ≈ V := by
    have hpoly : RatPolyCoeffEqv t3 (polyMul qf2 (liftBoundary n q)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
        (by decide) (fun | 0 => q | 1 => liftBoundary n q | _ => f)
    have hcross := cross_pin n w K ids qf2 q
    have htarget : H n (polyMul q (productMap n w K ids qf2)) ≈ V := by
      unfold V sourceMoment
      exact kineticPair_symm n w K ids hids q qf2 hq
        (supported_polyMul hq (supported_polyMul hf hf))
    exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul hpoly))
      (Q'.eqv_trans _ _ _ hcross htarget)
  have h4 : H (n+n) (polyMul W t4) ≈ V := by
    have hpoly : RatPolyCoeffEqv t4 (polyMul q (liftBoundary n qf2)) := by
      unfold t4 y v qf2
      rw [lift_product, lift_product]
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))
        (by decide) (fun | 0 => q | 1 => liftBoundary n q | _ => liftBoundary n f)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul hpoly))
      (cross_pin n w K ids q qf2)
  have hT : H (n+n) (polyMul W T) ≈ (U+U)+(V+V) :=
    Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right (n+n) W (polyAdd t1 t2) (polyAdd t3 t4))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (n+n) W t1 t2)
          (Q'.add_eqv_congr' h1 h2))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (n+n) W t3 t4)
          (Q'.add_eqv_congr' h3 h4)))
  have hraw := fourterm_norm n w K ids q f
  have halg : 4*((U+U)+(V+V)) ≈ 8*U+8*V :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1))))
      (.add (.mul (.const 8) (.var 0)) (.mul (.const 8) (.var 1)))
      (by decide) (fun | 0 => U | _ => V)
  have hU : U ≈ H n (polyMul (polyMul q q)
      (polyMul f (productMap n w K ids f))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc (polyMul q q) f _)
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _ hT) halg))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left 8 _ _ hU)
            (Q'.eqv_refl _)))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.add (.mul (.const 8) (.var 1)) (.mul (.const 8) (.var 2))))
          (.add (.add (.var 0) (.mul (.const 8) (.var 1))) (.mul (.const 8) (.var 2)))
          (by decide)
          (fun | 0 => sourceIncrementCost n w K ids q f
               | 1 => H n (polyMul (polyMul q q)
                   (polyMul f (productMap n w K ids f)))
               | _ => V))))

#print axioms sumTest_norm_pin

end YMGap.Continuum.SU2QuaternionProductHeatSumNorm

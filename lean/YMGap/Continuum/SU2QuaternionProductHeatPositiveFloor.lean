/-
# Positive floor for the original selected product heat

This file records the finite algebraic floor obtained by multiplying the
individual certified heat floors.  It is a certificate on the original
polynomial Haar carrier, not a continuum or normalized Wilson estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Constructive.Geometric
import YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
import YMGap.Continuum.SU2QuaternionRatPolyDifferential
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- The elementary product-floor identity, compiled as a certificate.

The witness uses `(p-ell)q + ell(q-eta)`, so it only needs the two
nonnegative residual certificates and nonnegativity of `ell`; it does not
discard or replace either factor.
-/
def Certificate.productFloor {blocks : Nat} {p q : RatPoly} {ell eta : Q'}
    (hq : Certificate blocks q)
    (hple : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (hqeta : Certificate blocks (polyAdd q (polyNeg (cap eta))))
    (hell : (0 : Q') ≤ ell) :
    Certificate blocks (polyAdd (polyMul p q) (polyNeg (cap (ell * eta)))) := by
  let S := (hple.mul hq).add ((Certificate.constant blocks ell hell).mul hqeta)
  have hsplit : RatPolyCoeffEqv
      (polyAdd (polyMul (polyAdd p (polyNeg (cap ell))) q)
        (polyMul (cap ell) (polyAdd q (polyNeg (cap eta)))))
      (polyAdd (polyMul p q) (polyNeg (polyMul (cap ell) (cap eta)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
        (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap ell | _ => cap eta)
  have hcap : RatPolyCoeffEqv
      (polyAdd (polyMul p q) (polyNeg (polyMul (cap ell) (cap eta))))
      (polyAdd (polyMul p q) (polyNeg (cap (ell * eta)))) :=
    (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul ell eta))
  exact Certificate.ofCoeff (hsplit.trans hcap).symm S

/-- The actual product of selected heat factors has the product floor
`headFloor(w) ^ ids.length` on every finite admissible list. -/
def productHeat_floorCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) :
    (ids : List Nat) → (∀ i, i ∈ ids → i < n) →
      Certificate (n+n)
        (polyAdd (productHeat n w K ids)
          (polyNeg (cap ((headFloor w) ^ ids.length))))
  | [], _ => by
      have hzero : Certificate (n+n) (cap (0 : Q')) :=
        Certificate.constant _ 0 (Q'.le_refl' _)
      have hone : RatPolyCoeffEqv (cap (1 : Q')) polyOne :=
        RatPolyCoeffEqv.one_smul polyOne
      have hcancel : RatPolyCoeffEqv
          (polyAdd polyOne (polyNeg polyOne)) (cap (0 : Q')) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
          (fun _ => polyOne)
      apply Certificate.ofCoeff (p := polyAdd polyOne (polyNeg (cap 1)))
        (q := cap 0)
      exact ((RatPolyCoeffEqv.refl polyOne).add (RatPolyCoeffEqv.neg hone)).trans
        hcancel
      exact hzero
  | i :: ids, hi => by
      have hii : i < n := hi i List.mem_cons_self
      have htail : ∀ j, j ∈ ids → j < n :=
        fun j hj => hi j (List.mem_cons_of_mem i hj)
      let f := heatAt i (n+i) w K
      let ell := headFloor w
      have hq : Certificate (n+n) (productHeat n w K ids) :=
        productHeatCertificate n hw0 hw1 K hK ids htail
      have hple : Certificate (n+n) (polyAdd f (polyNeg (cap ell))) :=
        heatAt_floorCertificate (by omega) (by omega) hw0 hw1 K hK
      have hqeta : Certificate (n+n)
          (polyAdd (productHeat n w K ids)
            (polyNeg (cap (ell ^ ids.length)))) :=
        productHeat_floorCertificate n hw0 hw1 K hK ids htail
      have hprod := Certificate.productFloor hq hple hqeta
        (Q'.le_of_lt (headFloor_positive hw0 hw1))
      simpa [productHeat, polynomialProduct, f, ell, Q'.pow_succ] using hprod

theorem productFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (ids : List Nat) : (0 : Q') < (headFloor w) ^ ids.length :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) ids.length

end YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor.Certificate.productFloor
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor.productHeat_floorCertificate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor.productFloor_positive

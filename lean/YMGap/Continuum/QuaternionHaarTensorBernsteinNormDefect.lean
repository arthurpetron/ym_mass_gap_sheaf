/-
The finite same-Haar tensor Bernstein norm-defect comparison.

The weights are the ACTUAL four-coordinate joint weights under one quaternion
Haar, never products of marginal Haar weights. This file multiplies the
constructed cube norm-defect certificate by the actual positive joint basis,
then sums its finite consequences. The separate conditional-variance identity
needed to evaluate the discrepancy sum is not asserted here.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
import YMGap.Continuum.QuaternionHaarCubeNormDefect
import YMGap.Continuum.BernsteinFallingProductError
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarCubeNormDefect
open YMGap.Continuum.BernsteinFallingProductError
open YMGap.Continuum.QuaternionHaarWordDifference

local infix:50 " ≈ " => Q'.eqv

/-- Actual rational cube coordinate at Bernstein degree `N=n+1`. -/
def rawCoordinate (n k : Nat) : Q' := 2 * grid n k + -1

/-- The scalar-first four-coordinate raw node, including all cube corners. -/
def rawNode (n k0 k1 k2 k3 : Nat) : CubeNode :=
  fun i => match i.val with
    | 0 => rawCoordinate n k0
    | 1 => rawCoordinate n k1
    | 2 => rawCoordinate n k2
    | _ => rawCoordinate n k3

private theorem rawCoordinate_abs_le_one (n k : Nat) (hk : k ≤ n+1) :
    Q'.abs (rawCoordinate n k) ≤ 1 := by
  have h0 : (0 : Q') ≤ 2 * grid n k :=
    Q'.mul_nonneg _ _ (by decide) (grid_nonnegative n k)
  have h1 : 2 * grid n k ≤ (2 : Q') * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (grid_le_one n k hk) (by decide)
  have hl : -(1 : Q') ≤ rawCoordinate n k := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.neg (.const 1)) (.add (.const 0) (.neg (.const 1)))
        (by decide) (fun _ => (0 : Q'))))
      (Q'.add_le_add_right _ _ _ h0)
  have hu : rawCoordinate n k ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ h1)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.const 1)) (.neg (.const 1)))
        (.const 1) (by decide) (fun _ => (0 : Q'))))
  exact Q'.abs_le hl hu

/-- Every actual grid coordinate lies in the squared rational cube. -/
theorem rawCoordinate_square_le_one (n k : Nat) (hk : k ≤ n+1) :
    rawCoordinate n k * rawCoordinate n k ≤ (1 : Q') := by
  let u := rawCoordinate n k
  have hu := rawCoordinate_abs_le_one n k hk
  have hsq : Q'.abs u * Q'.abs u ≤ (1 : Q') * 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hu (Q'.abs_nonneg u))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hu (by decide))
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self (u*u))
    (Q'.le_trans' _ _ _ (YMGap.Constructive.ExpNeg.abs_mul_le u u)
      (Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv (by decide :
        Q'.eqv ((1 : Q')*1) 1))))

/-- The four actual grid indices imply the exact guard required by the
one-block cube certificate; `n=0` and endpoints are included. -/
theorem rawNode_square_le_one (n k0 k1 k2 k3 : Nat)
    (h0 : k0 ≤ n+1) (h1 : k1 ≤ n+1)
    (h2 : k2 ≤ n+1) (h3 : k3 ≤ n+1) :
    ∀ i : Fin 4,
      rawNode n k0 k1 k2 k3 i * rawNode n k0 k1 k2 k3 i ≤ (1 : Q') := by
  intro i
  rcases i with ⟨i,hi⟩
  cases i with
  | zero => exact rawCoordinate_square_le_one n k0 h0
  | succ i => cases i with
    | zero => exact rawCoordinate_square_le_one n k1 h1
    | succ i => cases i with
      | zero => exact rawCoordinate_square_le_one n k2 h2
      | succ i => exact rawCoordinate_square_le_one n k3 h3

private def basisCertificateRaw (n k0 k1 k2 k3 : Nat) :
    Certificate 1 (jointBasisRaw n k0 k1 k2 k3) :=
  .mul (coordinateBasisCertificate n ⟨0, by decide⟩ k0)
    (.mul (coordinateBasisCertificate n ⟨1, by decide⟩ k1)
      (.mul (coordinateBasisCertificate n ⟨2, by decide⟩ k2)
        (coordinateBasisCertificate n ⟨3, by decide⟩ k3)))

private def rawDefectScalar (n k0 k1 k2 k3 : Nat) : Q' :=
  let a := nodeNormScalar (rawNode n k0 k1 k2 k3) + -1
  a * a

private theorem term_normDefect_le (n k0 k1 k2 k3 : Nat)
    (h0 : k0 ≤ n+1) (h1 : k1 ≤ n+1)
    (h2 : k2 ≤ n+1) (h3 : k3 ≤ n+1) :
    jointWeightRaw n k0 k1 k2 k3 * rawDefectScalar n k0 k1 k2 k3 ≤
      16 * quaternionHaar 1
        (polyMul (jointBasisRaw n k0 k1 k2 k3)
          (discrepancy (rawNode n k0 k1 k2 k3))) := by
  let W := jointBasisRaw n k0 k1 k2 k3
  let r := rawNode n k0 k1 k2 k3
  let D := discrepancy r
  let c := rawDefectScalar n k0 k1 k2 k3
  have horder : quaternionHaar 1 (polyMul W (normDefect r)) ≤
      quaternionHaar 1 (polyMul W (polyMul (cap 16) D)) :=
    weighted_order (basisCertificateRaw n k0 k1 k2 k3)
      (defectCertificate r (rawNode_square_le_one n k0 k1 k2 k3 h0 h1 h2 h3))
  have hleft : quaternionHaar 1 (polyMul W (normDefect r)) ≈
      jointWeightRaw n k0 k1 k2 k3 * c := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul (normDefect_cap r)))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff ((RatPolyCoeffEqv.mul_comm W (cap c)).trans
          (cap_mul_left c W)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 1 c W)
          (Q'.mul_comm_eqv c (quaternionHaar 1 W))))
  have hright : quaternionHaar 1 (polyMul W (polyMul (cap 16) D)) ≈
      16 * quaternionHaar 1 (polyMul W D) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul (cap_mul_left 16 D)))
      (weighted_scale 1 W D 16)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
    (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hright))

private def sum4 (f : Nat → Nat → Nat → Nat → Q') (count : Nat) : Q' :=
  finSum (fun k0 => finSum (fun k1 => finSum (fun k2 =>
    finSum (fun k3 => f k0 k1 k2 k3) count) count) count) count

/-- Literal SAME-Haar weighted sum of the raw cube-to-sphere discrepancy. -/
def jointDiscrepancy (n : Nat) : Q' :=
  sum4 (fun k0 k1 k2 k3 => quaternionHaar 1
    (polyMul (jointBasisRaw n k0 k1 k2 k3)
      (discrepancy (rawNode n k0 k1 k2 k3)))) (n+2)

/-- Literal weighted squared norm defect, using the same four joint weights. -/
def jointNormDefect (n : Nat) : Q' :=
  sum4 (fun k0 k1 k2 k3 =>
    jointWeightRaw n k0 k1 k2 k3 * rawDefectScalar n k0 k1 k2 k3) (n+2)

private theorem finSum_le_lt (f g : Nat → Q') :
    ∀ count, (∀ k, k < count → f k ≤ g k) →
      finSum f count ≤ finSum g count
  | 0, _ => Q'.le_refl' 0
  | count+1, h =>
      Q'.add_le_add
        (finSum_le_lt f g count (fun k hk => h k (by omega)))
        (h count (by omega))

private theorem sum4_le_lt (f g : Nat → Nat → Nat → Nat → Q')
    (count : Nat)
    (h : ∀ k0 k1 k2 k3, k0<count → k1<count → k2<count → k3<count →
      f k0 k1 k2 k3 ≤ g k0 k1 k2 k3) :
    sum4 f count ≤ sum4 g count := by
  unfold sum4
  apply finSum_le_lt
  intro k0 hk0
  apply finSum_le_lt
  intro k1 hk1
  apply finSum_le_lt
  intro k2 hk2
  apply finSum_le_lt
  intro k3 hk3
  exact h k0 k1 k2 k3 hk0 hk1 hk2 hk3

private theorem sum4_const_mul (c : Q')
    (f : Nat → Nat → Nat → Nat → Q') (count : Nat) :
    c * sum4 f count ≈
      sum4 (fun k0 k1 k2 k3 => c * f k0 k1 k2 k3) count := by
  unfold sum4
  exact Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
    (finSum_eqv_congr _ _ (fun k0 =>
      Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
        (finSum_eqv_congr _ _ (fun k1 =>
          Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
            (finSum_eqv_congr _ _ (fun k2 =>
              const_mul_finSum _ c count) count)) count)) count)

/-- The finite signed norm-defect cost is paid by the actual positive
joint-basis discrepancy, at every degree including `N=1` (`n=0`). -/
theorem jointNormDefect_le_sixteen_discrepancy (n : Nat) :
    jointNormDefect n ≤ 16 * jointDiscrepancy n := by
  have h := sum4_le_lt
    (fun k0 k1 k2 k3 =>
      jointWeightRaw n k0 k1 k2 k3 * rawDefectScalar n k0 k1 k2 k3)
    (fun k0 k1 k2 k3 => 16 * quaternionHaar 1
      (polyMul (jointBasisRaw n k0 k1 k2 k3)
        (discrepancy (rawNode n k0 k1 k2 k3))))
    (n+2) (fun k0 k1 k2 k3 h0 h1 h2 h3 =>
      term_normDefect_le n k0 k1 k2 k3
        (by omega) (by omega) (by omega) (by omega))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.eqv_symm (sum4_const_mul 16 _ (n+2))))

end YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.rawCoordinate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.rawNode
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.rawCoordinate_square_le_one
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.rawNode_square_le_one
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.jointDiscrepancy
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.jointNormDefect
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect.jointNormDefect_le_sixteen_discrepancy

/-
# Angular derivatives on one quaternion block

This file packages the algebraic rotation field
`x_i * partial_j - x_j * partial_i` on the rational polynomial carrier.
Its Gaussian-head integral vanishes exactly for head coordinates.  This is
only the finite polynomial/Gaussian identity; no Haar transfer, selected-action
integration by parts, or Schwinger--Dyson conclusion is asserted here.
-/

import YMGap.Continuum.SU2QuaternionHeadGaussianIBP

namespace YMGap.Continuum.SU2QuaternionAngularDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP

local infix:50 " ≈ " => Q'.eqv

/-- The infinitesimal coordinate-plane rotation `x_i partial_j-x_j partial_i`. -/
def angularDerivative (i j : Nat) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (polyVar i) (ratDerivative j p))
    (polySmul (-1) (polyMul (polyVar j) (ratDerivative i p)))

/-- Angular differentiation is additive, at coefficient equality. -/
theorem angularDerivative_add (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (polyAdd p q))
      (polyAdd (angularDerivative i j p) (angularDerivative i j q)) := by
  unfold angularDerivative
  rw [ratDerivative_add_exact, ratDerivative_add_exact]
  refine ((RatPolyCoeffEqv.mul_add_right (polyVar i) _ _).add
    ((RatPolyCoeffEqv.mul_add_right (polyVar j) _ _).smul (-1))).trans ?_
  refine (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
    (RatPolyCoeffEqv.smul_add (-1)
      (polyMul (polyVar j) (ratDerivative i p))
      (polyMul (polyVar j) (ratDerivative i q)))).trans ?_
  exact RatPolyCoeffEqv.four_add_swap _ _ _ _

/-- Coefficient equality is preserved by angular differentiation. -/
theorem angularDerivative_congr (i j : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (angularDerivative i j p) (angularDerivative i j q) := by
  unfold angularDerivative
  exact RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.mul_left (polyVar i) (h.derivative j))
    ((RatPolyCoeffEqv.mul_left (polyVar j) (h.derivative i)).smul (-1))

private theorem coordinate_times_product
    (coordinate derivative : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyVar coordinate)
        (ratDerivative derivative (polyMul p q)))
      (polyAdd
        (polyMul
          (polyMul (polyVar coordinate) (ratDerivative derivative p)) q)
        (polyMul p
          (polyMul (polyVar coordinate) (ratDerivative derivative q)))) := by
  refine (RatPolyCoeffEqv.mul_left (polyVar coordinate)
    (ratDerivative_mul derivative p q)).trans ?_
  refine (RatPolyCoeffEqv.mul_add_right (polyVar coordinate) _ _).trans ?_
  apply RatPolyCoeffEqv.add
  · exact (RatPolyCoeffEqv.mul_assoc
      (polyVar coordinate) (ratDerivative derivative p) q).symm
  · refine (RatPolyCoeffEqv.mul_assoc
      (polyVar coordinate) p (ratDerivative derivative q)).symm.trans ?_
    refine ((RatPolyCoeffEqv.mul_comm (polyVar coordinate) p).mul_right
      (ratDerivative derivative q)).trans ?_
    exact RatPolyCoeffEqv.mul_assoc
      p (polyVar coordinate) (ratDerivative derivative q)

/-- Leibniz rule for the angular derivation. -/
theorem angularDerivative_mul (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (polyMul p q))
      (polyAdd
        (polyMul (angularDerivative i j p) q)
        (polyMul p (angularDerivative i j q))) := by
  let api := polyMul (polyVar i) (ratDerivative j p)
  let aqi := polyMul (polyVar i) (ratDerivative j q)
  let bpj := polyMul (polyVar j) (ratDerivative i p)
  let bqj := polyMul (polyVar j) (ratDerivative i q)
  unfold angularDerivative
  refine ((coordinate_times_product i j p q).add
    ((coordinate_times_product j i p q).smul (-1))).trans ?_
  refine (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
    (RatPolyCoeffEqv.smul_add (-1)
      (polyMul bpj q) (polyMul p bqj))).trans ?_
  refine (RatPolyCoeffEqv.four_add_swap
    (polyMul api q) (polyMul p aqi)
    (polySmul (-1) (polyMul bpj q))
    (polySmul (-1) (polyMul p bqj))).trans ?_
  apply RatPolyCoeffEqv.add
  · rw [polyMul_add_left_exact]
    exact RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
      (RatPolyCoeffEqv.polyMul_smul_left (-1) bpj q).symm
  · refine (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
      (RatPolyCoeffEqv.polyMul_smul_right (-1) p bqj).symm).trans ?_
    exact (RatPolyCoeffEqv.mul_add_right p aqi (polySmul (-1) bqj)).symm

private theorem ratDerivative_polyVar_ne (i j : Nat) (hij : i ≠ j) :
    RatPolyCoeffEqv (ratDerivative i (polyVar j)) polyZero := by
  intro weight
  change
    (Q'.ofNat (exponentAt (varMono j) i) * 1) *
        weight (lowerExponentAt i (varMono j)) + 0 ≈ 0
  rw [YMGap.Continuum.SU2QuaternionSolidZonalCharacter.exponentAt_varMono,
    if_neg hij]
  have hcoefficient : Q'.ofNat 0 * 1 ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ 1 Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv 1)
  have hterm :
      (Q'.ofNat 0 * 1) * weight (lowerExponentAt i (varMono j)) ≈
        (0 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hcoefficient)
      (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hterm (Q'.eqv_refl 0))
    (QPoly.q_add_zero_eqv 0)

private theorem derivative_product_off_diagonal
    (i j : Nat) (hij : i ≠ j) (p : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative i (polyMul (polyVar j) p))
      (polyMul (polyVar j) (ratDerivative i p)) := by
  refine (ratDerivative_mul i (polyVar j) p).trans ?_
  refine (RatPolyCoeffEqv.add
    ((ratDerivative_polyVar_ne i j hij).mul_right p)
    (RatPolyCoeffEqv.refl _)).trans ?_
  refine (RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.mul_zero_left p)
    (RatPolyCoeffEqv.refl _)).trans ?_
  exact RatPolyCoeffEqv.zero_add _

private theorem partialGaussianHead_smul (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv
      (partialGaussianHead (polySmul a p))
      (polySmul a (partialGaussianHead p)) := by
  intro weight
  refine Q'.eqv_trans _ _ _ (partialGaussianHead_probe weight _) ?_
  refine Q'.eqv_trans _ _ _
    (ratWeightedSum_smul (gaussianHeadProbe weight) a p) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (partialGaussianHead_probe weight p))) ?_
  exact Q'.eqv_symm (ratWeightedSum_smul weight a _)

private theorem partialGaussianHead_cross
    (i j : Nat) (hi : i < 4) (hj : j < 4) (hij : i ≠ j) (p : RatPoly) :
    RatPolyCoeffEqv
      (partialGaussianHead
        (polyMul (polyVar i) (ratDerivative j p)))
      (partialGaussianHead
        (polyMul (polyVar j) (ratDerivative i p))) := by
  refine (partialGaussianHead_congr
    (derivative_product_off_diagonal j i (Ne.symm hij) p).symm).trans ?_
  refine (partialGaussianHead_ibp j hj (polyMul (polyVar i) p)).symm.trans ?_
  have hc : RatPolyCoeffEqv
      (polyMul (polyVar j) (polyMul (polyVar i) p))
      (polyMul (polyVar i) (polyMul (polyVar j) p)) := by
    refine (RatPolyCoeffEqv.mul_assoc
      (polyVar j) (polyVar i) p).symm.trans ?_
    refine ((RatPolyCoeffEqv.mul_comm (polyVar j) (polyVar i)).mul_right p).trans ?_
    exact RatPolyCoeffEqv.mul_assoc (polyVar i) (polyVar j) p
  refine (partialGaussianHead_congr hc).trans ?_
  exact (partialGaussianHead_ibp i hi (polyMul (polyVar j) p)).trans
    (partialGaussianHead_congr
      (derivative_product_off_diagonal i j hij p))

/-- Exact Gaussian angular-divergence cancellation in the head quaternion.
No homogeneity, degree, support, or positivity premise is used. -/
theorem partialGaussianHead_angularDerivative_zero
    (i j : Nat) (hi : i < 4) (hj : j < 4) (p : RatPoly) :
    RatPolyCoeffEqv
      (partialGaussianHead (angularDerivative i j p)) polyZero := by
  unfold angularDerivative
  rw [partialGaussianHead_add]
  by_cases hij : i = j
  · subst j
    exact (RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.refl _)
      (partialGaussianHead_smul (-1)
        (polyMul (polyVar i) (ratDerivative i p)))).trans
      (RatPolyCoeffEqv.add_neg_smul _)
  · exact ((partialGaussianHead_cross i j hi hj hij p).add
      (partialGaussianHead_smul (-1)
        (polyMul (polyVar j) (ratDerivative i p)))).trans
      (RatPolyCoeffEqv.add_neg_smul _)

end YMGap.Continuum.SU2QuaternionAngularDerivative

#print axioms YMGap.Continuum.SU2QuaternionAngularDerivative.angularDerivative
#print axioms YMGap.Continuum.SU2QuaternionAngularDerivative.angularDerivative_add
#print axioms YMGap.Continuum.SU2QuaternionAngularDerivative.angularDerivative_congr
#print axioms YMGap.Continuum.SU2QuaternionAngularDerivative.angularDerivative_mul
#print axioms YMGap.Continuum.SU2QuaternionAngularDerivative.partialGaussianHead_angularDerivative_zero

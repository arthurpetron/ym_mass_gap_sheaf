/-
# Rational linear laws for the same three-regulator Wilson limit

Each finite chart uses one original action and one partition, independently
of the insertion. Exact finite linearity therefore survives the previously
constructed diagonal, even though its Cauchy modulus depends on the expression.
Congruence below requires coefficient equality on every actual placed chart;
it does not assume arbitrary observable coverage or a new quotient relation.

These laws feed the mixed reflected form. They do not identify the enlarged
carrier with the previous plaquette carrier or transport its strict bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance (finiteValue_coeff_congr)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (haar_of_coeff_eqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base : Nat}

theorem chartScalar_congr (H : Nat) (e f : WindowExpression base) (r stage t : Nat)
    (hp : RatPolyCoeffEqv (chartInsertion r H t e) (chartInsertion r H t f)) :
    chartScalar hw0 hw1 H e r stage t ≈ chartScalar hw0 hw1 H f r stage t :=
  finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _ hp stage

theorem chartScalar_add (H : Nat) (e f : WindowExpression base) (r stage t : Nat) :
    chartScalar hw0 hw1 H (.add e f) r stage t ≈
      chartScalar hw0 hw1 H e r stage t + chartScalar hw0 hw1 H f r stage t := by
  unfold chartScalar chartInsertion centeredExpression
  simp only [recenterExpression, placedPolynomial]
  unfold finiteValue numerator
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_append _ _ _))
    (Q'.add_mul_eqv _ _ _)

theorem chartScalar_smul (H : Nat) (c : Q') (e : WindowExpression base) (r stage t : Nat) :
    chartScalar hw0 hw1 H (.smul c e) r stage t ≈
      c * chartScalar hw0 hw1 H e r stage t := by
  unfold chartScalar chartInsertion centeredExpression
  simp only [recenterExpression, placedPolynomial]
  unfold finiteValue numerator
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ c _ _)
          (Q'.mul_eqv_congr_left c _ _ (haar_of_coeff_eqv _ (RatPolyCoeffEqv.mul_comm _ _))))))
    (Q'.mul_assoc_eqv _ _ _)

theorem chartScalar_one (H r stage t : Nat) :
    chartScalar hw0 hw1 H (.one : WindowExpression base) r stage t ≈ 1 := by
  have hpin := chartScalar_original_pin hw0 hw1 H (.one : WindowExpression base)
    True.intro r stage t
  have hraw := originalWindowScalar_pin hw0 hw1 (2*H)
    (centeredExpression r (.one : WindowExpression base)) True.intro stage t t
  exact Q'.eqv_trans _ _ _ hpin (Q'.eqv_trans _ _ _ hraw
    (windowRatio_one hw0 hw1 _ _ _ t (2*H) t))

attribute [local irreducible] chartScalar

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

/-- Coefficient equality on the actual placed charts, with the original
partitions retained, determines the same limiting value. -/
theorem spatialLimit_congr (H : Nat) (e f : WindowExpression base)
    (he : Within (2*H) e) (hf : Within (2*H) f)
    (hp : ∀ r t, RatPolyCoeffEqv (chartInsertion r H t e) (chartInsertion r H t f)) :
    Equiv (spatialLimit hw0 hw1 H e he hsmall hd hs hb)
      (spatialLimit hw0 hw1 H f hf hsmall hd hs hb) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_congr hw0 hw1 H e f n n n (hp n n)))
    (spatial_diagonal_converges hw0 hw1 H e he hsmall hd hs hb)
    (spatial_diagonal_converges hw0 hw1 H f hf hsmall hd hs hb)

theorem spatialLimit_add (H : Nat) (e f : WindowExpression base)
    (he : Within (2*H) e) (hf : Within (2*H) f) :
    Equiv (spatialLimit hw0 hw1 H (.add e f) ⟨he, hf⟩ hsmall hd hs hb)
      (add (spatialLimit hw0 hw1 H e he hsmall hd hs hb)
        (spatialLimit hw0 hw1 H f hf hsmall hd hs hb)) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_add hw0 hw1 H e f n n n))
    (spatial_diagonal_converges hw0 hw1 H (.add e f) ⟨he, hf⟩ hsmall hd hs hb)
    (TrigAddCReal.convergesTo_add
      (spatial_diagonal_converges hw0 hw1 H e he hsmall hd hs hb)
      (spatial_diagonal_converges hw0 hw1 H f hf hsmall hd hs hb))

theorem spatialLimit_smul (H : Nat) (c : Q') (e : WindowExpression base)
    (he : Within (2*H) e) :
    Equiv (spatialLimit hw0 hw1 H (.smul c e) he hsmall hd hs hb)
      (mul (ofQ' c) (spatialLimit hw0 hw1 H e he hsmall hd hs hb)) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_smul hw0 hw1 H c e n n n))
    (spatial_diagonal_converges hw0 hw1 H (.smul c e) he hsmall hd hs hb)
    (convergesTo_const_mul (ofQ' c)
      (spatial_diagonal_converges hw0 hw1 H e he hsmall hd hs hb))

theorem spatialLimit_one (H : Nat) :
    Equiv (spatialLimit hw0 hw1 H (.one : WindowExpression base) True.intro hsmall hd hs hb)
      (ofQ' 1) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv (fun _ => chartScalar_one hw0 hw1 H n n n))
    (spatial_diagonal_converges hw0 hw1 H .one True.intro hsmall hd hs hb)
    (convergesTo_const (ofQ' 1))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.chartScalar_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.chartScalar_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.chartScalar_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.chartScalar_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.spatialLimit_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.spatialLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.spatialLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.spatialLimit_one

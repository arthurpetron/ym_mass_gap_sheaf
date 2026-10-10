/-
Finite concentration of the ACTUAL joint Bernstein weights on one quaternion.

The four coordinate rows are multiplied BEFORE the same polynomial Haar is
applied. Their conditional variance sums are coefficient identities; the
only sphere identity is the existing arbitrary-insertion Haar norm relation.
This gives a rational 48/(n+1) squared norm-defect bound, not continuous
integration, an interacting measure estimate or a physical spectral gap.
-/

import YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarCubeNormDefect
open YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
open YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance

local infix:50 " ≈ " => Q'.eqv

private def i0 : Fin 4 := ⟨0, by decide⟩
private def i1 : Fin 4 := ⟨1, by decide⟩
private def i2 : Fin 4 := ⟨2, by decide⟩
private def i3 : Fin 4 := ⟨3, by decide⟩
private def prod4 (a b c d : RatPoly) : RatPoly :=
  polyMul a (polyMul b (polyMul c d))
private def add4 (a b c d : RatPoly) : RatPoly :=
  polyAdd a (polyAdd b (polyAdd c d))
private def esum4 (a b c d : PolyExpr) : PolyExpr :=
  .add a (.add b (.add c d))
private def eprod4 (a b c d : PolyExpr) : PolyExpr :=
  .mul a (.mul b (.mul c d))

private def polySum4 (f : Nat → Nat → Nat → Nat → RatPoly) (count : Nat) : RatPoly :=
  polySum (fun k0 => polySum (fun k1 => polySum (fun k2 =>
    polySum (fun k3 => f k0 k1 k2 k3) count) count) count) count

private theorem polySum4_congr (f g : Nat → Nat → Nat → Nat → RatPoly)
    (h : ∀ a b c d, RatPolyCoeffEqv (f a b c d) (g a b c d)) (count : Nat) :
    RatPolyCoeffEqv (polySum4 f count) (polySum4 g count) :=
  polySum_congr _ _ (fun a => polySum_congr _ _ (fun b =>
    polySum_congr _ _ (fun c => polySum_congr _ _ (h a b c) count) count)
    count) count

private theorem polySum4_add (f g : Nat → Nat → Nat → Nat → RatPoly) (count : Nat) :
    RatPolyCoeffEqv (polySum4 (fun a b c d => polyAdd (f a b c d) (g a b c d)) count)
      (polyAdd (polySum4 f count) (polySum4 g count)) := by
  unfold polySum4
  exact (polySum_congr _ _ (fun a =>
    (polySum_congr _ _ (fun b =>
      (polySum_congr _ _ (fun c => polySum_add _ _ count) count).trans
        (polySum_add _ _ count)) count).trans (polySum_add _ _ count)) count).trans
    (polySum_add _ _ count)

private theorem polySum4_haar (f : Nat → Nat → Nat → Nat → RatPoly) (count : Nat) :
    quaternionHaar 1 (polySum4 f count) ≈
      finSum (fun a => finSum (fun b => finSum (fun c =>
        finSum (fun d => quaternionHaar 1 (f a b c d)) count) count) count) count :=
  Q'.eqv_trans _ _ _ (polySum_haar _ count)
    (finSum_eqv_congr _ _ (fun _a => Q'.eqv_trans _ _ _ (polySum_haar _ count)
      (finSum_eqv_congr _ _ (fun _b => Q'.eqv_trans _ _ _ (polySum_haar _ count)
        (finSum_eqv_congr _ _ (fun _c => polySum_haar _ count) count)) count)) count)

private def tensorSum (f0 f1 f2 f3 : Nat → RatPoly) (count : Nat) : RatPoly :=
  polySum4 (fun a b c d => prod4 (f0 a) (f1 b) (f2 c) (f3 d)) count

private theorem tensorSum_factorization (f0 f1 f2 f3 : Nat → RatPoly) (count : Nat) :
    RatPolyCoeffEqv (tensorSum f0 f1 f2 f3 count)
      (prod4 (polySum f0 count) (polySum f1 count)
        (polySum f2 count) (polySum f3 count)) := by
  have h23 : RatPolyCoeffEqv (polyMul (polySum f2 count) (polySum f3 count))
      (polySum (fun c => polySum (fun d => polyMul (f2 c) (f3 d)) count) count) :=
    (polySum_mul_right f2 (polySum f3 count) count).trans
      (polySum_congr _ _ (fun c => polySum_mul_left (f2 c) f3 count) count)
  have h123 : RatPolyCoeffEqv
      (polyMul (polySum f1 count) (polyMul (polySum f2 count) (polySum f3 count)))
      (polySum (fun b => polySum (fun c => polySum (fun d =>
        polyMul (f1 b) (polyMul (f2 c) (f3 d))) count) count) count) :=
    ((RatPolyCoeffEqv.refl _).mul h23).trans
      ((polySum_mul_right f1 _ count).trans
        (polySum_congr _ _ (fun b => (polySum_mul_left (f1 b) _ count).trans
          (polySum_congr _ _ (fun c => polySum_mul_left (f1 b) _ count) count)) count))
  exact (((RatPolyCoeffEqv.refl _).mul h123).trans
    ((polySum_mul_right f0 _ count).trans
      (polySum_congr _ _ (fun a => (polySum_mul_left (f0 a) _ count).trans
        (polySum_congr _ _ (fun b => (polySum_mul_left (f0 a) _ count).trans
          (polySum_congr _ _ (fun c => polySum_mul_left (f0 a) _ count) count)) count))
        count))).symm

private theorem distribute_discrepancy (b0 b1 b2 b3 d0 d1 d2 d3 : RatPoly) :
    RatPolyCoeffEqv (polyMul (prod4 b0 b1 b2 b3) (add4 d0 d1 d2 d3))
      (add4 (prod4 (polyMul b0 d0) b1 b2 b3)
        (prod4 b0 (polyMul b1 d1) b2 b3)
        (prod4 b0 b1 (polyMul b2 d2) b3)
        (prod4 b0 b1 b2 (polyMul b3 d3))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (eprod4 (.var 0) (.var 1) (.var 2) (.var 3))
      (esum4 (.var 4) (.var 5) (.var 6) (.var 7)))
    (esum4 (eprod4 (.mul (.var 0) (.var 4)) (.var 1) (.var 2) (.var 3))
      (eprod4 (.var 0) (.mul (.var 1) (.var 5)) (.var 2) (.var 3))
      (eprod4 (.var 0) (.var 1) (.mul (.var 2) (.var 6)) (.var 3))
      (eprod4 (.var 0) (.var 1) (.var 2) (.mul (.var 3) (.var 7))))
    (by decide)
    (fun | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
         | 4 => d0 | 5 => d1 | 6 => d2 | _ => d3)

/-- The actual joint discrepancy before the ORIGINAL Haar is applied. -/
def discrepancyPolynomial (n : Nat) : RatPoly :=
  polySum4 (fun a b c d => polyMul (jointBasisRaw n a b c d)
    (discrepancy (rawNode n a b c d))) (n+2)

private theorem variance_slot0 (n : Nat) : RatPolyCoeffEqv
    (tensorSum (varianceTerm n i0) (coordinateBasis n i1)
      (coordinateBasis n i2) (coordinateBasis n i3) (n+2))
    (coordinateVariance n i0) :=
  (tensorSum_factorization _ _ _ _ _).trans
    (((RatPolyCoeffEqv.refl _).mul ((coordinatePartition_sum n i1).mul
      ((coordinatePartition_sum n i2).mul (coordinatePartition_sum n i3)))).trans
      (((RatPolyCoeffEqv.refl _).mul ((RatPolyCoeffEqv.one_mul _).trans
        (RatPolyCoeffEqv.one_mul _))).trans (RatPolyCoeffEqv.mul_one _)))

private theorem variance_slot1 (n : Nat) : RatPolyCoeffEqv
    (tensorSum (coordinateBasis n i0) (varianceTerm n i1)
      (coordinateBasis n i2) (coordinateBasis n i3) (n+2))
    (coordinateVariance n i1) :=
  (tensorSum_factorization _ _ _ _ _).trans
    (((coordinatePartition_sum n i0).mul ((RatPolyCoeffEqv.refl _).mul
      ((coordinatePartition_sum n i2).mul (coordinatePartition_sum n i3)))).trans
      ((RatPolyCoeffEqv.one_mul _).trans
        (((RatPolyCoeffEqv.refl _).mul (RatPolyCoeffEqv.one_mul _)).trans
          (RatPolyCoeffEqv.mul_one _))))

private theorem variance_slot2 (n : Nat) : RatPolyCoeffEqv
    (tensorSum (coordinateBasis n i0) (coordinateBasis n i1)
      (varianceTerm n i2) (coordinateBasis n i3) (n+2))
    (coordinateVariance n i2) :=
  (tensorSum_factorization _ _ _ _ _).trans
    (((coordinatePartition_sum n i0).mul ((coordinatePartition_sum n i1).mul
      ((RatPolyCoeffEqv.refl _).mul (coordinatePartition_sum n i3)))).trans
      ((RatPolyCoeffEqv.one_mul _).trans ((RatPolyCoeffEqv.one_mul _).trans
        (RatPolyCoeffEqv.mul_one _))))

private theorem variance_slot3 (n : Nat) : RatPolyCoeffEqv
    (tensorSum (coordinateBasis n i0) (coordinateBasis n i1)
      (coordinateBasis n i2) (varianceTerm n i3) (n+2))
    (coordinateVariance n i3) :=
  (tensorSum_factorization _ _ _ _ _).trans
    (((coordinatePartition_sum n i0).mul ((coordinatePartition_sum n i1).mul
      ((coordinatePartition_sum n i2).mul (RatPolyCoeffEqv.refl _)))).trans
      ((RatPolyCoeffEqv.one_mul _).trans ((RatPolyCoeffEqv.one_mul _).trans
        (RatPolyCoeffEqv.one_mul _))))

/-- Tensor partition and variance are identities on the shared coordinates,
not a product-marginal probabilistic assumption. -/
theorem discrepancyPolynomial_variance (n : Nat) : RatPolyCoeffEqv
    (discrepancyPolynomial n)
    (add4 (coordinateVariance n i0) (coordinateVariance n i1)
      (coordinateVariance n i2) (coordinateVariance n i3)) := by
  have hterm : ∀ a b c d, RatPolyCoeffEqv
      (polyMul (jointBasisRaw n a b c d) (discrepancy (rawNode n a b c d)))
      (add4
        (prod4 (varianceTerm n i0 a) (coordinateBasis n i1 b)
          (coordinateBasis n i2 c) (coordinateBasis n i3 d))
        (prod4 (coordinateBasis n i0 a) (varianceTerm n i1 b)
          (coordinateBasis n i2 c) (coordinateBasis n i3 d))
        (prod4 (coordinateBasis n i0 a) (coordinateBasis n i1 b)
          (varianceTerm n i2 c) (coordinateBasis n i3 d))
        (prod4 (coordinateBasis n i0 a) (coordinateBasis n i1 b)
          (coordinateBasis n i2 c) (varianceTerm n i3 d))) := by
    intro a b c d
    exact distribute_discrepancy _ _ _ _ _ _ _ _
  exact (polySum4_congr _ _ hterm (n+2)).trans
    ((polySum4_add _ _ (n+2)).trans
      (((RatPolyCoeffEqv.refl _).add ((polySum4_add _ _ (n+2)).trans
        ((RatPolyCoeffEqv.refl _).add (polySum4_add _ _ (n+2))))).trans
        ((variance_slot0 n).add ((variance_slot1 n).add
          ((variance_slot2 n).add (variance_slot3 n))))))

private def sphereNorm : RatPoly :=
  add4 (polyMul (polyVar 0) (polyVar 0)) (polyMul (polyVar 1) (polyVar 1))
    (polyMul (polyVar 2) (polyVar 2)) (polyMul (polyVar 3) (polyVar 3))

private theorem variance_sum (n : Nat) : RatPolyCoeffEqv
    (add4 (coordinateVariance n i0) (coordinateVariance n i1)
      (coordinateVariance n i2) (coordinateVariance n i3))
    (polyMul (cap (Q'.invSucc n)) (polyAdd (cap 4) (polyNeg sphereNorm))) := by
  have hv (i : Fin 4) := (coordinateVariance_eq n i).trans
    (cap_mul_left (Q'.invSucc n)
      (polyAdd polyOne (polyNeg (polyMul (polyVar i.val) (polyVar i.val))))).symm
  exact ((hv i0).add ((hv i1).add ((hv i2).add (hv i3)))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (esum4 (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
        (.mul (.var 0) (.add (.const 1) (.neg (.var 2))))
        (.mul (.var 0) (.add (.const 1) (.neg (.var 3))))
        (.mul (.var 0) (.add (.const 1) (.neg (.var 4)))))
      (.mul (.var 0) (.add (.const 4)
        (.neg (esum4 (.var 1) (.var 2) (.var 3) (.var 4)))))
      (by decide)
      (fun | 0 => cap (Q'.invSucc n)
           | 1 => polyMul (polyVar 0) (polyVar 0)
           | 2 => polyMul (polyVar 1) (polyVar 1)
           | 3 => polyMul (polyVar 2) (polyVar 2)
           | _ => polyMul (polyVar 3) (polyVar 3)))

/-- Exact total discrepancy: four coordinate variances minus the SAME
one-block sphere norm. Valid also at the minimum degree n=0. -/
theorem jointDiscrepancy_eq (n : Nat) :
    jointDiscrepancy n ≈ 3 * Q'.invSucc n := by
  have hsphere : HaarCarrierEqv 1 sphereNorm polyOne := by
    change HaarCarrierEqv 1
      (polyQuaternionNorm (PolyQuaternion.coordinateVariable 0)) polyOne
    exact haarNorm_coordinate (blocks := 1) (block := 0) (by decide : 0 < 1)
  have hcarrier : HaarCarrierEqv 1 (discrepancyPolynomial n)
      (polyMul (cap (Q'.invSucc n)) (polyAdd (cap 4) (polyNeg polyOne))) :=
    HaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier ((discrepancyPolynomial_variance n).trans
        (variance_sum n)))
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl 1 _)
        (HaarCarrierEqv.add (HaarCarrierEqv.refl 1 _)
          (HaarCarrierEqv.neg hsphere)))
  have hconst : RatPolyCoeffEqv
      (polyMul (cap (Q'.invSucc n)) (polyAdd (cap 4) (polyNeg polyOne)))
      (polySmul (3 * Q'.invSucc n) polyOne) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.const 4) (.neg (.const 1))))
      (.mul (.const 3) (.var 0)) (by decide)
      (fun _ => cap (Q'.invSucc n))
      |>.trans (cap_mul 3 (Q'.invSucc n))
  have hhaar := Q'.eqv_trans _ _ _ (haar_of_carrier hcarrier)
    (Q'.eqv_trans _ _ _ (haar_of_coeff hconst)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 1 (3 * Q'.invSucc n) polyOne)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (by decide +kernel : quaternionHaar 1 polyOne ≈ 1))
          (Q'.mul_one_eqv _))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (polySum4_haar _ (n+2))) hhaar

/-- A fully rational finite norm-defect concentration bound, with the SAME
nonnegative joint weights and no continuous-Haar premise. -/
theorem jointNormDefect_le (n : Nat) :
    jointNormDefect n ≤ 48 * Q'.invSucc n := by
  have h := jointNormDefect_le_sixteen_discrepancy n
  have hpin : 16 * jointDiscrepancy n ≈ 48 * Q'.invSucc n :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (jointDiscrepancy_eq n))
      (poly_identity_of_normal_eq
        (.mul (.const 16) (.mul (.const 3) (.var 0)))
        (.mul (.const 48) (.var 0)) (by decide) (fun _ => Q'.invSucc n))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hpin)

end YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration.discrepancyPolynomial
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration.discrepancyPolynomial_variance
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration.jointDiscrepancy_eq
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration.jointNormDefect_le

/-
Pointwise tensor Bernstein concentration on the ACTUAL rational unit quaternion.
The weights are evaluations of the joint RatPoly basis, not its Haar averages.
No continuous Haar integral or completed-point approximation is asserted here.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
import YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance
import YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration
import YMGap.Continuum.BernsteinUniformConvergence

namespace YMGap.Continuum.QuaternionPointBernsteinConcentration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarCubeNormDefect
open YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
open YMGap.Continuum.QuaternionHaarBernsteinCoordinateVariance
open YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionNormRepair

local infix:50 " ≈ " => Q'.eqv

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t :: p => congrArg (fun z => t.2 * evalMono rho t.1 + z) (weighted_eval rho p)

private theorem eval_of_coeff (rho : Nat → Q') {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)

private theorem eval_cap (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (evalRatPoly_one rho))
      (Q'.mul_one_eqv c))

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem eval_ratFinSum (rho : Nat → Q') (f : Nat → RatPoly) :
    ∀ count, evalRatPoly rho (ratFinSum f count) ≈
      finSum (fun k => evalRatPoly rho (f k)) count
  | 0 => Q'.eqv_refl 0
  | count+1 => by
      change evalRatPoly rho (polyAdd (ratFinSum f count) (f count)) ≈
        finSum (fun k => evalRatPoly rho (f k)) count + evalRatPoly rho (f count)
      exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
        (Q'.add_eqv_congr_right _ _ _ (eval_ratFinSum rho f count))

private theorem eval_polySum (rho : Nat → Q') (f : Nat → RatPoly) :
    ∀ count, evalRatPoly rho (polySum f count) ≈
      finSum (fun k => evalRatPoly rho (f k)) count
  | 0 => Q'.eqv_refl 0
  | count+1 => by
      change evalRatPoly rho (polyAdd (polySum f count) (f count)) ≈
        finSum (fun k => evalRatPoly rho (f k)) count + evalRatPoly rho (f count)
      exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
        (Q'.add_eqv_congr_right _ _ _ (eval_polySum rho f count))

/-- Actual value of a joint polynomial basis at one rational unit quaternion. -/
def pointWeight (x : UnitNorm) (n a b c d : Nat) : Q' :=
  evalRatPoly (environmentOf x.val) (jointBasisRaw n a b c d)

private theorem abs_square (a : Q') : Q'.abs a * Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => a)

private theorem shifted_eval (rho : Nat → Q') (i : Fin 4) :
    evalRatPoly rho (shiftedCoordinate i) ≈
      YMGap.Constructive.HalfPow.half * (1 + rho i.val) := by
  have hpoly (z : Q') :
      QPoly.eval YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate.unitCoordinate z ≈
        YMGap.Constructive.HalfPow.half * (1+z) := by
    change (YMGap.Constructive.HalfPow.half +
      z * (YMGap.Constructive.HalfPow.half + z * 0)) ≈ _
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 1) (.add (.var 0) (.mul (.var 1) (.const 0)))))
      (.mul (.var 0) (.add (.const 1) (.var 1)))
      (by decide) (fun | 0 => YMGap.Constructive.HalfPow.half | _ => z)
  exact Q'.eqv_trans _ _ _
    (eval_subst rho (polyVar i.val)
      YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate.unitCoordinate)
    (Q'.eqv_trans _ _ _
      (hpoly (evalRatPoly rho (polyVar i.val)))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left 1 _ _ (evalRatPoly_var rho i.val))))

private theorem shifted_interval (x : UnitNorm) (i : Fin 4) :
    (0 : Q') ≤ evalRatPoly (environmentOf x.val) (shiftedCoordinate i) ∧
      evalRatPoly (environmentOf x.val) (shiftedCoordinate i) ≤ 1 := by
  let z := coordinate x.val i
  have hzsq : z*z ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (coordinate_square_le x.val i) (Q'.le_of_eqv x.unitNorm)
  have hzabs : Q'.abs z ≤ 1 :=
    CReal.le_of_sq_le_sq (by decide : (0 : Q') < 1) (Q'.abs_nonneg z)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square z))
        (Q'.le_trans' _ _ _ hzsq (Q'.le_of_eqv (by decide :
          Q'.eqv (1 : Q') (1*1)))))
  have hzlo : -(1 : Q') ≤ z :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hzabs) (ExpNeg.neg_abs_le z)
  have hzhi : z ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self z) hzabs
  have hsum0 : (0 : Q') ≤ 1+z :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : Q'.eqv (0 : Q') (1 + -(1 : Q'))))
      (Q'.add_le_add_left 1 _ _ hzlo)
  have hsum2 : 1+z ≤ (2 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ hzhi)
      (Q'.le_of_eqv (by decide : Q'.eqv (1 + (1 : Q')) (2 : Q')))
  have hy : evalRatPoly (environmentOf x.val) (shiftedCoordinate i) ≈
      YMGap.Constructive.HalfPow.half * (1+z) := by
    exact Q'.eqv_trans _ _ _ (shifted_eval (environmentOf x.val) i)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left 1 _ _
          (by rw [environmentOf_coordinate]; exact Q'.eqv_refl _)))
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ YMGap.Constructive.HalfPow.half_nonneg hsum0)
      (Q'.ge_of_eqv hy)
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hy)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum2
          YMGap.Constructive.HalfPow.half_nonneg)
        (Q'.le_of_eqv (by decide :
          Q'.eqv (YMGap.Constructive.HalfPow.half * 2) 1)))

private theorem eval_oneMinusVar (z : Q') :
    QPoly.eval oneMinusVar z ≈ 1 + -z := by
  change (1 + z * (-1 + z*0)) ≈ 1 + -z
  exact poly_identity_of_normal_eq
    (.add (.const 1) (.mul (.var 0)
      (.add (.neg (.const 1)) (.mul (.var 0) (.const 0)))))
    (.add (.const 1) (.neg (.var 0))) (by decide) (fun _ => z)

private theorem eval_basisPoly (D k : Nat) (z : Q') :
    QPoly.eval (bernsteinBasisPoly D k) z ≈ bernsteinBasis D z k := by
  unfold bernsteinBasisPoly bernsteinBasis
  have hv := eval_ppow_pvar z k
  have hm : QPoly.eval
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow oneMinusVar (D-k)) z ≈
        (1-z)^(D-k) :=
    Q'.eqv_trans _ _ _ (eval_ppow oneMinusVar z (D-k))
      (pow_eqv_congr (eval_oneMinusVar z) (D-k))
  exact Q'.eqv_trans _ _ _ (QPoly.eval_pmul
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow
        YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar k)
      (YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow oneMinusVar (D-k)) z)
    (mul_congr hv hm)

private theorem coordinateBasis_eval (rho : Nat → Q') (n : Nat)
    (i : Fin 4) (k : Nat) :
    evalRatPoly rho (coordinateBasis n i k) ≈
      Q'.ofNat (YMGap.RG.binom (degree n) k) *
        bernsteinBasis (degree n)
          (evalRatPoly rho (shiftedCoordinate i)) k := by
  unfold coordinateBasis
  exact Q'.eqv_trans _ _ _ (eval_subst rho _ _)
    (Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ _)
      (Q'.mul_eqv_congr_left _ _ _
        (eval_basisPoly (degree n) k _)))

private theorem coordinateBasis_point_nonnegative (x : UnitNorm) (n : Nat)
    (i : Fin 4) (k : Nat) :
    (0 : Q') ≤ evalRatPoly (environmentOf x.val) (coordinateBasis n i k) := by
  let y := evalRatPoly (environmentOf x.val) (shiftedCoordinate i)
  have hy := shifted_interval x i
  have hb : (0 : Q') ≤ bernsteinBasis (degree n) y k := by
    unfold bernsteinBasis
    exact Q'.mul_nonneg _ _ (Q'.pow_nonneg y hy.1 k)
      (Q'.pow_nonneg (1-y) (one_sub_nonneg hy.2) (degree n-k))
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (YMGap.RG.ofNat_nonneg _) hb)
    (Q'.ge_of_eqv (coordinateBasis_eval (environmentOf x.val) n i k))

/-- The literal pointwise Bernstein kernel is nonnegative. -/
theorem pointWeight_nonnegative (x : UnitNorm) (n a b c d : Nat) :
    (0 : Q') ≤ pointWeight x n a b c d := by
  have h0 := coordinateBasis_point_nonnegative x n ⟨0, by decide⟩ a
  have h1 := coordinateBasis_point_nonnegative x n ⟨1, by decide⟩ b
  have h2 := coordinateBasis_point_nonnegative x n ⟨2, by decide⟩ c
  have h3 := coordinateBasis_point_nonnegative x n ⟨3, by decide⟩ d
  have he : pointWeight x n a b c d ≈
      evalRatPoly (environmentOf x.val) (coordinateBasis n ⟨0, by decide⟩ a) *
      (evalRatPoly (environmentOf x.val) (coordinateBasis n ⟨1, by decide⟩ b) *
       (evalRatPoly (environmentOf x.val) (coordinateBasis n ⟨2, by decide⟩ c) *
        evalRatPoly (environmentOf x.val) (coordinateBasis n ⟨3, by decide⟩ d))) := by
    unfold pointWeight jointBasisRaw
    exact Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_mul _ _ _))))
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ h0 (Q'.mul_nonneg _ _ h1
      (Q'.mul_nonneg _ _ h2 h3))) (Q'.ge_of_eqv he)

/-- Literal same-point fourfold mass, with no Haar averaging of the weights. -/
def pointMass (x : UnitNorm) (n : Nat) : Q' :=
  sum4 (pointWeight x n) (n+2)

private theorem eval_jointPolynomial (rho : Nat → Q') (n : Nat) :
    evalRatPoly rho (jointPolynomial n) ≈
      sum4 (fun a b c d => evalRatPoly rho (jointBasisRaw n a b c d)) (n+2) := by
  unfold jointPolynomial sum4
  exact Q'.eqv_trans _ _ _ (eval_ratFinSum rho _ (n+2))
    (finSum_eqv_congr _ _ (fun a => Q'.eqv_trans _ _ _
      (eval_ratFinSum rho _ (n+2))
      (finSum_eqv_congr _ _ (fun b => Q'.eqv_trans _ _ _
        (eval_ratFinSum rho _ (n+2))
        (finSum_eqv_congr _ _ (fun c => eval_ratFinSum rho _ (n+2))
          (n+2))) (n+2))) (n+2))

/-- Pointwise partition of unity of the literal joint RatPoly Bernstein row. -/
theorem pointMass_one (x : UnitNorm) (n : Nat) : pointMass x n ≈ 1 := by
  have hones : RatPolyCoeffEqv
      (polyMul (coordinatePartition n ⟨0, by decide⟩)
        (polyMul (coordinatePartition n ⟨1, by decide⟩)
          (polyMul (coordinatePartition n ⟨2, by decide⟩)
            (coordinatePartition n ⟨3, by decide⟩)))) polyOne :=
    (((coordinatePartition_one n ⟨0, by decide⟩).mul
      ((coordinatePartition_one n ⟨1, by decide⟩).mul
        ((coordinatePartition_one n ⟨2, by decide⟩).mul
          (coordinatePartition_one n ⟨3, by decide⟩)))).trans
      ((RatPolyCoeffEqv.one_mul _).trans
        ((RatPolyCoeffEqv.one_mul _).trans (RatPolyCoeffEqv.one_mul _))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_jointPolynomial (environmentOf x.val) n))
    (Q'.eqv_trans _ _ _
      (eval_of_coeff (environmentOf x.val)
        ((jointPolynomial_eq_partitions n).symm.trans hones))
      (evalRatPoly_one (environmentOf x.val)))

/-- The squared raw-node distance with the SAME pointwise weights. -/
def pointRawDistance (x : UnitNorm) (n : Nat) : Q' :=
  sum4 (fun a b c d => pointWeight x n a b c d *
    distSq (rawQuaternion n a b c d) x.val) (n+2)

private theorem eval_coordDifference (rho : Nat → Q') (r : CubeNode) (i : Fin 4) :
    evalRatPoly rho (coordDifference r i) ≈ r i + -(rho i.val) := by
  unfold coordDifference
  exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (eval_cap rho (r i))
      (Q'.eqv_trans _ _ _ (evalRatPoly_neg rho _)
        (Q'.neg_eqv_congr _ _ (evalRatPoly_var rho i.val))))

private theorem eval_discrepancy (rho : Nat → Q') (r : CubeNode) :
    evalRatPoly rho (discrepancy r) ≈
      ((r ⟨0, by decide⟩ + -(rho 0)) * (r ⟨0, by decide⟩ + -(rho 0)) +
        (r ⟨1, by decide⟩ + -(rho 1)) * (r ⟨1, by decide⟩ + -(rho 1))) +
      ((r ⟨2, by decide⟩ + -(rho 2)) * (r ⟨2, by decide⟩ + -(rho 2)) +
        (r ⟨3, by decide⟩ + -(rho 3)) * (r ⟨3, by decide⟩ + -(rho 3))) := by
  have h0 := eval_coordDifference rho r ⟨0, by decide⟩
  have h1 := eval_coordDifference rho r ⟨1, by decide⟩
  have h2 := eval_coordDifference rho r ⟨2, by decide⟩
  have h3 := eval_coordDifference rho r ⟨3, by decide⟩
  have hraw : evalRatPoly rho (discrepancy r) ≈
      (r ⟨0, by decide⟩ + -(rho 0)) * (r ⟨0, by decide⟩ + -(rho 0)) +
      ((r ⟨1, by decide⟩ + -(rho 1)) * (r ⟨1, by decide⟩ + -(rho 1)) +
       ((r ⟨2, by decide⟩ + -(rho 2)) * (r ⟨2, by decide⟩ + -(rho 2)) +
        (r ⟨3, by decide⟩ + -(rho 3)) * (r ⟨3, by decide⟩ + -(rho 3)))) := by
    unfold discrepancy
    exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
          (mul_congr h0 h0))
        (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
              (mul_congr h1 h1))
            (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
              (Q'.add_eqv_congr'
                (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
                  (mul_congr h2 h2))
                (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
                  (mul_congr h3 h3)))))))
  exact Q'.eqv_trans _ _ _ hraw
    (poly_identity_of_normal_eq
      (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (by decide)
      (fun | 0 => (r ⟨0, by decide⟩ + -(rho 0)) *
                   (r ⟨0, by decide⟩ + -(rho 0))
           | 1 => (r ⟨1, by decide⟩ + -(rho 1)) *
                   (r ⟨1, by decide⟩ + -(rho 1))
           | 2 => (r ⟨2, by decide⟩ + -(rho 2)) *
                   (r ⟨2, by decide⟩ + -(rho 2))
           | _ => (r ⟨3, by decide⟩ + -(rho 3)) *
                   (r ⟨3, by decide⟩ + -(rho 3))))

private theorem eval_discrepancy_raw (x : UnitNorm) (n a b c d : Nat) :
    evalRatPoly (environmentOf x.val) (discrepancy (rawNode n a b c d)) ≈
      distSq (rawQuaternion n a b c d) x.val := by
  have h := eval_discrepancy (environmentOf x.val) (rawNode n a b c d)
  exact Q'.eqv_trans _ _ _ h (by
    simpa only [environmentOf_coordinate, rawQuaternion_coordinate,
      RationalQuaternionNormRepair.coordinate, distSq, rawNode, rawQuaternion] using
      (Q'.eqv_refl (distSq (rawQuaternion n a b c d) x.val)))

private theorem eval_discrepancyPolynomial (x : UnitNorm) (n : Nat) :
    evalRatPoly (environmentOf x.val) (discrepancyPolynomial n) ≈
      pointRawDistance x n := by
  let rho := environmentOf x.val
  have hterm (a b c d : Nat) :
      evalRatPoly rho (polyMul (jointBasisRaw n a b c d)
        (discrepancy (rawNode n a b c d))) ≈
      pointWeight x n a b c d * distSq (rawQuaternion n a b c d) x.val :=
    Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (Q'.mul_eqv_congr_left _ _ _ (eval_discrepancy_raw x n a b c d))
  unfold discrepancyPolynomial pointRawDistance sum4
  exact Q'.eqv_trans _ _ _ (eval_polySum rho _ (n+2))
    (finSum_eqv_congr _ _ (fun a => Q'.eqv_trans _ _ _
      (eval_polySum rho _ (n+2))
      (finSum_eqv_congr _ _ (fun b => Q'.eqv_trans _ _ _
        (eval_polySum rho _ (n+2))
        (finSum_eqv_congr _ _ (fun c => Q'.eqv_trans _ _ _
          (eval_polySum rho _ (n+2))
          (finSum_eqv_congr _ _ (fun d => hterm a b c d) (n+2)))
          (n+2))) (n+2))) (n+2))

private theorem coordinateVariance_eval (rho : Nat → Q') (n : Nat)
    (i : Fin 4) :
    evalRatPoly rho (coordinateVariance n i) ≈
      Q'.invSucc n * (1 + -(rho i.val * rho i.val)) := by
  have h := eval_of_coeff rho (coordinateVariance_eq n i)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (evalRatPoly_smul rho (Q'.invSucc n) _)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
          (Q'.add_eqv_congr' (evalRatPoly_one rho)
            (Q'.eqv_trans _ _ _ (evalRatPoly_neg rho _)
              (Q'.neg_eqv_congr _ _
                (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
                  (mul_congr (evalRatPoly_var rho i.val)
                    (evalRatPoly_var rho i.val)))))))))

private theorem eval_variance4 (rho : Nat → Q') (n : Nat) :
    evalRatPoly rho
      (polyAdd (coordinateVariance n ⟨0, by decide⟩)
        (polyAdd (coordinateVariance n ⟨1, by decide⟩)
          (polyAdd (coordinateVariance n ⟨2, by decide⟩)
            (coordinateVariance n ⟨3, by decide⟩)))) ≈
      Q'.invSucc n * (1 + -(rho 0*rho 0)) +
      (Q'.invSucc n * (1 + -(rho 1*rho 1)) +
       (Q'.invSucc n * (1 + -(rho 2*rho 2)) +
        Q'.invSucc n * (1 + -(rho 3*rho 3)))) := by
  exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (coordinateVariance_eval rho n ⟨0, by decide⟩)
      (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
        (Q'.add_eqv_congr' (coordinateVariance_eval rho n ⟨1, by decide⟩)
          (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
            (Q'.add_eqv_congr'
              (coordinateVariance_eval rho n ⟨2, by decide⟩)
              (coordinateVariance_eval rho n ⟨3, by decide⟩))))))

/-- Exact pointwise tensor variance, including `n=0`. This is not the Haar
joint-discrepancy identity: it evaluates the coefficient identity at `x`. -/
theorem pointRawDistance_eq (x : UnitNorm) (n : Nat) :
    pointRawDistance x n ≈ 3 * Q'.invSucc n := by
  let rho := environmentOf x.val
  let t := Q'.invSucc n
  have hcoeff := eval_of_coeff rho (discrepancyPolynomial_variance n)
  have hbasic : pointRawDistance x n ≈
      t*(1 + -(rho 0*rho 0)) +
      (t*(1 + -(rho 1*rho 1)) +
       (t*(1 + -(rho 2*rho 2)) +
        t*(1 + -(rho 3*rho 3)))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_discrepancyPolynomial x n))
      (Q'.eqv_trans _ _ _ hcoeff (eval_variance4 rho n))
  have hring :
      t*(1 + -(rho 0*rho 0)) +
      (t*(1 + -(rho 1*rho 1)) +
       (t*(1 + -(rho 2*rho 2)) +
        t*(1 + -(rho 3*rho 3)))) ≈
      t*(4 + -(normSq x.val)) := by
    have h0 : rho 0 = x.val.r := rfl
    have h1 : rho 1 = x.val.i := rfl
    have h2 : rho 2 = x.val.j := rfl
    have h3 : rho 3 = x.val.k := rfl
    rw [h0, h1, h2, h3]
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.const 1) (.neg (.mul (.var 1) (.var 1)))))
        (.add (.mul (.var 0) (.add (.const 1) (.neg (.mul (.var 2) (.var 2)))))
          (.add (.mul (.var 0) (.add (.const 1) (.neg (.mul (.var 3) (.var 3)))))
            (.mul (.var 0) (.add (.const 1) (.neg (.mul (.var 4) (.var 4))))))))
      (.mul (.var 0) (.add (.const 4)
        (.neg (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))
          (.add (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4)))))))
      (by decide)
      (fun | 0 => t | 1 => x.val.r | 2 => x.val.i
           | 3 => x.val.j | _ => x.val.k)
  have hunit : t*(4 + -(normSq x.val)) ≈ t*(4 + -1) :=
    Q'.mul_eqv_congr_left t _ _
      (Q'.add_eqv_congr_left 4 _ _
        (Q'.neg_eqv_congr _ _ x.unitNorm))
  have hlast : t*(4 + -1) ≈ 3*t :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.const 4) (.neg (.const 1))))
      (.mul (.const 3) (.var 0)) (by decide) (fun _ => t)
  exact Q'.eqv_trans _ _ _ hbasic
    (Q'.eqv_trans _ _ _ hring (Q'.eqv_trans _ _ _ hunit hlast))

#print axioms pointWeight
#print axioms pointWeight_nonnegative
#print axioms pointMass
#print axioms pointMass_one
#print axioms pointRawDistance
#print axioms pointRawDistance_eq

end YMGap.Continuum.QuaternionPointBernsteinConcentration

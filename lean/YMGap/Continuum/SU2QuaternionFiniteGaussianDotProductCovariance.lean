/-
# Connected covariance of finite Gaussian row dot products

This leaf consumes the checked arbitrary four-row Gaussian moment.  A finite
row dot product is represented literally as a finite sum of products of the
existing rational linear rows.  Its mean is the corresponding Gram trace,
and the connected covariance of two such dots is the finite double sum of
the two cross-pairings left after exact cancellation of the disconnected
pairing.

Taking both component counts to be three gives the expectation-level algebra
needed by every dot-times-norm and dot-times-dot term in the quartic Cayley
coefficient H4.  This module does not yet assemble that signed H4 expression,
identify an original interacting law, bound a normalized denominator, or
prove a physical mass gap.  Variables outside the finite Gaussian prefix are
evaluated at ONE by the existing evaluator; no tail-coefficient statement is
made.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment
import YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment

local infix:50 " ≈ " => Q'.eqv

/-- Literal dot product of two finite families of rational Gaussian rows. -/
def finiteGaussianRowDot (N componentCount : Nat)
    (left right : Nat → Nat → Q') : RatPoly :=
  polySum ((List.range componentCount).map fun component =>
    polyMul (finiteLinearRow N (left component))
      (finiteLinearRow N (right component)))

/-- Gram-trace value of the same finite row dot product. -/
def finiteRowDotGram (N componentCount : Nat)
    (left right : Nat → Nat → Q') : Q' :=
  qListSum ((List.range componentCount).map fun component =>
    finiteRowGram N (left component) (right component))

/-- The two connected cross-pairings for two finite row dot products. -/
def finiteRowDotConnectedGram (N leftCount rightCount : Nat)
    (a b c d : Nat → Nat → Q') : Q' :=
  qListSum ((List.range leftCount).map fun leftComponent =>
    qListSum ((List.range rightCount).map fun rightComponent =>
      finiteRowGram N (a leftComponent) (c rightComponent) *
          finiteRowGram N (b leftComponent) (d rightComponent) +
        finiteRowGram N (a leftComponent) (d rightComponent) *
          finiteRowGram N (b leftComponent) (c rightComponent)))

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem gaussian_zero (N : Nat) :
    finiteProductGaussian N polyZero ≈ 0 := by
  rw [finiteProductGaussian_probe]
  exact Q'.eqv_refl _

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_polySum (N : Nat) : ∀ polynomials : List RatPoly,
    finiteProductGaussian N (polySum polynomials) ≈
      qListSum (polynomials.map fun polynomial =>
        finiteProductGaussian N polynomial)
  | [] => gaussian_zero N
  | polynomial :: polynomials =>
      Q'.eqv_trans _ _ _ (gaussian_add N polynomial (polySum polynomials))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (gaussian_polySum N polynomials))

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ ids : List A,
    (∀ i, i ∈ ids → f i ≈ g i) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | i :: ids, h => Q'.add_eqv_congr' (h i List.mem_cons_self)
      (qListSum_congr f g ids (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- The finite Gaussian mean of a literal row dot is its computed Gram
trace, with no independence or nondegeneracy premise. -/
theorem finiteProductGaussian_row_dot (N componentCount : Nat)
    (left right : Nat → Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianRowDot N componentCount left right) ≈
      finiteRowDotGram N componentCount left right := by
  unfold finiteGaussianRowDot finiteRowDotGram
  exact Q'.eqv_trans _ _ _
    (gaussian_polySum N
      ((List.range componentCount).map fun component =>
        polyMul (finiteLinearRow N (left component))
          (finiteLinearRow N (right component))))
    (by
      simp only [List.map_map]
      exact qListSum_congr _ _ (List.range componentCount)
        (fun component _ =>
          finiteProductGaussian_row_pair N
            (left component) (right component)))

private theorem covariance_add_left (N : Nat) (p q r : RatPoly) :
    finiteGaussianCovariance N (polyAdd p q) r ≈
      finiteGaussianCovariance N p r + finiteGaussianCovariance N q r := by
  unfold finiteGaussianCovariance
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (gaussian_add N (polyMul p r) (polyMul q r))
      (Q'.neg_eqv_congr _ _
        (mul_congr (gaussian_add N p q) (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.add (.var 2) (.var 3)) (.var 4))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 4))))
        (.add (.var 1) (.neg (.mul (.var 3) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul p r)
        | 1 => finiteProductGaussian N (polyMul q r)
        | 2 => finiteProductGaussian N p
        | 3 => finiteProductGaussian N q
        | _ => finiteProductGaussian N r))

private theorem covariance_add_right (N : Nat) (p q r : RatPoly) :
    finiteGaussianCovariance N p (polyAdd q r) ≈
      finiteGaussianCovariance N p q + finiteGaussianCovariance N p r := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (RatPolyCoeffEqv.mul_add_right p q r))
        (gaussian_add N (polyMul p q) (polyMul p r)))
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_refl _) (gaussian_add N q r))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.add (.var 3) (.var 4)))))
      (.add
        (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
        (.add (.var 1) (.neg (.mul (.var 2) (.var 4)))))
      (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul p q)
        | 1 => finiteProductGaussian N (polyMul p r)
        | 2 => finiteProductGaussian N p
        | 3 => finiteProductGaussian N q
        | _ => finiteProductGaussian N r))

private theorem covariance_zero_left (N : Nat) (q : RatPoly) :
    finiteGaussianCovariance N polyZero q ≈ 0 := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (gaussian_zero N)
      (Q'.neg_eqv_congr _ _
        (mul_congr (gaussian_zero N) (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.const 0) (.var 0))))
      (.const 0) (by decide) (fun _ => finiteProductGaussian N q))

private theorem covariance_zero_right (N : Nat) (p : RatPoly) :
    finiteGaussianCovariance N p polyZero ≈ 0 := by
  unfold finiteGaussianCovariance
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (RatPolyCoeffEqv.mul_zero_right p))
        (gaussian_zero N))
      (Q'.neg_eqv_congr _ _
        (mul_congr (Q'.eqv_refl _) (gaussian_zero N))))
    (poly_identity_of_normal_eq
      (.add (.const 0) (.neg (.mul (.var 0) (.const 0))))
      (.const 0) (by decide) (fun _ => finiteProductGaussian N p))

private theorem covariance_polySum_left (N : Nat) (q : RatPoly) :
    ∀ polynomials : List RatPoly,
      finiteGaussianCovariance N (polySum polynomials) q ≈
        qListSum (polynomials.map fun polynomial =>
          finiteGaussianCovariance N polynomial q)
  | [] => covariance_zero_left N q
  | polynomial :: polynomials =>
      Q'.eqv_trans _ _ _
        (covariance_add_left N polynomial (polySum polynomials) q)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (covariance_polySum_left N q polynomials))

private theorem covariance_polySum_right (N : Nat) (p : RatPoly) :
    ∀ polynomials : List RatPoly,
      finiteGaussianCovariance N p (polySum polynomials) ≈
        qListSum (polynomials.map fun polynomial =>
          finiteGaussianCovariance N p polynomial)
  | [] => covariance_zero_right N p
  | polynomial :: polynomials =>
      Q'.eqv_trans _ _ _
        (covariance_add_right N p polynomial (polySum polynomials))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (covariance_polySum_right N p polynomials))

private theorem row_dot_covariance_expansion
    (N leftCount rightCount : Nat) (a b c d : Nat → Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRowDot N leftCount a b)
        (finiteGaussianRowDot N rightCount c d) ≈
      qListSum ((List.range leftCount).map fun leftComponent =>
        qListSum ((List.range rightCount).map fun rightComponent =>
          finiteGaussianCovariance N
            (polyMul (finiteLinearRow N (a leftComponent))
              (finiteLinearRow N (b leftComponent)))
            (polyMul (finiteLinearRow N (c rightComponent))
              (finiteLinearRow N (d rightComponent))))) := by
  let leftProducts := (List.range leftCount).map fun component =>
    polyMul (finiteLinearRow N (a component))
      (finiteLinearRow N (b component))
  let rightProducts := (List.range rightCount).map fun component =>
    polyMul (finiteLinearRow N (c component))
      (finiteLinearRow N (d component))
  have hleft := covariance_polySum_left N (polySum rightProducts) leftProducts
  have hright :
      qListSum (leftProducts.map fun leftProduct =>
        finiteGaussianCovariance N leftProduct (polySum rightProducts)) ≈
      qListSum (leftProducts.map fun leftProduct =>
        qListSum (rightProducts.map fun rightProduct =>
          finiteGaussianCovariance N leftProduct rightProduct)) :=
    qListSum_congr _ _ leftProducts (fun leftProduct _ =>
      covariance_polySum_right N leftProduct rightProducts)
  simpa only [finiteGaussianRowDot, leftProducts, rightProducts, List.map_map]
    using Q'.eqv_trans _ _ _ hleft hright

/-- Connected covariance of two literal finite Gaussian row dot products.
The result retains exactly the two cross-pairings; the disconnected product
of Gram traces is absent by checked cancellation. -/
theorem finiteGaussianCovariance_row_dots
    (N leftCount rightCount : Nat) (a b c d : Nat → Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRowDot N leftCount a b)
        (finiteGaussianRowDot N rightCount c d) ≈
      finiteRowDotConnectedGram N leftCount rightCount a b c d := by
  exact Q'.eqv_trans _ _ _
    (row_dot_covariance_expansion N leftCount rightCount a b c d)
    (by
      unfold finiteRowDotConnectedGram
      exact qListSum_congr _ _ (List.range leftCount)
        (fun leftComponent _ =>
          qListSum_congr _ _ (List.range rightCount)
            (fun rightComponent _ => by
              unfold finiteGaussianCovariance
              exact finiteProductGaussian_four_rows_connected N
                (a leftComponent) (b leftComponent)
                (c rightComponent) (d rightComponent))))

/-- Raw fourth moment of two literal row dots.  It is the product of their
Gram traces plus the checked connected cross-pairing sum. -/
theorem finiteProductGaussian_row_dot_product
    (N leftCount rightCount : Nat) (a b c d : Nat → Nat → Q') :
    finiteProductGaussian N
        (polyMul (finiteGaussianRowDot N leftCount a b)
          (finiteGaussianRowDot N rightCount c d)) ≈
      finiteRowDotGram N leftCount a b *
          finiteRowDotGram N rightCount c d +
        finiteRowDotConnectedGram N leftCount rightCount a b c d := by
  have hmeans :
      finiteProductGaussian N (finiteGaussianRowDot N leftCount a b) *
          finiteProductGaussian N (finiteGaussianRowDot N rightCount c d) ≈
        finiteRowDotGram N leftCount a b *
          finiteRowDotGram N rightCount c d :=
    mul_congr
      (finiteProductGaussian_row_dot N leftCount a b)
      (finiteProductGaussian_row_dot N rightCount c d)
  have hcov := finiteGaussianCovariance_row_dots
    N leftCount rightCount a b c d
  have hsum := Q'.add_eqv_congr' hcov hmeans
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.var 0)
      (.add
        (.add (.var 0) (.neg (.var 1)))
        (.var 1))
      (by decide) (fun
        | 0 => finiteProductGaussian N
            (polyMul (finiteGaussianRowDot N leftCount a b)
              (finiteGaussianRowDot N rightCount c d))
        | _ => finiteProductGaussian N
            (finiteGaussianRowDot N leftCount a b) *
          finiteProductGaussian N
            (finiteGaussianRowDot N rightCount c d)))
    (Q'.eqv_trans _ _ _ hsum
      (poly_identity_of_normal_eq
        (.add (.var 0) (.var 1))
        (.add (.var 1) (.var 0))
        (by decide) (fun
          | 0 => finiteRowDotConnectedGram N leftCount rightCount a b c d
          | _ => finiteRowDotGram N leftCount a b *
            finiteRowDotGram N rightCount c d)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance.finiteProductGaussian_row_dot
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance.finiteGaussianCovariance_row_dots
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance.finiteProductGaussian_row_dot_product

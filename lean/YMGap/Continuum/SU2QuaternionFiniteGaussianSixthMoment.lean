/-
# Computed rational-row mixed fourth and three-square sixth moments

This leaf uses the EXISTING finiteProductGaussian, finiteLinearRow,
finiteRowDerivative, finiteRowNorm2 and finiteRowGram. First Stein, row Leibniz
and the checked mixed derivative contraction PRODUCE all moment formulas.
There is no Gaussian/moment/pullback law or Gram identity among the premises.
All finite N, including zero, and zero or degenerate rational rows are covered.
Variables outside N evaluate at ONE; no coefficient-preserved tails are claimed.
Padded zero monomials in derivatives are contracted under this SAME evaluator,
not equated with polyConst under arbitrary coefficient probes.

The literal covariance here is Cov(B^2*D^2,E^2), with both actual finite
Gaussian means retained. Its finite radial sum is the consumer
Cov(S_B^2,S_D)=8*Tr(Sigma*K*K^*)+4*Tr(Sigma)*Tr(K*K^*) in the adaptive-score
audit. That summation, actual transverse mode rows and CReal moduli, and the
ORIGINAL compact-Haar/section/source/OLD-center comparison remain separate.
No original-law pin, interacting uniform estimate or physical gap is claimed.
Root serializes compilation and axiom checks.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment

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

local infix:50 " ≈ " => Q'.eqv

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem swap_first_two (p q r : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyMul q r)) (polyMul q (polyMul p r)) :=
  RatPolyCoeffEqv.trans (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.mul_assoc p q r))
    (RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm p q).mul_right r)
      (RatPolyCoeffEqv.mul_assoc q p r))

private theorem swap_last_two (p q r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul p q) r) (polyMul (polyMul p r) q) :=
  RatPolyCoeffEqv.trans (RatPolyCoeffEqv.mul_assoc p q r)
    (RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm q r).mul_left p)
      (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.mul_assoc p r q)))

private theorem twice_scalar (x : Q') : x+x ≈ 2*x :=
  poly_identity_of_normal_eq (.add (.var 0) (.var 0))
    (.mul (.const 2) (.var 0)) (by decide) (fun _ => x)

private theorem row_pair_insert (N : Nat) (u v : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N (polyMul (polyMul (finiteLinearRow N u) (finiteLinearRow N v)) p) ≈
      finiteRowGram N u v * finiteProductGaussian N p +
        finiteProductGaussian N (polyMul (finiteLinearRow N v) (finiteRowDerivative N u p)) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_assoc _ _ p))
    (Q'.eqv_trans _ _ _ (finiteProductGaussian_linearRow_stein N u (polyMul (finiteLinearRow N v) p))
      (Q'.eqv_trans _ _ _ (finiteProductGaussian_coeffEqv N
        (finiteRowDerivative_mul N u (finiteLinearRow N v) p))
        (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
          (Q'.add_eqv_congr' (finiteRowDerivative_mixed_contraction N u v p) (Q'.eqv_refl _)))))

private theorem square_derivative_contract (N : Nat) (u v : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N (polyMul p
      (finiteRowDerivative N u (polyMul (finiteLinearRow N v) (finiteLinearRow N v)))) ≈
      2 * (finiteRowGram N u v * finiteProductGaussian N (polyMul p (finiteLinearRow N v))) := by
  let V := finiteLinearRow N v
  let C := finiteRowDerivative N u V
  have hleft : RatPolyCoeffEqv (polyMul p (polyMul C V)) (polyMul C (polyMul p V)) :=
    swap_first_two p C V
  have hright : RatPolyCoeffEqv (polyMul p (polyMul V C)) (polyMul C (polyMul p V)) :=
    RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm V C).mul_left p) hleft
  have hsplit := RatPolyCoeffEqv.trans ((finiteRowDerivative_mul N u V V).mul_left p)
    (RatPolyCoeffEqv.trans (RatPolyCoeffEqv.mul_add_right p (polyMul C V) (polyMul V C))
      (RatPolyCoeffEqv.add hleft hright))
  exact Q'.eqv_trans _ _ _ (finiteProductGaussian_coeffEqv N hsplit)
    (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (finiteRowDerivative_mixed_contraction N u v (polyMul p V))
          (finiteRowDerivative_mixed_contraction N u v (polyMul p V)))
        (twice_scalar _)))

/-- Actual mixed fourth moment B*D*E^2, with all Grams computed from rows. -/
theorem finiteProductGaussian_mixed_fourth (N : Nat) (b d e : Nat → Q') :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N d))
        (polyMul (finiteLinearRow N e) (finiteLinearRow N e))) ≈
      finiteRowGram N b d * finiteRowNorm2 N e +
        2 * (finiteRowGram N b e * finiteRowGram N d e) := by
  exact Q'.eqv_trans _ _ _ (row_pair_insert N b d (polyMul (finiteLinearRow N e) (finiteLinearRow N e)))
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N e e))
      (Q'.eqv_trans _ _ _ (square_derivative_contract N b e (finiteLinearRow N d))
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N d e)))))

private theorem square_product_derivative_contract (N : Nat)
    (u v w : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N (polyMul p (finiteRowDerivative N u
      (polyMul (polyMul (finiteLinearRow N v) (finiteLinearRow N v))
        (polyMul (finiteLinearRow N w) (finiteLinearRow N w))))) ≈
      2 * (finiteRowGram N u v * finiteProductGaussian N
        (polyMul (polyMul p (finiteLinearRow N v))
          (polyMul (finiteLinearRow N w) (finiteLinearRow N w)))) +
      2 * (finiteRowGram N u w * finiteProductGaussian N
        (polyMul (polyMul p (finiteLinearRow N w))
          (polyMul (finiteLinearRow N v) (finiteLinearRow N v)))) := by
  let V := finiteLinearRow N v
  let W := finiteLinearRow N w
  let V2 := polyMul V V
  let W2 := polyMul W W
  let Cv := finiteRowDerivative N u V2
  let Cw := finiteRowDerivative N u W2
  have hleft : RatPolyCoeffEqv (polyMul p (polyMul Cv W2)) (polyMul (polyMul p W2) Cv) :=
    RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm Cv W2).mul_left p)
      (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.mul_assoc p W2 Cv))
  have hright : RatPolyCoeffEqv (polyMul p (polyMul V2 Cw)) (polyMul (polyMul p V2) Cw) :=
    RatPolyCoeffEqv.symm (RatPolyCoeffEqv.mul_assoc p V2 Cw)
  have hsplit := RatPolyCoeffEqv.trans ((finiteRowDerivative_mul N u V2 W2).mul_left p)
    (RatPolyCoeffEqv.trans (RatPolyCoeffEqv.mul_add_right p (polyMul Cv W2) (polyMul V2 Cw))
      (RatPolyCoeffEqv.add hleft hright))
  have hfirst := Q'.eqv_trans _ _ _ (square_derivative_contract N u v (polyMul p W2))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (finiteProductGaussian_coeffEqv N (swap_last_two p W2 V))))
  have hsecond := Q'.eqv_trans _ _ _ (square_derivative_contract N u w (polyMul p V2))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (finiteProductGaussian_coeffEqv N (swap_last_two p V2 W))))
  exact Q'.eqv_trans _ _ _ (finiteProductGaussian_coeffEqv N hsplit)
    (Q'.eqv_trans _ _ _ (gaussian_add N _ _) (Q'.add_eqv_congr' hfirst hsecond))

private theorem sixth_scalar (a c f x y z : Q') :
    a*(c*f+2*(z*z)) +
      (2*(x*(x*f+2*(y*z))) + 2*(y*(y*c+2*(x*z)))) ≈
      a*c*f + 2*(a*(z*z)+c*(y*y)+f*(x*x)) + 8*x*y*z := by
  let A : PolyExpr := .var 0
  let C : PolyExpr := .var 1
  let F : PolyExpr := .var 2
  let X : PolyExpr := .var 3
  let Y : PolyExpr := .var 4
  let Z : PolyExpr := .var 5
  exact poly_identity_of_normal_eq
    (.add (.mul A (.add (.mul C F) (.mul (.const 2) (.mul Z Z))))
      (.add (.mul (.const 2) (.mul X (.add (.mul X F) (.mul (.const 2) (.mul Y Z)))))
        (.mul (.const 2) (.mul Y (.add (.mul Y C) (.mul (.const 2) (.mul X Z)))))))
    (.add (.add (.mul (.mul A C) F)
      (.mul (.const 2) (.add (.add (.mul A (.mul Z Z)) (.mul C (.mul Y Y))) (.mul F (.mul X X)))))
      (.mul (.mul (.mul (.const 8) X) Y) Z))
    (by decide) (fun | 0 => a | 1 => c | 2 => f | 3 => x | 4 => y | _ => z)

/-- Computed three-square sixth moment. No independence, nonzero variance or
change-of-basis hypothesis is needed, including empty and degenerate rows. -/
theorem finiteProductGaussian_three_square_sixth (N : Nat) (b d e : Nat → Q') :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N b))
        (polyMul (polyMul (finiteLinearRow N d) (finiteLinearRow N d))
          (polyMul (finiteLinearRow N e) (finiteLinearRow N e)))) ≈
      finiteRowNorm2 N b * finiteRowNorm2 N d * finiteRowNorm2 N e +
      2 * (finiteRowNorm2 N b * (finiteRowGram N d e * finiteRowGram N d e) +
        finiteRowNorm2 N d * (finiteRowGram N b e * finiteRowGram N b e) +
        finiteRowNorm2 N e * (finiteRowGram N b d * finiteRowGram N b d)) +
      8 * finiteRowGram N b d * finiteRowGram N b e * finiteRowGram N d e := by
  let B := finiteLinearRow N b
  let D := finiteLinearRow N d
  let E := finiteLinearRow N e
  let a := finiteRowNorm2 N b
  let c := finiteRowNorm2 N d
  let f := finiteRowNorm2 N e
  let x := finiteRowGram N b d
  let y := finiteRowGram N b e
  let z := finiteRowGram N d e
  have hmixedReverse : finiteProductGaussian N (polyMul (polyMul B E) (polyMul D D)) ≈
      y*c+2*(x*z) :=
    Q'.eqv_trans _ _ _ (finiteProductGaussian_mixed_fourth N b e d)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (finiteRowGram_symm N e d))))
  have hfirst : a * finiteProductGaussian N (polyMul (polyMul D D) (polyMul E E)) ≈
      a*(c*f+2*(z*z)) :=
    Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_square_pair N d e)
  have hsecond : finiteProductGaussian N
      (polyMul B (finiteRowDerivative N b (polyMul (polyMul D D) (polyMul E E)))) ≈
      2*(x*(x*f+2*(y*z))) + 2*(y*(y*c+2*(x*z))) :=
    Q'.eqv_trans _ _ _ (square_product_derivative_contract N b d e B)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_mixed_fourth N b d e)))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hmixedReverse)))
  exact Q'.eqv_trans _ _ _ (row_pair_insert N b b (polyMul (polyMul D D) (polyMul E E)))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hfirst hsecond) (sixth_scalar a c f x y z))

private theorem covariance_scalar (a c f x y z : Q') :
    (a*c*f+2*(a*(z*z)+c*(y*y)+f*(x*x))+8*x*y*z) -
      (a*c+2*(x*x))*f ≈ 2*(a*(z*z)+c*(y*y))+8*x*y*z := by
  let A : PolyExpr := .var 0
  let C : PolyExpr := .var 1
  let F : PolyExpr := .var 2
  let X : PolyExpr := .var 3
  let Y : PolyExpr := .var 4
  let Z : PolyExpr := .var 5
  exact poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.mul A C) F)
      (.mul (.const 2) (.add (.add (.mul A (.mul Z Z)) (.mul C (.mul Y Y))) (.mul F (.mul X X)))))
      (.mul (.mul (.mul (.const 8) X) Y) Z))
      (.neg (.mul (.add (.mul A C) (.mul (.const 2) (.mul X X))) F)))
    (.add (.mul (.const 2) (.add (.mul A (.mul Z Z)) (.mul C (.mul Y Y))))
      (.mul (.mul (.mul (.const 8) X) Y) Z))
    (by decide) (fun | 0 => a | 1 => c | 2 => f | 3 => x | 4 => y | _ => z)

/-- Literal actual covariance Cov(B^2*D^2,E^2). Both actual Gaussian means
are retained on the left; this is the finite summand for the radial consumer. -/
theorem finiteProductGaussian_three_square_covariance (N : Nat) (b d e : Nat → Q') :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N b))
        (polyMul (polyMul (finiteLinearRow N d) (finiteLinearRow N d))
          (polyMul (finiteLinearRow N e) (finiteLinearRow N e)))) -
      finiteProductGaussian N
        (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N b))
          (polyMul (finiteLinearRow N d) (finiteLinearRow N d))) *
      finiteProductGaussian N (polyMul (finiteLinearRow N e) (finiteLinearRow N e)) ≈
      2 * (finiteRowNorm2 N b * (finiteRowGram N d e * finiteRowGram N d e) +
        finiteRowNorm2 N d * (finiteRowGram N b e * finiteRowGram N b e)) +
      8 * finiteRowGram N b d * finiteRowGram N b e * finiteRowGram N d e := by
  have hproduct := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (finiteProductGaussian_row_square_pair N b d))
    (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N e e))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (finiteProductGaussian_three_square_sixth N b d e)
      (Q'.neg_eqv_congr _ _ hproduct))
    (covariance_scalar (finiteRowNorm2 N b) (finiteRowNorm2 N d) (finiteRowNorm2 N e)
      (finiteRowGram N b d) (finiteRowGram N b e) (finiteRowGram N d e))

end YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment.finiteProductGaussian_mixed_fourth
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment.finiteProductGaussian_three_square_sixth
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment.finiteProductGaussian_three_square_covariance

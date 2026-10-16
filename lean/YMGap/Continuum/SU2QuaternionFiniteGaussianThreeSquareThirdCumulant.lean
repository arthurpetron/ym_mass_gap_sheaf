/-
# Third cumulant of three finite Gaussian row squares

The complete spatial heat-action quartic coefficient contains a quadratic
row insertion, `-H2/6`, in addition to its quartic pieces.  Against the two
quadratic bulk-source observables this produces a `2+2+2` third cumulant.

This leaf derives its exact connected value from the existing finite
three-square sixth moment.  Every disconnected norm term cancels, leaving
the single Gram triangle `8*G12*G13*G23`.  No Gaussian law, independence
axiom, sign estimate, ORIGINAL-law comparison or physical mass gap is used.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant

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
open YMGap.Continuum.SU2QuaternionFiniteGaussianSixthMoment
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem threeSquareCumulant_scalar
    (a c f x y z : Q') :
    ((((a*c*f +
              2*(a*(z*z)+c*(y*y)+f*(x*x)) + 8*x*y*z) +
            -((a*c+2*(x*x))*f)) +
          -((a*f+2*(y*y))*c)) +
        -((c*f+2*(z*z))*a)) +
      2*(a*(c*f)) ≈
        8*x*y*z := by
  let A : PolyExpr := .var 0
  let C : PolyExpr := .var 1
  let F : PolyExpr := .var 2
  let X : PolyExpr := .var 3
  let Y : PolyExpr := .var 4
  let Z : PolyExpr := .var 5
  exact poly_identity_of_normal_eq
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add (.mul (.mul A C) F)
                (.mul (.const 2)
                  (.add (.add (.mul A (.mul Z Z)) (.mul C (.mul Y Y)))
                    (.mul F (.mul X X)))))
              (.mul (.mul (.mul (.const 8) X) Y) Z))
            (.neg (.mul (.add (.mul A C)
              (.mul (.const 2) (.mul X X))) F)))
          (.neg (.mul (.add (.mul A F)
            (.mul (.const 2) (.mul Y Y))) C)))
        (.neg (.mul (.add (.mul C F)
          (.mul (.const 2) (.mul Z Z))) A)))
      (.mul (.const 2) (.mul A (.mul C F))))
    (.mul (.mul (.mul (.const 8) X) Y) Z)
    (by decide) (fun
      | 0 => a
      | 1 => c
      | 2 => f
      | 3 => x
      | 4 => y
      | _ => z)

/-- Exact connected third cumulant of three literal finite rational-row
squares.  All norm/disconnected terms cancel, including degenerate rows and
the zero-coordinate case. -/
theorem finiteGaussianThirdCumulant_three_row_squares
    (N : Nat) (b d e : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowSquare N b)
        (finiteGaussianRowSquare N d)
        (finiteGaussianRowSquare N e) ≈
      8 * finiteRowGram N b d * finiteRowGram N b e *
        finiteRowGram N d e := by
  let a := finiteRowNorm2 N b
  let c := finiteRowNorm2 N d
  let f := finiteRowNorm2 N e
  let x := finiteRowGram N b d
  let y := finiteRowGram N b e
  let z := finiteRowGram N d e
  let B2 := polyMul (finiteLinearRow N b) (finiteLinearRow N b)
  let D2 := polyMul (finiteLinearRow N d) (finiteLinearRow N d)
  let E2 := polyMul (finiteLinearRow N e) (finiteLinearRow N e)
  have h6 := finiteProductGaussian_three_square_sixth N b d e
  have h6assoc :
      finiteProductGaussian N (polyMul (polyMul B2 D2) E2) ≈
        finiteProductGaussian N (polyMul B2 (polyMul D2 E2)) :=
    finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.mul_assoc B2 D2 E2)
  have h6left := Q'.eqv_trans _ _ _ h6assoc h6
  have hbd := finiteProductGaussian_row_square_pair N b d
  have hbe := finiteProductGaussian_row_square_pair N b e
  have hde := finiteProductGaussian_row_square_pair N d e
  have hb := finiteProductGaussian_row_pair N b b
  have hd := finiteProductGaussian_row_pair N d d
  have he := finiteProductGaussian_row_pair N e e
  unfold finiteGaussianThirdCumulant finiteGaussianRowSquare
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' h6left
            (Q'.neg_eqv_congr _ _ (mul_congr hbd he)))
          (Q'.neg_eqv_congr _ _ (mul_congr hbe hd)))
        (Q'.neg_eqv_congr _ _ (mul_congr hde hb)))
      (Q'.mul_eqv_congr_left 2 _ _
        (mul_congr hb (mul_congr hd he))))
    (threeSquareCumulant_scalar a c f x y z)

end YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant.finiteGaussianThirdCumulant_three_row_squares

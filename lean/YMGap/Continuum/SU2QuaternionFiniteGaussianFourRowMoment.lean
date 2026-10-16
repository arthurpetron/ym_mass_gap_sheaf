/-
# Computed rational four-row Gaussian moment

This leaf derives the literal four-row Wick contraction from the EXISTING
finiteProductGaussian evaluator, finite linear rows, Stein identity, row
Leibniz rule and checked derivative contractions.  The theorem holds for
every finite N, including zero, and arbitrary rational rows, including
degenerate ones.  No Gaussian law, independence premise, Gram identity or
moment formula is assumed.

This is the missing algebraic primitive for averaging the quartic Cayley
coefficient H4 in Gram data before any denominator-relative comparison.  The
actual H4 assembly, compact-Haar/original-law comparison, uniform interacting
estimate and physical mass gap remain separate obligations.  Variables
outside N are evaluated at ONE by the existing finite evaluator; no
coefficient-preserving tail statement is made.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment

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

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

private theorem row_pair_insert (N : Nat) (u v : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N u) (finiteLinearRow N v)) p) ≈
      finiteRowGram N u v * finiteProductGaussian N p +
        finiteProductGaussian N
          (polyMul (finiteLinearRow N v) (finiteRowDerivative N u p)) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_assoc _ _ p))
    (Q'.eqv_trans _ _ _
      (finiteProductGaussian_linearRow_stein N u (polyMul (finiteLinearRow N v) p))
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (finiteRowDerivative_mul N u (finiteLinearRow N v) p))
        (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
          (Q'.add_eqv_congr'
            (finiteRowDerivative_mixed_contraction N u v p)
            (Q'.eqv_refl _)))))

private theorem derivative_pair_product (N : Nat)
    (u v w x : Nat → Q') :
    finiteProductGaussian N
      (polyMul (finiteLinearRow N v)
        (finiteRowDerivative N u
          (polyMul (finiteLinearRow N w) (finiteLinearRow N x)))) ≈
      finiteRowGram N u w * finiteRowGram N v x +
        finiteRowGram N u x * finiteRowGram N v w := by
  let V := finiteLinearRow N v
  let W := finiteLinearRow N w
  let X := finiteLinearRow N x
  let Cw := finiteRowDerivative N u W
  let Cx := finiteRowDerivative N u X
  have hleft : RatPolyCoeffEqv (polyMul V (polyMul Cw X))
      (polyMul Cw (polyMul V X)) :=
    swap_first_two V Cw X
  have hright : RatPolyCoeffEqv (polyMul V (polyMul W Cx))
      (polyMul Cx (polyMul V W)) :=
    RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm W Cx).mul_left V)
      (swap_first_two V Cx W)
  have hsplit := RatPolyCoeffEqv.trans
    ((finiteRowDerivative_mul N u W X).mul_left V)
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_add_right V (polyMul Cw X) (polyMul W Cx))
      (RatPolyCoeffEqv.add hleft hright))
  exact Q'.eqv_trans _ _ _ (finiteProductGaussian_coeffEqv N hsplit)
    (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (finiteRowDerivative_mixed_contraction N u w (polyMul V X))
          (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N v x)))
        (Q'.eqv_trans _ _ _
          (finiteRowDerivative_mixed_contraction N u x (polyMul V W))
          (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N v w)))))

/-- Actual four-row moment, expressed only through the computed finite Gram
sums of the same rows and evaluator. -/
theorem finiteProductGaussian_four_rows
    (N : Nat) (b d e f : Nat → Q') :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N d))
        (polyMul (finiteLinearRow N e) (finiteLinearRow N f))) ≈
      finiteRowGram N b d * finiteRowGram N e f +
        (finiteRowGram N b e * finiteRowGram N d f +
          finiteRowGram N b f * finiteRowGram N d e) := by
  exact Q'.eqv_trans _ _ _
    (row_pair_insert N b d
      (polyMul (finiteLinearRow N e) (finiteLinearRow N f)))
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (finiteProductGaussian_row_pair N e f))
      (derivative_pair_product N b d e f))

/-- Connected four-row product.  The disconnected `(b,d)(e,f)` pairing is
cancelled exactly before any estimate or division is introduced. -/
theorem finiteProductGaussian_four_rows_connected
    (N : Nat) (b d e f : Nat → Q') :
    finiteProductGaussian N
        (polyMul (polyMul (finiteLinearRow N b) (finiteLinearRow N d))
          (polyMul (finiteLinearRow N e) (finiteLinearRow N f))) -
      finiteProductGaussian N
          (polyMul (finiteLinearRow N b) (finiteLinearRow N d)) *
        finiteProductGaussian N
          (polyMul (finiteLinearRow N e) (finiteLinearRow N f)) ≈
      finiteRowGram N b e * finiteRowGram N d f +
        finiteRowGram N b f * finiteRowGram N d e := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finiteProductGaussian_four_rows N b d e f)
      (Q'.neg_eqv_congr _ _
        (mul_congr
          (finiteProductGaussian_row_pair N b d)
          (finiteProductGaussian_row_pair N e f))))
    (poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.var 1))
          (.add (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
        (.neg (.mul (.var 0) (.var 1))))
      (.add (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5)))
      (by decide) (fun
        | 0 => finiteRowGram N b d
        | 1 => finiteRowGram N e f
        | 2 => finiteRowGram N b e
        | 3 => finiteRowGram N d f
        | 4 => finiteRowGram N b f
        | _ => finiteRowGram N d e))

end YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment.finiteProductGaussian_four_rows
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment.finiteProductGaussian_four_rows_connected

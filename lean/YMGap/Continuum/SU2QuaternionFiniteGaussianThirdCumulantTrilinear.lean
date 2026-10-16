/-
# Trilinearity of the finite Gaussian third cumulant

This leaf proves the additive and finite-sum part of the exact term-list lift
needed by the normalized Cayley-quartic source response.  The cumulant is the
literal evaluator expression already pinned to the checked `2+2+4` row Wick
reduction; no abstract probability or assumed cumulant law is imported.

The result expands a cumulant of three finite polynomial sums into the finite
triple sum of the corresponding cumulants.  Scalar weights and the concrete
bulk-source/plaquette term lists are separate immediate consumers.  No sign,
uniform estimate, ORIGINAL-law comparison or mass-gap conclusion is asserted.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

local infix:50 " ≈ " => Q'.eqv

private def cumulantValue
    (triple leftRight insertionMean leftInsertion rightMean
      rightInsertion leftMean : Q') : Q' :=
  ((((triple + -(leftRight * insertionMean)) +
        -(leftInsertion * rightMean)) +
      -(rightInsertion * leftMean)) +
    2 * (leftMean * (rightMean * insertionMean)))

private def cumulantExpr
    (triple leftRight insertionMean leftInsertion rightMean
      rightInsertion leftMean : PolyExpr) : PolyExpr :=
  .add
    (.add
      (.add
        (.add triple (.neg (.mul leftRight insertionMean)))
        (.neg (.mul leftInsertion rightMean)))
      (.neg (.mul rightInsertion leftMean)))
    (.mul (.const 2) (.mul leftMean (.mul rightMean insertionMean)))

private theorem cumulantValue_congr
    {triple triple' leftRight leftRight' insertionMean insertionMean'
      leftInsertion leftInsertion' rightMean rightMean'
      rightInsertion rightInsertion' leftMean leftMean' : Q'}
    (htriple : triple ≈ triple')
    (hleftRight : leftRight ≈ leftRight')
    (hinsertionMean : insertionMean ≈ insertionMean')
    (hleftInsertion : leftInsertion ≈ leftInsertion')
    (hrightMean : rightMean ≈ rightMean')
    (hrightInsertion : rightInsertion ≈ rightInsertion')
    (hleftMean : leftMean ≈ leftMean') :
    cumulantValue triple leftRight insertionMean leftInsertion rightMean
        rightInsertion leftMean ≈
      cumulantValue triple' leftRight' insertionMean' leftInsertion'
        rightMean' rightInsertion' leftMean' := by
  unfold cumulantValue
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' htriple
          (Q'.neg_eqv_congr _ _
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _ hleftRight)
              (Q'.mul_eqv_congr_left _ _ _ hinsertionMean))))
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hleftInsertion)
            (Q'.mul_eqv_congr_left _ _ _ hrightMean))))
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hrightInsertion)
          (Q'.mul_eqv_congr_left _ _ _ hleftMean))))
    (Q'.mul_eqv_congr_left 2 _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hleftMean)
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hrightMean)
            (Q'.mul_eqv_congr_left _ _ _ hinsertionMean)))))

/-- The finite Gaussian third cumulant depends only on the coefficient classes
of its three polynomial arguments. -/
theorem finiteGaussianThirdCumulant_coeffEqv
    (N : Nat) {left left' right right' insertion insertion' : RatPoly}
    (hleft : RatPolyCoeffEqv left left')
    (hright : RatPolyCoeffEqv right right')
    (hinsertion : RatPolyCoeffEqv insertion insertion') :
    finiteGaussianThirdCumulant N left right insertion ≈
      finiteGaussianThirdCumulant N left' right' insertion' := by
  have hleftRight : RatPolyCoeffEqv
      (polyMul left right) (polyMul left' right') :=
    RatPolyCoeffEqv.mul hleft hright
  have hleftInsertion : RatPolyCoeffEqv
      (polyMul left insertion) (polyMul left' insertion') :=
    RatPolyCoeffEqv.mul hleft hinsertion
  have hrightInsertion : RatPolyCoeffEqv
      (polyMul right insertion) (polyMul right' insertion') :=
    RatPolyCoeffEqv.mul hright hinsertion
  have htriple : RatPolyCoeffEqv
      (polyMul (polyMul left right) insertion)
      (polyMul (polyMul left' right') insertion') :=
    RatPolyCoeffEqv.mul hleftRight hinsertion
  unfold finiteGaussianThirdCumulant
  exact cumulantValue_congr
    (finiteProductGaussian_coeffEqv N htriple)
    (finiteProductGaussian_coeffEqv N hleftRight)
    (finiteProductGaussian_coeffEqv N hinsertion)
    (finiteProductGaussian_coeffEqv N hleftInsertion)
    (finiteProductGaussian_coeffEqv N hright)
    (finiteProductGaussian_coeffEqv N hrightInsertion)
    (finiteProductGaussian_coeffEqv N hleft)

private theorem monoMul_right_nil : ∀ monomial : List Nat,
    monoMul monomial [] = monomial
  | [] => rfl
  | _ :: _ => by simp only [monoMul]

private theorem polyMul_one_right (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polynomial polyOne) polynomial := by
  intro weight
  induction polynomial with
  | nil => exact Q'.eqv_refl 0
  | cons term rest induction =>
      change
        (term.2 * 1) * weight (monoMul term.1 []) +
              ratWeightedSum weight (polyMul rest polyOne) ≈
          term.2 * weight term.1 + ratWeightedSum weight rest
      rw [monoMul_right_nil]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv term.2))
        induction

private theorem polyMul_one_left (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polyOne polynomial) polynomial :=
  RatPolyCoeffEqv.trans (RatPolyCoeffEqv.mul_comm polyOne polynomial)
    (polyMul_one_right polynomial)

/-- The finite product-Gaussian evaluator sends the constant polynomial one
to the scalar one. -/
theorem finiteProductGaussian_one (N : Nat) :
    finiteProductGaussian N polyOne ≈ 1 := by
  have gaussianMono_nil : finiteGaussianMono N [] = 1 := by
    induction N with
    | zero => rfl
    | succ N ih =>
        change gaussianMoment1 ([].getD N 0) * finiteGaussianMono N [] = 1
        rw [List.getD_nil, ih]
        rfl
  change 1 * finiteGaussianMono N [] + 0 ≈ 1
  rw [gaussianMono_nil]
  decide

/-- A constant first block has zero third cumulant. -/
theorem finiteGaussianThirdCumulant_one_left
    (N : Nat) (q r : RatPoly) :
    finiteGaussianThirdCumulant N polyOne q r ≈ 0 := by
  have hone := finiteProductGaussian_one N
  have hlq := finiteProductGaussian_coeffEqv N
    (polyMul_one_left q)
  have hlr := finiteProductGaussian_coeffEqv N
    (polyMul_one_left r)
  have hlqr := finiteProductGaussian_coeffEqv N
    ((polyMul_one_left q).mul_right r)
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈ 0
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr hlqr hlq (Q'.eqv_refl _) hlr
      (Q'.eqv_refl _) (Q'.eqv_refl _) hone)
    (poly_identity_of_normal_eq
      (cumulantExpr (.var 0) (.var 1) (.var 2) (.var 2)
        (.var 1) (.var 0) (.const 1))
      (.const 0) (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul q r)
        | 1 => finiteProductGaussian N q
        | _ => finiteProductGaussian N r))

/-- A constant second block has zero third cumulant. -/
theorem finiteGaussianThirdCumulant_one_middle
    (N : Nat) (p r : RatPoly) :
    finiteGaussianThirdCumulant N p polyOne r ≈ 0 := by
  have hone := finiteProductGaussian_one N
  have hpone := finiteProductGaussian_coeffEqv N
    (polyMul_one_right p)
  have honer := finiteProductGaussian_coeffEqv N
    (polyMul_one_left r)
  have hponer := finiteProductGaussian_coeffEqv N
    ((polyMul_one_right p).mul_right r)
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈ 0
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr hponer hpone (Q'.eqv_refl _)
      (Q'.eqv_refl _) hone honer (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (cumulantExpr (.var 0) (.var 1) (.var 2) (.var 0)
        (.const 1) (.var 2) (.var 1))
      (.const 0) (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul p r)
        | 1 => finiteProductGaussian N p
        | _ => finiteProductGaussian N r))

private theorem cumulantValue_add_left
    (triple₁ triple₂ leftRight₁ leftRight₂ insertionMean
      leftInsertion₁ leftInsertion₂ rightMean rightInsertion
      leftMean₁ leftMean₂ : Q') :
    cumulantValue (triple₁ + triple₂) (leftRight₁ + leftRight₂)
        insertionMean (leftInsertion₁ + leftInsertion₂) rightMean
        rightInsertion (leftMean₁ + leftMean₂) ≈
      cumulantValue triple₁ leftRight₁ insertionMean leftInsertion₁
          rightMean rightInsertion leftMean₁ +
        cumulantValue triple₂ leftRight₂ insertionMean leftInsertion₂
          rightMean rightInsertion leftMean₂ := by
  unfold cumulantValue
  exact poly_identity_of_normal_eq
    (cumulantExpr
      (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)) (.var 4)
      (.add (.var 5) (.var 6)) (.var 7) (.var 8)
      (.add (.var 9) (.var 10)))
    (.add
      (cumulantExpr (.var 0) (.var 2) (.var 4) (.var 5) (.var 7)
        (.var 8) (.var 9))
      (cumulantExpr (.var 1) (.var 3) (.var 4) (.var 6) (.var 7)
        (.var 8) (.var 10)))
    (by decide) (fun
      | 0 => triple₁
      | 1 => triple₂
      | 2 => leftRight₁
      | 3 => leftRight₂
      | 4 => insertionMean
      | 5 => leftInsertion₁
      | 6 => leftInsertion₂
      | 7 => rightMean
      | 8 => rightInsertion
      | 9 => leftMean₁
      | _ => leftMean₂)

private theorem cumulantValue_add_middle
    (triple₁ triple₂ leftRight₁ leftRight₂ insertionMean leftInsertion
      rightMean₁ rightMean₂ rightInsertion₁ rightInsertion₂ leftMean : Q') :
    cumulantValue (triple₁ + triple₂) (leftRight₁ + leftRight₂)
        insertionMean leftInsertion (rightMean₁ + rightMean₂)
        (rightInsertion₁ + rightInsertion₂) leftMean ≈
      cumulantValue triple₁ leftRight₁ insertionMean leftInsertion
          rightMean₁ rightInsertion₁ leftMean +
        cumulantValue triple₂ leftRight₂ insertionMean leftInsertion
          rightMean₂ rightInsertion₂ leftMean := by
  unfold cumulantValue
  exact poly_identity_of_normal_eq
    (cumulantExpr
      (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)) (.var 4)
      (.var 5) (.add (.var 6) (.var 7))
      (.add (.var 8) (.var 9)) (.var 10))
    (.add
      (cumulantExpr (.var 0) (.var 2) (.var 4) (.var 5) (.var 6)
        (.var 8) (.var 10))
      (cumulantExpr (.var 1) (.var 3) (.var 4) (.var 5) (.var 7)
        (.var 9) (.var 10)))
    (by decide) (fun
      | 0 => triple₁
      | 1 => triple₂
      | 2 => leftRight₁
      | 3 => leftRight₂
      | 4 => insertionMean
      | 5 => leftInsertion
      | 6 => rightMean₁
      | 7 => rightMean₂
      | 8 => rightInsertion₁
      | 9 => rightInsertion₂
      | _ => leftMean)

private theorem cumulantValue_add_right
    (triple₁ triple₂ leftRight insertionMean₁ insertionMean₂
      leftInsertion₁ leftInsertion₂ rightMean
      rightInsertion₁ rightInsertion₂ leftMean : Q') :
    cumulantValue (triple₁ + triple₂) leftRight
        (insertionMean₁ + insertionMean₂)
        (leftInsertion₁ + leftInsertion₂) rightMean
        (rightInsertion₁ + rightInsertion₂) leftMean ≈
      cumulantValue triple₁ leftRight insertionMean₁ leftInsertion₁
          rightMean rightInsertion₁ leftMean +
        cumulantValue triple₂ leftRight insertionMean₂ leftInsertion₂
          rightMean rightInsertion₂ leftMean := by
  unfold cumulantValue
  exact poly_identity_of_normal_eq
    (cumulantExpr
      (.add (.var 0) (.var 1)) (.var 2) (.add (.var 3) (.var 4))
      (.add (.var 5) (.var 6)) (.var 7)
      (.add (.var 8) (.var 9)) (.var 10))
    (.add
      (cumulantExpr (.var 0) (.var 2) (.var 3) (.var 5) (.var 7)
        (.var 8) (.var 10))
      (cumulantExpr (.var 1) (.var 2) (.var 4) (.var 6) (.var 7)
        (.var 9) (.var 10)))
    (by decide) (fun
      | 0 => triple₁
      | 1 => triple₂
      | 2 => leftRight
      | 3 => insertionMean₁
      | 4 => insertionMean₂
      | 5 => leftInsertion₁
      | 6 => leftInsertion₂
      | 7 => rightMean
      | 8 => rightInsertion₁
      | 9 => rightInsertion₂
      | _ => leftMean)

private theorem cumulantValue_smul_left
    (weight triple leftRight insertionMean leftInsertion rightMean
      rightInsertion leftMean : Q') :
    cumulantValue (weight * triple) (weight * leftRight) insertionMean
        (weight * leftInsertion) rightMean rightInsertion
        (weight * leftMean) ≈
      weight * cumulantValue triple leftRight insertionMean leftInsertion
        rightMean rightInsertion leftMean := by
  unfold cumulantValue
  exact poly_identity_of_normal_eq
    (cumulantExpr
      (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)) (.var 3)
      (.mul (.var 0) (.var 4)) (.var 5) (.var 6)
      (.mul (.var 0) (.var 7)))
    (.mul (.var 0)
      (cumulantExpr (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
        (.var 6) (.var 7)))
    (by decide) (fun
      | 0 => weight
      | 1 => triple
      | 2 => leftRight
      | 3 => insertionMean
      | 4 => leftInsertion
      | 5 => rightMean
      | 6 => rightInsertion
      | _ => leftMean)

private theorem cumulantValue_smul_middle
    (weight triple leftRight insertionMean leftInsertion rightMean
      rightInsertion leftMean : Q') :
    cumulantValue (weight * triple) (weight * leftRight) insertionMean
        leftInsertion (weight * rightMean) (weight * rightInsertion)
        leftMean ≈
      weight * cumulantValue triple leftRight insertionMean leftInsertion
        rightMean rightInsertion leftMean := by
  unfold cumulantValue
  exact poly_identity_of_normal_eq
    (cumulantExpr
      (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)) (.var 3)
      (.var 4) (.mul (.var 0) (.var 5))
      (.mul (.var 0) (.var 6)) (.var 7))
    (.mul (.var 0)
      (cumulantExpr (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
        (.var 6) (.var 7)))
    (by decide) (fun
      | 0 => weight
      | 1 => triple
      | 2 => leftRight
      | 3 => insertionMean
      | 4 => leftInsertion
      | 5 => rightMean
      | 6 => rightInsertion
      | _ => leftMean)

private theorem cumulantValue_smul_right
    (weight triple leftRight insertionMean leftInsertion rightMean
      rightInsertion leftMean : Q') :
    cumulantValue (weight * triple) leftRight (weight * insertionMean)
        (weight * leftInsertion) rightMean (weight * rightInsertion)
        leftMean ≈
      weight * cumulantValue triple leftRight insertionMean leftInsertion
        rightMean rightInsertion leftMean := by
  unfold cumulantValue
  exact poly_identity_of_normal_eq
    (cumulantExpr
      (.mul (.var 0) (.var 1)) (.var 2) (.mul (.var 0) (.var 3))
      (.mul (.var 0) (.var 4)) (.var 5)
      (.mul (.var 0) (.var 6)) (.var 7))
    (.mul (.var 0)
      (cumulantExpr (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
        (.var 6) (.var 7)))
    (by decide) (fun
      | 0 => weight
      | 1 => triple
      | 2 => leftRight
      | 3 => insertionMean
      | 4 => leftInsertion
      | 5 => rightMean
      | 6 => rightInsertion
      | _ => leftMean)

private theorem gaussian_zero (N : Nat) :
    finiteProductGaussian N polyZero ≈ 0 := by
  rw [finiteProductGaussian_probe]
  exact Q'.eqv_refl _

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe,
    finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_smul (N : Nat) (weight : Q') (p : RatPoly) :
    finiteProductGaussian N (polySmul weight p) ≈
      weight * finiteProductGaussian N p := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) weight p

private theorem gaussian_mul_add_left (N : Nat) (p q r : RatPoly) :
    finiteProductGaussian N (polyMul (polyAdd p q) r) ≈
      finiteProductGaussian N (polyMul p r) +
        finiteProductGaussian N (polyMul q r) := by
  rw [polyMul_add_left_exact]
  exact gaussian_add N _ _

private theorem gaussian_mul_add_right (N : Nat) (p q r : RatPoly) :
    finiteProductGaussian N (polyMul p (polyAdd q r)) ≈
      finiteProductGaussian N (polyMul p q) +
        finiteProductGaussian N (polyMul p r) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.mul_add_right p q r))
    (gaussian_add N _ _)

private theorem gaussian_triple_add_left (N : Nat)
    (p q r s : RatPoly) :
    finiteProductGaussian N
        (polyMul (polyMul (polyAdd p q) r) s) ≈
      finiteProductGaussian N (polyMul (polyMul p r) s) +
        finiteProductGaussian N (polyMul (polyMul q r) s) := by
  rw [polyMul_add_left_exact p q r,
    polyMul_add_left_exact (polyMul p r) (polyMul q r) s]
  exact gaussian_add N _ _

private theorem gaussian_triple_add_middle (N : Nat)
    (p q r s : RatPoly) :
    finiteProductGaussian N
        (polyMul (polyMul p (polyAdd q r)) s) ≈
      finiteProductGaussian N (polyMul (polyMul p q) s) +
        finiteProductGaussian N (polyMul (polyMul p r) s) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      ((RatPolyCoeffEqv.mul_add_right p q r).mul_right s))
    (gaussian_mul_add_left N (polyMul p q) (polyMul p r) s)

private theorem gaussian_triple_add_right (N : Nat)
    (p q r s : RatPoly) :
    finiteProductGaussian N
        (polyMul (polyMul p q) (polyAdd r s)) ≈
      finiteProductGaussian N (polyMul (polyMul p q) r) +
        finiteProductGaussian N (polyMul (polyMul p q) s) :=
  gaussian_mul_add_right N (polyMul p q) r s

private theorem gaussian_mul_smul_left (N : Nat)
    (weight : Q') (p q : RatPoly) :
    finiteProductGaussian N (polyMul (polySmul weight p) q) ≈
      weight * finiteProductGaussian N (polyMul p q) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.polyMul_smul_left weight p q))
    (gaussian_smul N weight (polyMul p q))

private theorem gaussian_mul_smul_right (N : Nat)
    (weight : Q') (p q : RatPoly) :
    finiteProductGaussian N (polyMul p (polySmul weight q)) ≈
      weight * finiteProductGaussian N (polyMul p q) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.polyMul_smul_right weight p q))
    (gaussian_smul N weight (polyMul p q))

private theorem gaussian_triple_smul_left (N : Nat)
    (weight : Q') (p q r : RatPoly) :
    finiteProductGaussian N
        (polyMul (polyMul (polySmul weight p) q) r) ≈
      weight * finiteProductGaussian N (polyMul (polyMul p q) r) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.trans
        ((RatPolyCoeffEqv.polyMul_smul_left weight p q).mul_right r)
        (RatPolyCoeffEqv.polyMul_smul_left weight (polyMul p q) r)))
    (gaussian_smul N weight (polyMul (polyMul p q) r))

private theorem gaussian_triple_smul_middle (N : Nat)
    (weight : Q') (p q r : RatPoly) :
    finiteProductGaussian N
        (polyMul (polyMul p (polySmul weight q)) r) ≈
      weight * finiteProductGaussian N (polyMul (polyMul p q) r) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.trans
        ((RatPolyCoeffEqv.polyMul_smul_right weight p q).mul_right r)
        (RatPolyCoeffEqv.polyMul_smul_left weight (polyMul p q) r)))
    (gaussian_smul N weight (polyMul (polyMul p q) r))

private theorem gaussian_triple_smul_right (N : Nat)
    (weight : Q') (p q r : RatPoly) :
    finiteProductGaussian N
        (polyMul (polyMul p q) (polySmul weight r)) ≈
      weight * finiteProductGaussian N (polyMul (polyMul p q) r) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.polyMul_smul_right weight (polyMul p q) r))
    (gaussian_smul N weight (polyMul (polyMul p q) r))

/-- Additivity in the first polynomial block. -/
theorem finiteGaussianThirdCumulant_add_left
    (N : Nat) (p q r s : RatPoly) :
    finiteGaussianThirdCumulant N (polyAdd p q) r s ≈
      finiteGaussianThirdCumulant N p r s +
        finiteGaussianThirdCumulant N q r s := by
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈
    cumulantValue _ _ _ _ _ _ _ + cumulantValue _ _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr
      (gaussian_triple_add_left N p q r s)
      (gaussian_mul_add_left N p q r)
      (Q'.eqv_refl _)
      (gaussian_mul_add_left N p q s)
      (Q'.eqv_refl _)
      (Q'.eqv_refl _)
      (gaussian_add N p q))
    (cumulantValue_add_left _ _ _ _ _ _ _ _ _ _ _)

/-- Additivity in the second polynomial block. -/
theorem finiteGaussianThirdCumulant_add_middle
    (N : Nat) (p q r s : RatPoly) :
    finiteGaussianThirdCumulant N p (polyAdd q r) s ≈
      finiteGaussianThirdCumulant N p q s +
        finiteGaussianThirdCumulant N p r s := by
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈
    cumulantValue _ _ _ _ _ _ _ + cumulantValue _ _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr
      (gaussian_triple_add_middle N p q r s)
      (gaussian_mul_add_right N p q r)
      (Q'.eqv_refl _)
      (Q'.eqv_refl _)
      (gaussian_add N q r)
      (gaussian_mul_add_left N q r s)
      (Q'.eqv_refl _))
    (cumulantValue_add_middle _ _ _ _ _ _ _ _ _ _ _)

/-- Additivity in the inserted polynomial block. -/
theorem finiteGaussianThirdCumulant_add_right
    (N : Nat) (p q r s : RatPoly) :
    finiteGaussianThirdCumulant N p q (polyAdd r s) ≈
      finiteGaussianThirdCumulant N p q r +
        finiteGaussianThirdCumulant N p q s := by
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈
    cumulantValue _ _ _ _ _ _ _ + cumulantValue _ _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr
      (gaussian_triple_add_right N p q r s)
      (Q'.eqv_refl _)
      (gaussian_add N r s)
      (gaussian_mul_add_right N p r s)
      (Q'.eqv_refl _)
      (gaussian_mul_add_right N q r s)
      (Q'.eqv_refl _))
    (cumulantValue_add_right _ _ _ _ _ _ _ _ _ _ _)

/-- Rational homogeneity in the first polynomial block. -/
theorem finiteGaussianThirdCumulant_smul_left
    (N : Nat) (weight : Q') (p q r : RatPoly) :
    finiteGaussianThirdCumulant N (polySmul weight p) q r ≈
      weight * finiteGaussianThirdCumulant N p q r := by
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈
    weight * cumulantValue _ _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr
      (gaussian_triple_smul_left N weight p q r)
      (gaussian_mul_smul_left N weight p q)
      (Q'.eqv_refl _)
      (gaussian_mul_smul_left N weight p r)
      (Q'.eqv_refl _)
      (Q'.eqv_refl _)
      (gaussian_smul N weight p))
    (cumulantValue_smul_left _ _ _ _ _ _ _ _)

/-- Rational homogeneity in the second polynomial block. -/
theorem finiteGaussianThirdCumulant_smul_middle
    (N : Nat) (weight : Q') (p q r : RatPoly) :
    finiteGaussianThirdCumulant N p (polySmul weight q) r ≈
      weight * finiteGaussianThirdCumulant N p q r := by
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈
    weight * cumulantValue _ _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr
      (gaussian_triple_smul_middle N weight p q r)
      (gaussian_mul_smul_right N weight p q)
      (Q'.eqv_refl _)
      (Q'.eqv_refl _)
      (gaussian_smul N weight q)
      (gaussian_mul_smul_left N weight q r)
      (Q'.eqv_refl _))
    (cumulantValue_smul_middle _ _ _ _ _ _ _ _)

/-- Rational homogeneity in the inserted polynomial block. -/
theorem finiteGaussianThirdCumulant_smul_right
    (N : Nat) (weight : Q') (p q r : RatPoly) :
    finiteGaussianThirdCumulant N p q (polySmul weight r) ≈
      weight * finiteGaussianThirdCumulant N p q r := by
  unfold finiteGaussianThirdCumulant
  change cumulantValue _ _ _ _ _ _ _ ≈
    weight * cumulantValue _ _ _ _ _ _ _
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr
      (gaussian_triple_smul_right N weight p q r)
      (Q'.eqv_refl _)
      (gaussian_smul N weight r)
      (gaussian_mul_smul_right N weight p r)
      (Q'.eqv_refl _)
      (gaussian_mul_smul_right N weight q r)
      (Q'.eqv_refl _))
    (cumulantValue_smul_right _ _ _ _ _ _ _ _)

/-- Polynomial centering by an arbitrary supplied scalar. -/
def finiteGaussianCenteredPolynomial (center : Q') (polynomial : RatPoly) :
    RatPoly :=
  polyAdd polynomial (polySmul (-center) polyOne)

/-- Centering the first source block by any scalar leaves the third cumulant
unchanged. -/
theorem finiteGaussianThirdCumulant_center_left
    (N : Nat) (center : Q') (p q r : RatPoly) :
    finiteGaussianThirdCumulant N
        (finiteGaussianCenteredPolynomial center p) q r ≈
      finiteGaussianThirdCumulant N p q r := by
  unfold finiteGaussianCenteredPolynomial
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_add_left N p
      (polySmul (-center) polyOne) q r)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (finiteGaussianThirdCumulant_smul_left N (-center) polyOne q r)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (-center) _ _
              (finiteGaussianThirdCumulant_one_left N q r))
            (Q'.mul_zero_eqv (-center)))))
      (QPoly.q_add_zero_eqv _))

/-- Centering the second source block by any scalar leaves the third cumulant
unchanged. -/
theorem finiteGaussianThirdCumulant_center_middle
    (N : Nat) (center : Q') (p q r : RatPoly) :
    finiteGaussianThirdCumulant N p
        (finiteGaussianCenteredPolynomial center q) r ≈
      finiteGaussianThirdCumulant N p q r := by
  unfold finiteGaussianCenteredPolynomial
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_add_middle N p q
      (polySmul (-center) polyOne) r)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (finiteGaussianThirdCumulant_smul_middle N (-center) p polyOne r)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (-center) _ _
              (finiteGaussianThirdCumulant_one_middle N p r))
            (Q'.mul_zero_eqv (-center)))))
      (QPoly.q_add_zero_eqv _))

/-- Simultaneously replacing both source blocks by arbitrary scalar-centered
versions leaves the inserted third cumulant unchanged. -/
theorem finiteGaussianThirdCumulant_center_left_middle
    (N : Nat) (leftCenter rightCenter : Q') (p q r : RatPoly) :
    finiteGaussianThirdCumulant N
        (finiteGaussianCenteredPolynomial leftCenter p)
        (finiteGaussianCenteredPolynomial rightCenter q) r ≈
      finiteGaussianThirdCumulant N p q r :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_center_left N leftCenter p
      (finiteGaussianCenteredPolynomial rightCenter q) r)
    (finiteGaussianThirdCumulant_center_middle N rightCenter p q r)

private theorem finiteGaussianThirdCumulant_zero_left
    (N : Nat) (q r : RatPoly) :
    finiteGaussianThirdCumulant N polyZero q r ≈ 0 := by
  unfold finiteGaussianThirdCumulant
  have hleft := gaussian_zero N
  have hlq := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_left q)) hleft
  have hlr := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_left r)) hleft
  have hlqr := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      ((RatPolyCoeffEqv.mul_zero_left q).mul_right r |>.trans
        (RatPolyCoeffEqv.mul_zero_left r))) hleft
  change cumulantValue _ _ _ _ _ _ _ ≈ 0
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr hlqr hlq (Q'.eqv_refl _) hlr
      (Q'.eqv_refl _) (Q'.eqv_refl _) hleft)
    (poly_identity_of_normal_eq
      (cumulantExpr (.const 0) (.const 0) (.var 0) (.const 0)
        (.var 1) (.var 2) (.const 0))
      (.const 0) (by decide) (fun
        | 0 => finiteProductGaussian N r
        | 1 => finiteProductGaussian N q
        | _ => finiteProductGaussian N (polyMul q r)))

private theorem finiteGaussianThirdCumulant_zero_middle
    (N : Nat) (p r : RatPoly) :
    finiteGaussianThirdCumulant N p polyZero r ≈ 0 := by
  unfold finiteGaussianThirdCumulant
  have hzero := gaussian_zero N
  have hpz := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_right p)) hzero
  have hzr := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_left r)) hzero
  have hpzr := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      ((RatPolyCoeffEqv.mul_zero_right p).mul_right r |>.trans
        (RatPolyCoeffEqv.mul_zero_left r))) hzero
  change cumulantValue _ _ _ _ _ _ _ ≈ 0
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr hpzr hpz (Q'.eqv_refl _)
      (Q'.eqv_refl _) hzero hzr (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (cumulantExpr (.const 0) (.const 0) (.var 0) (.var 1)
        (.const 0) (.const 0) (.var 2))
      (.const 0) (by decide) (fun
        | 0 => finiteProductGaussian N r
        | 1 => finiteProductGaussian N (polyMul p r)
        | _ => finiteProductGaussian N p))

private theorem finiteGaussianThirdCumulant_zero_right
    (N : Nat) (p q : RatPoly) :
    finiteGaussianThirdCumulant N p q polyZero ≈ 0 := by
  unfold finiteGaussianThirdCumulant
  have hzero := gaussian_zero N
  have hpz := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_right p)) hzero
  have hqz := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.mul_zero_right q)) hzero
  have hpqz := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.mul_zero_right (polyMul p q))) hzero
  change cumulantValue _ _ _ _ _ _ _ ≈ 0
  exact Q'.eqv_trans _ _ _
    (cumulantValue_congr hpqz (Q'.eqv_refl _) hzero hpz
      (Q'.eqv_refl _) hqz (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (cumulantExpr (.const 0) (.var 0) (.const 0) (.const 0)
        (.var 1) (.const 0) (.var 2))
      (.const 0) (by decide) (fun
        | 0 => finiteProductGaussian N (polyMul p q)
        | 1 => finiteProductGaussian N q
        | _ => finiteProductGaussian N p))

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≈ g item) →
    qListSum (items.map f) ≈ qListSum (items.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

theorem finiteGaussianThirdCumulant_polySum_left
    (N : Nat) (q r : RatPoly) : ∀ polynomials : List RatPoly,
    finiteGaussianThirdCumulant N (polySum polynomials) q r ≈
      qListSum (polynomials.map fun p =>
        finiteGaussianThirdCumulant N p q r)
  | [] => finiteGaussianThirdCumulant_zero_left N q r
  | p :: polynomials =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_add_left N p
          (polySum polynomials) q r)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (finiteGaussianThirdCumulant_polySum_left N q r polynomials))

theorem finiteGaussianThirdCumulant_polySum_middle
    (N : Nat) (p r : RatPoly) : ∀ polynomials : List RatPoly,
    finiteGaussianThirdCumulant N p (polySum polynomials) r ≈
      qListSum (polynomials.map fun q =>
        finiteGaussianThirdCumulant N p q r)
  | [] => finiteGaussianThirdCumulant_zero_middle N p r
  | q :: polynomials =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_add_middle N p q
          (polySum polynomials) r)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (finiteGaussianThirdCumulant_polySum_middle N p r polynomials))

theorem finiteGaussianThirdCumulant_polySum_right
    (N : Nat) (p q : RatPoly) : ∀ polynomials : List RatPoly,
    finiteGaussianThirdCumulant N p q (polySum polynomials) ≈
      qListSum (polynomials.map fun r =>
        finiteGaussianThirdCumulant N p q r)
  | [] => finiteGaussianThirdCumulant_zero_right N p q
  | r :: polynomials =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_add_right N p q r
          (polySum polynomials))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (finiteGaussianThirdCumulant_polySum_right N p q polynomials))

/-- Exact finite triple-sum expansion of the third cumulant. -/
theorem finiteGaussianThirdCumulant_polySum_three
    (N : Nat) (left right insertions : List RatPoly) :
    finiteGaussianThirdCumulant N
        (polySum left) (polySum right) (polySum insertions) ≈
      qListSum (left.map fun p =>
        qListSum (right.map fun q =>
          qListSum (insertions.map fun r =>
            finiteGaussianThirdCumulant N p q r))) := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_polySum_left N
      (polySum right) (polySum insertions) left)
    (qListSum_congr _ _ left (fun p _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_polySum_middle N p
          (polySum insertions) right)
        (qListSum_congr _ _ right (fun q _ =>
          finiteGaussianThirdCumulant_polySum_right N p q insertions))))

/-- Exact weighted finite triple-sum expansion.  Each rational coefficient is
kept outside its row polynomial, matching the existing bulk-source encoding. -/
theorem finiteGaussianThirdCumulant_weighted_polySum_three
    (N : Nat)
    (left right insertions : List (Q' × RatPoly)) :
    finiteGaussianThirdCumulant N
        (polySum (left.map fun term => polySmul term.1 term.2))
        (polySum (right.map fun term => polySmul term.1 term.2))
        (polySum (insertions.map fun term => polySmul term.1 term.2)) ≈
      qListSum (left.map fun leftTerm =>
        qListSum (right.map fun rightTerm =>
          qListSum (insertions.map fun insertionTerm =>
            leftTerm.1 * (rightTerm.1 *
              (insertionTerm.1 * finiteGaussianThirdCumulant N
                leftTerm.2 rightTerm.2 insertionTerm.2))))) := by
  have hsum := finiteGaussianThirdCumulant_polySum_three N
    (left.map fun term => polySmul term.1 term.2)
    (right.map fun term => polySmul term.1 term.2)
    (insertions.map fun term => polySmul term.1 term.2)
  exact Q'.eqv_trans _ _ _ hsum (by
    simp only [List.map_map]
    exact qListSum_congr _ _ left (fun leftTerm _ =>
      qListSum_congr _ _ right (fun rightTerm _ =>
        qListSum_congr _ _ insertions (fun insertionTerm _ =>
          Q'.eqv_trans _ _ _
            (finiteGaussianThirdCumulant_smul_left N leftTerm.1
              leftTerm.2 (polySmul rightTerm.1 rightTerm.2)
              (polySmul insertionTerm.1 insertionTerm.2))
            (Q'.mul_eqv_congr_left leftTerm.1 _ _
              (Q'.eqv_trans _ _ _
                (finiteGaussianThirdCumulant_smul_middle N rightTerm.1
                  leftTerm.2 rightTerm.2
                  (polySmul insertionTerm.1 insertionTerm.2))
                (Q'.mul_eqv_congr_left rightTerm.1 _ _
                  (finiteGaussianThirdCumulant_smul_right N insertionTerm.1
                    leftTerm.2 rightTerm.2 insertionTerm.2))))))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_center_left_middle
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_add_left
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_add_middle
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_add_right
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_smul_left
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_smul_middle
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_smul_right
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_polySum_three
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear.finiteGaussianThirdCumulant_weighted_polySum_three

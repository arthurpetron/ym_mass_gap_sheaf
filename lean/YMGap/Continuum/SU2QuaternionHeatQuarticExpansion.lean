/-
# Exact quartic character expansion of every finite heat-prefix term

The square of `2 - chi_1` sends each SU(2) character to a finite signed
five-diagonal character combination, with separate spin-zero and spin-one
formulas. Distributing these exact identities over the ORIGINAL heat prefix
retains every finite-cutoff boundary term, including K=0 and K=1. This file
does not regroup equal output spins, estimate their coefficients, or assume
positivity of the signed expansion.
-/

import YMGap.Continuum.SU2QuaternionHeatFusionResidual

namespace YMGap.Continuum.SU2QuaternionHeatQuarticExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

/-- The physical fundamental trace deficit. -/
def defect (x : RatPoly) : RatPoly :=
  polyAdd (cap 2) (polyNeg (characterPolynomial x 1))

private def scale (c : Q') (p : RatPoly) : RatPoly := polyMul (cap c) p

/-- The exact, unregrouped output for each basis spin. `j=k+2` covers all
bulk spins without truncated natural-number subtraction. -/
def quarticBasis (x : RatPoly) : Nat → RatPoly
  | 0 => polyAdd
      (polyAdd (scale 5 (characterPolynomial x 0))
        (polyNeg (scale 4 (characterPolynomial x 1))))
      (characterPolynomial x 2)
  | 1 => polyAdd
      (polyAdd (scale 6 (characterPolynomial x 1))
        (polyNeg (scale 4 (polyAdd (characterPolynomial x 0) (characterPolynomial x 2)))))
      (characterPolynomial x 3)
  | k + 2 => polyAdd
      (polyAdd (scale 6 (characterPolynomial x (k+2)))
        (polyNeg (scale 4 (polyAdd (characterPolynomial x (k+1))
          (characterPolynomial x (k+3))))))
      (polyAdd (characterPolynomial x k) (characterPolynomial x (k+4)))

private theorem first_mul_succ (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv
      (polyMul (characterPolynomial x 1) (characterPolynomial x (n+1)))
      (polyAdd (characterPolynomial x (n+2)) (characterPolynomial x n)) := by
  let a := polyMul (characterPolynomial x 1) (characterPolynomial x (n+1))
  let b := characterPolynomial x n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (.refl b))

private theorem defect_square_decomp (x p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (defect x) (defect x)) p)
      (polyAdd
        (polyAdd
          (polyMul (polyMul (characterPolynomial x 1) (characterPolynomial x 1)) p)
          (polyNeg (scale 4 (polyMul (characterPolynomial x 1) p))))
        (scale 4 p)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.add (.const 2) (.neg (.var 0)))
      (.add (.const 2) (.neg (.var 0)))) (.var 1))
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.neg (.mul (.const 4) (.mul (.var 0) (.var 1)))))
      (.mul (.const 4) (.var 1)))
    (by decide) (fun | 0 => characterPolynomial x 1 | _ => p)

private theorem square_mul_zero (x : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (characterPolynomial x 1) (characterPolynomial x 1))
        (characterPolynomial x 0))
      (polyAdd (characterPolynomial x 2) (characterPolynomial x 0)) :=
  (RatPolyCoeffEqv.mul_one _).trans (first_mul_succ x 0)

private theorem square_mul_one (x : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (characterPolynomial x 1) (characterPolynomial x 1))
        (characterPolynomial x 1))
      (polyAdd (polyAdd (characterPolynomial x 3) (characterPolynomial x 1))
        (characterPolynomial x 1)) :=
  (RatPolyCoeffEqv.mul_assoc _ _ _).trans
    (((first_mul_succ x 0).mul_left (characterPolynomial x 1)).trans
      ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
        ((first_mul_succ x 1).add (RatPolyCoeffEqv.mul_one _))))

private theorem square_mul_bulk (x : RatPoly) (k : Nat) :
    RatPolyCoeffEqv
      (polyMul (polyMul (characterPolynomial x 1) (characterPolynomial x 1))
        (characterPolynomial x (k+2)))
      (polyAdd
        (polyAdd (characterPolynomial x (k+4)) (characterPolynomial x (k+2)))
        (polyAdd (characterPolynomial x (k+2)) (characterPolynomial x k))) :=
  (RatPolyCoeffEqv.mul_assoc _ _ _).trans
    (((first_mul_succ x (k+1)).mul_left (characterPolynomial x 1)).trans
      ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
        ((first_mul_succ x (k+2)).add (first_mul_succ x k))))

private theorem assemble (x p first square result : RatPoly)
    (hfirst : RatPolyCoeffEqv (polyMul (characterPolynomial x 1) p) first)
    (hsquare : RatPolyCoeffEqv
      (polyMul (polyMul (characterPolynomial x 1) (characterPolynomial x 1)) p) square)
    (hrecombine : RatPolyCoeffEqv
      (polyAdd (polyAdd square (polyNeg (scale 4 first))) (scale 4 p)) result) :
    RatPolyCoeffEqv (polyMul (polyMul (defect x) (defect x)) p) result :=
  (defect_square_decomp x p).trans
    ((((hsquare.add (RatPolyCoeffEqv.neg (hfirst.mul_left (cap 4)))).add
      (RatPolyCoeffEqv.refl _))).trans hrecombine)

/-- Every spin is expanded exactly, with no heat-coefficient hypothesis. -/
theorem defect_square_basis (x : RatPoly) : ∀ j : Nat,
    RatPolyCoeffEqv
      (polyMul (polyMul (defect x) (defect x)) (characterPolynomial x j))
      (quarticBasis x j)
  | 0 => by
      apply assemble x (characterPolynomial x 0) (characterPolynomial x 1)
        (polyAdd (characterPolynomial x 2) (characterPolynomial x 0))
      · exact RatPolyCoeffEqv.mul_one _
      · exact square_mul_zero x
      · exact coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.add (.var 2) (.var 0))
            (.neg (.mul (.const 4) (.var 1)))) (.mul (.const 4) (.var 0)))
          (.add (.add (.mul (.const 5) (.var 0))
            (.neg (.mul (.const 4) (.var 1)))) (.var 2))
          (by decide) (fun i =>
            if i = 0 then characterPolynomial x 0
            else if i = 1 then characterPolynomial x 1
            else characterPolynomial x 2)
  | 1 => by
      apply assemble x (characterPolynomial x 1)
        (polyAdd (characterPolynomial x 2) (characterPolynomial x 0))
        (polyAdd (polyAdd (characterPolynomial x 3) (characterPolynomial x 1))
          (characterPolynomial x 1))
      · exact first_mul_succ x 0
      · exact square_mul_one x
      · exact coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.add (.add (.var 3) (.var 1)) (.var 1))
            (.neg (.mul (.const 4) (.add (.var 2) (.var 0)))))
            (.mul (.const 4) (.var 1)))
          (.add (.add (.mul (.const 6) (.var 1))
            (.neg (.mul (.const 4) (.add (.var 0) (.var 2))))) (.var 3))
          (by decide) (fun i =>
            if i = 0 then characterPolynomial x 0
            else if i = 1 then characterPolynomial x 1
            else if i = 2 then characterPolynomial x 2
            else characterPolynomial x 3)
  | k + 2 => by
      apply assemble x (characterPolynomial x (k+2))
        (polyAdd (characterPolynomial x (k+3)) (characterPolynomial x (k+1)))
        (polyAdd
          (polyAdd (characterPolynomial x (k+4)) (characterPolynomial x (k+2)))
          (polyAdd (characterPolynomial x (k+2)) (characterPolynomial x k)))
      · exact first_mul_succ x (k+1)
      · exact square_mul_bulk x k
      · exact coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.add (.add (.var 4) (.var 2))
            (.add (.var 2) (.var 0)))
            (.neg (.mul (.const 4) (.add (.var 3) (.var 1)))))
            (.mul (.const 4) (.var 2)))
          (.add (.add (.mul (.const 6) (.var 2))
            (.neg (.mul (.const 4) (.add (.var 1) (.var 3)))))
            (.add (.var 0) (.var 4)))
          (by decide) (fun i =>
            if i = 0 then characterPolynomial x k
            else if i = 1 then characterPolynomial x (k+1)
            else if i = 2 then characterPolynomial x (k+2)
            else if i = 3 then characterPolynomial x (k+3)
            else characterPolynomial x (k+4))

private theorem mul_finite_sum (factor : RatPoly) (f : Nat → RatPoly) :
    ∀ xs : List Nat,
      RatPolyCoeffEqv (polyMul factor (finitePolySum f xs))
        (finitePolySum (fun j => polyMul factor (f j)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right factor
  | j :: js =>
      (RatPolyCoeffEqv.mul_add_right factor (f j) (finitePolySum f js)).trans
        ((RatPolyCoeffEqv.refl _).add (mul_finite_sum factor f js))

private theorem finite_sum_congr (f g : Nat → RatPoly)
    (h : ∀ j, RatPolyCoeffEqv (f j) (g j)) :
    ∀ xs : List Nat, RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl polyZero
  | j :: js => (h j).add (finite_sum_congr f g h js)

/-- Exact complete finite-prefix identity. It retains all signed basis terms
in their ORIGINAL index order; no endpoint coefficient is silently dropped. -/
theorem heat_quartic_expansion (w : Q') (K : Nat) (x : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (defect x) (defect x)) (heatPrefix w K x))
      (finitePolySum (fun j => polySmul (coeffW w j) (quarticBasis x j))
        (List.range (K+1))) := by
  unfold heatPrefix
  exact (mul_finite_sum (polyMul (defect x) (defect x))
    (fun j => polySmul (coeffW w j) (characterPolynomial x j)) (List.range (K+1))).trans
    (finite_sum_congr _ _ (fun j =>
      (RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
        ((defect_square_basis x j).smul _)) (List.range (K+1)))

#print axioms defect
#print axioms quarticBasis
#print axioms defect_square_basis
#print axioms heat_quartic_expansion

end YMGap.Continuum.SU2QuaternionHeatQuarticExpansion

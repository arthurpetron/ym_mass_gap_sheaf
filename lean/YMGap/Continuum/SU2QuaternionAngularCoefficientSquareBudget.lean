/-
# Explicit coefficient-square budget for signed angular families

The local l1-square curvature cost is converted to an l2-square cost with
the actual local list length.  Repeated generators and repeated selected
heat factors are deliberately retained.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature
import YMGap.Continuum.RationalListCauchy

namespace YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalListCauchy
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionSignedHeatLogCurvature
open YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature

local infix:50 " ≈ " => Q'.eqv

def coefficientSquareSum {n : Nat} (terms : List (AngularTerm n)) : Q' :=
  qsumSquares (terms.map (fun term => term.coefficient))

def localCoefficientSquareSum {n : Nat}
    (terms : List (AngularTerm n)) (selected : Nat) : Q' :=
  coefficientSquareSum
    (terms.filter (fun term => decide (term.block.val = selected)))

def productCoefficientSquareSum {n : Nat}
    (terms : List (AngularTerm n)) : List Nat → Q'
  | [] => 0
  | i::ids => localCoefficientSquareSum terms i +
      productCoefficientSquareSum terms ids

theorem coefficientSquareSum_nonnegative {n : Nat} :
    ∀ terms : List (AngularTerm n), (0 : Q') ≤ coefficientSquareSum terms
  | [] => Q'.le_refl' 0
  | term::terms =>
      Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg term.coefficient)
        (coefficientSquareSum_nonnegative terms)

theorem localCoefficientSquareSum_nonnegative {n : Nat}
    (terms : List (AngularTerm n)) (selected : Nat) :
    (0 : Q') ≤ localCoefficientSquareSum terms selected :=
  coefficientSquareSum_nonnegative _

theorem productCoefficientSquareSum_nonnegative {n : Nat}
    (terms : List (AngularTerm n)) : ∀ ids : List Nat,
    (0 : Q') ≤ productCoefficientSquareSum terms ids
  | [] => Q'.le_refl' 0
  | _::ids => Q'.zero_le_add _ _ (localCoefficientSquareSum_nonnegative terms _)
      (productCoefficientSquareSum_nonnegative terms ids)

private theorem absSquares_eqv {n : Nat} : ∀ terms : List (AngularTerm n),
    qsumSquares (terms.map (fun term => Q'.abs term.coefficient)) ≈
      coefficientSquareSum terms
  | [] => Q'.eqv_refl 0
  | term::terms => Q'.add_eqv_congr'
      (abs_square_eqv term.coefficient) (absSquares_eqv terms)

private theorem coefficientL1_eq_qsum {n : Nat} : ∀ terms : List (AngularTerm n),
    coefficientL1 terms = qsum (terms.map (fun term => Q'.abs term.coefficient))
  | [] => rfl
  | term::terms => congrArg (fun c => Q'.abs term.coefficient + c)
      (coefficientL1_eq_qsum terms)

/-- Finite Cauchy for the exact signed angular coefficient list. -/
theorem coefficientL1_sq_le_length_mul_coefficientSquareSum {n : Nat}
    (terms : List (AngularTerm n)) :
    coefficientL1 terms * coefficientL1 terms ≤
      Q'.ofNat terms.length * coefficientSquareSum terms := by
  have h := qsum_sq_le_length_mul_qsumSquares
    (terms.map (fun term => Q'.abs term.coefficient))
  have hlen : (terms.map (fun term => Q'.abs term.coefficient)).length = terms.length :=
    List.length_map (fun term : AngularTerm n => Q'.abs term.coefficient)
  rw [hlen] at h
  rw [← coefficientL1_eq_qsum] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat terms.length) _ _
      (absSquares_eqv terms)))

private theorem localCost_le {n : Nat} (terms : List (AngularTerm n))
    (C : Q') (hC : (0 : Q') ≤ C) (selected m : Nat)
    (hlen : (terms.filter (fun term => decide (term.block.val = selected))).length ≤ m) :
    localCurvatureCost terms C selected ≤
      (Q'.ofNat m*C) * localCoefficientSquareSum terms selected := by
  let localized := terms.filter (fun term => decide (term.block.val = selected))
  have hs := coefficientL1_sq_le_length_mul_coefficientSquareSum localized
  have hnat : Q'.ofNat localized.length ≤ Q'.ofNat m := by
    change (Int.ofNat localized.length) * 1 ≤ (Int.ofNat m) * 1
    simpa only [Int.mul_one] using Int.ofNat_le.mpr hlen
  have hS := localCoefficientSquareSum_nonnegative terms selected
  have hlenS := Q'.mul_le_mul_of_nonneg_right _ _ _ hnat hS
  have hs' := Q'.le_trans' _ _ _ hs hlenS
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ C hs' hC
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.var 1))
        (by decide) (fun | 0 => localCoefficientL1 terms selected | _ => C)))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide)
        (fun | 0 => Q'.ofNat m | 1 => localCoefficientSquareSum terms selected | _ => C))))

/-- The whole repeated-factor curvature cost is controlled by the repeated
block-local coefficient-square sum.  The only multiplicity loss is the
explicit supplied local list bound `m`. -/
theorem productCurvatureCost_le_coefficientSquares {n : Nat}
    (terms : List (AngularTerm n)) (C : Q') (hC : (0 : Q') ≤ C)
    (m : Nat) (ids : List Nat)
    (hlocal : ∀ i, i ∈ ids →
      (terms.filter (fun term => decide (term.block.val = i))).length ≤ m) :
    productCurvatureCost terms C ids ≤
      (Q'.ofNat m*C) * productCoefficientSquareSum terms ids := by
  revert hlocal
  induction ids with
  | nil =>
    intro _
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv _))
  | cons i ids ih =>
    intro hlocal
    simp only [productCurvatureCost, productCoefficientSquareSum]
    have hi := localCost_le terms C hC i m (hlocal i List.mem_cons_self)
    have ht := ih (fun j hj => hlocal j (List.mem_cons_of_mem i hj))
    have hadd := Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hi) (Q'.add_le_add_left _ _ _ ht)
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat m*C)
        (localCoefficientSquareSum terms i)
        (productCoefficientSquareSum terms ids))))

end YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget

#print axioms YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget.coefficientSquareSum_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget.coefficientL1_sq_le_length_mul_coefficientSquareSum
#print axioms YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget.productCurvatureCost_le_coefficientSquares

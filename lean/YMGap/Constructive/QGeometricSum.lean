/-
# Finite geometric sums over constructive rationals

This module isolates the division-free telescope used by finite rational
fixed-point compilers.  It stays entirely in `Q'` and proves equality only
through `Q'.eqv`; no quotient elimination, classical reasoning, or hidden
analytic limit is involved.
-/

import YMGap.Constructive.RegularCRealArith

namespace YMGap.Constructive.QGeometricSum

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

/-- The finite geometric partial sum `sum_{k=0}^{M} y^k`. -/
def geomSum (y : Q') : Nat -> Q'
  | 0 => (1 : Q')
  | m + 1 => geomSum y m + y ^ (m + 1)

@[simp] theorem geomSum_zero (y : Q') : geomSum y 0 = 1 := rfl

theorem geomSum_succ (y : Q') (m : Nat) :
    geomSum y (m + 1) = geomSum y m + y ^ (m + 1) := rfl

/-- Division-free finite geometric telescope:
`(y - 1) * sum_{k=0}^{M} y^k = y^(M+1) - 1`. -/
theorem geomSum_telescope (y : Q') (M : Nat) :
    ((y + (-(1 : Q'))) * geomSum y M).eqv
      (y ^ (M + 1) + (-(1 : Q'))) := by
  induction M with
  | zero =>
      rw [geomSum_zero]
      refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ?_
      refine Q'.add_eqv_congr_right _ _ _ ?_
      rw [Q'.pow_succ, Q'.pow_zero]
      exact Q'.eqv_symm (Q'.mul_one_eqv y)
  | succ m ih =>
      rw [geomSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (y + (-(1 : Q')))
          (geomSum y m) (y ^ (m + 1))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      have hsecond :
          ((y + (-(1 : Q'))) * y ^ (m + 1)).eqv
            (y ^ (m + 2) + (-(y ^ (m + 1)))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_mul_eqv y (-(1 : Q')) (y ^ (m + 1))) ?_
        refine Q'.eqv_trans _
          (y ^ (m + 2) + ((-(1 : Q')) * y ^ (m + 1))) _
          (Q'.add_eqv_congr_right _ _ _ ?_) ?_
        · show (y * y ^ (m + 1)).eqv (y ^ (m + 2))
          rw [show m + 2 = (m + 1) + 1 by omega, Q'.pow_succ]
          exact Q'.eqv_refl _
        · exact Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _
              (Q'.neg_mul_eqv 1 (y ^ (m + 1)))
              (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (y ^ (m + 1)))))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ hsecond) ?_
      calc
        (y ^ (m + 1) + (-(1 : Q'))) +
            (y ^ (m + 2) + (-(y ^ (m + 1))))
            ≈ ((-(1 : Q')) + y ^ (m + 1)) +
                (y ^ (m + 2) + (-(y ^ (m + 1)))) :=
              Q'.add_eqv_congr_right _ _ _
                (Q'.add_comm_eqv (y ^ (m + 1)) (-(1 : Q')))
        _ ≈ (-(1 : Q')) +
              (y ^ (m + 1) +
                (y ^ (m + 2) + (-(y ^ (m + 1))))) :=
              Q'.add_assoc_eqv (-(1 : Q')) (y ^ (m + 1))
                (y ^ (m + 2) + (-(y ^ (m + 1))))
        _ ≈ (-(1 : Q')) +
              (y ^ (m + 1) +
                ((-(y ^ (m + 1))) + y ^ (m + 2))) :=
              Q'.add_eqv_congr_left _ _ _
                (Q'.add_eqv_congr_left _ _ _
                  (Q'.add_comm_eqv (y ^ (m + 2))
                    (-(y ^ (m + 1)))))
        _ ≈ (-(1 : Q')) +
              ((y ^ (m + 1) + (-(y ^ (m + 1)))) +
                y ^ (m + 2)) :=
              Q'.add_eqv_congr_left _ _ _
                (Q'.eqv_symm
                  (Q'.add_assoc_eqv (y ^ (m + 1))
                    (-(y ^ (m + 1))) (y ^ (m + 2))))
        _ ≈ (-(1 : Q')) + ((0 : Q') + y ^ (m + 2)) :=
              Q'.add_eqv_congr_left _ _ _
                (Q'.add_eqv_congr_right _ _ _
                  (Q'.add_neg_self_eqv (y ^ (m + 1))))
        _ ≈ (-(1 : Q')) + y ^ (m + 2) := by
              refine Q'.add_eqv_congr_left _ _ _ ?_
              rw [Q'.zero_add']
              exact Q'.eqv_refl _
        _ ≈ y ^ (m + 2) + (-(1 : Q')) :=
              Q'.add_comm_eqv (-(1 : Q')) (y ^ (m + 2))

/-- The same telescope in fixed-point form:
`(1-y) * sum_{k=0}^{M} y^k = 1-y^(M+1)`. -/
theorem one_sub_mul_geomSum (y : Q') (M : Nat) :
    (((1 : Q') + -y) * geomSum y M).eqv
      ((1 : Q') + -(y ^ (M + 1))) := by
  have hfactor : ((1 : Q') + -y).eqv (-(y + (-(1 : Q')))) := by
    refine Q'.eqv_trans _ ((-y) + (1 : Q')) _
      (Q'.add_comm_eqv 1 (-y)) ?_
    refine Q'.eqv_trans _ ((-y) + (-(-(1 : Q')))) _
      (Q'.add_eqv_congr_left (-y) _ _
        (Q'.eqv_symm (Q'.neg_neg_eqv 1))) ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv y (-(1 : Q')))
  refine Q'.eqv_trans _
    ((-(y + (-(1 : Q')))) * geomSum y M) _
    (Q'.mul_eqv_congr_right _ _ _ hfactor) ?_
  refine Q'.eqv_trans _
    (-((y + (-(1 : Q'))) * geomSum y M)) _
    (Q'.neg_mul_eqv (y + (-(1 : Q'))) (geomSum y M)) ?_
  refine Q'.eqv_trans _
    (-(y ^ (M + 1) + (-(1 : Q')))) _
    (Q'.neg_eqv_congr _ _ (geomSum_telescope y M)) ?_
  refine Q'.eqv_trans _
    (-(y ^ (M + 1)) + (-(-(1 : Q')))) _
    (Q'.neg_add_eqv (y ^ (M + 1)) (-(1 : Q'))) ?_
  refine Q'.eqv_trans _
    (-(y ^ (M + 1)) + (1 : Q')) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv 1)) ?_
  exact Q'.add_comm_eqv (-(y ^ (M + 1))) 1

end YMGap.Constructive.QGeometricSum

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.QGeometricSum.geomSum_telescope
#print axioms YMGap.Constructive.QGeometricSum.one_sub_mul_geomSum

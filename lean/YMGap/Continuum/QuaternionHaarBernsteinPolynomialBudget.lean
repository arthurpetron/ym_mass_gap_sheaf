/-
Computed coefficient-error budget for a finite signed one-block RatPoly.
Each monomial uses the actual four tensor Bernstein rows; its coefficient is
paid by an absolute value in the original list, including duplicates and zero
terms. This file has no Haar-to-grid assertion or analytic premise.
-/

import YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding
import YMGap.Continuum.QuaternionHaarTensorBernsteinError
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarTensorBernsteinError
open YMGap.Continuum.QuaternionHaarBernsteinMonomialRecoding

local infix:50 " ≈ " => Q'.eqv

private def i0 : Fin 4 := ⟨0, by decide⟩
private def i1 : Fin 4 := ⟨1, by decide⟩
private def i2 : Fin 4 := ⟨2, by decide⟩
private def i3 : Fin 4 := ⟨3, by decide⟩

/-- The checked four-row coefficient error for a single monomial. -/
def monomialGridBudget (m : List Nat) (eta : Q') : Q' :=
  productErrorBudget (monomialFactor m i0) (monomialFactor m i1)
    (monomialFactor m i2) (monomialFactor m i3) eta

/-- The literal signed-term-list budget; cancellation is not presumed. -/
def polynomialGridBudget : RatPoly → Q' → Q'
  | [], _ => 0
  | (m,c) :: rest, eta => Q'.abs c * monomialGridBudget m eta +
      polynomialGridBudget rest eta

/-- An eta-independent ceiling for one factor at every `0 < eta ≤ 1`. -/
def factorCeiling (m : List Nat) (i : Fin 4) : Q' :=
  weightedL1 1 (monomialFactor m i) + 1

theorem factorCeiling_nonnegative (m : List Nat) (i : Fin 4) :
    (0 : Q') ≤ factorCeiling m i :=
  Q'.zero_le_add _ _ (weightedL1_nonnegative 1 (by decide) _)
    (by decide)

private theorem rowBound_le_factorCeiling (m : List Nat) (i : Fin 4)
    (eta : Q') (heta : eta ≤ 1) :
    rowBound (monomialFactor m i) eta ≤ factorCeiling m i := by
  have he : rowError eta ≤ 1 := by
    have h0 := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half heta
      HalfPow.half_nonneg
    exact Q'.le_trans' _ _ _ h0
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
        (by decide : HalfPow.half ≤ (1 : Q')))
  exact Q'.add_le_add_left _ _ _ he

private theorem mul_mono {a b A B : Q'} (ha : a ≤ A) (hb : b ≤ B)
    (hbn : (0 : Q') ≤ b) (hAn : (0 : Q') ≤ A) :
    a*b ≤ A*B :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ha hbn)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hAn)

private theorem triple_mono {a b c A B C : Q'}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (hbn : (0 : Q') ≤ b) (hcn : (0 : Q') ≤ c)
    (hAn : (0 : Q') ≤ A) (hBn : (0 : Q') ≤ B) :
    a*b*c ≤ A*B*C :=
  mul_mono (mul_mono ha hb hbn hAn) hc hcn
    (Q'.mul_nonneg _ _ hAn hBn)

/-- A fixed, computable four-term triple-product ceiling. -/
def monomialGridStrength (m : List Nat) : Q' :=
  let C0 := factorCeiling m i0
  let C1 := factorCeiling m i1
  let C2 := factorCeiling m i2
  let C3 := factorCeiling m i3
  C1*C2*C3 + C0*C2*C3 + C0*C1*C3 + C0*C1*C2

theorem monomialGridStrength_nonnegative (m : List Nat) :
    (0 : Q') ≤ monomialGridStrength m := by
  let C0 := factorCeiling m i0
  let C1 := factorCeiling m i1
  let C2 := factorCeiling m i2
  let C3 := factorCeiling m i3
  have h0 : (0 : Q') ≤ C0 := factorCeiling_nonnegative m i0
  have h1 : (0 : Q') ≤ C1 := factorCeiling_nonnegative m i1
  have h2 : (0 : Q') ≤ C2 := factorCeiling_nonnegative m i2
  have h3 : (0 : Q') ≤ C3 := factorCeiling_nonnegative m i3
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ h1 h2) h3)
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ h0 h2) h3))
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ h0 h1) h3))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ h0 h1) h2)

private theorem monomialGridBudget_le_strength (m : List Nat)
    (eta : Q') (he : (0 : Q') < eta) (heta : eta ≤ 1) :
    monomialGridBudget m eta ≤ rowError eta * monomialGridStrength m := by
  let B0 := rowBound (monomialFactor m i0) eta
  let B1 := rowBound (monomialFactor m i1) eta
  let B2 := rowBound (monomialFactor m i2) eta
  let B3 := rowBound (monomialFactor m i3) eta
  let C0 := factorCeiling m i0
  let C1 := factorCeiling m i1
  let C2 := factorCeiling m i2
  let C3 := factorCeiling m i3
  have hB0 : (0 : Q') ≤ B0 := rowBound_nonnegative _ eta he
  have hB1 : (0 : Q') ≤ B1 := rowBound_nonnegative _ eta he
  have hB2 : (0 : Q') ≤ B2 := rowBound_nonnegative _ eta he
  have hB3 : (0 : Q') ≤ B3 := rowBound_nonnegative _ eta he
  have hC0 : (0 : Q') ≤ C0 := factorCeiling_nonnegative m i0
  have hC1 : (0 : Q') ≤ C1 := factorCeiling_nonnegative m i1
  have hC2 : (0 : Q') ≤ C2 := factorCeiling_nonnegative m i2
  have hC3 : (0 : Q') ≤ C3 := factorCeiling_nonnegative m i3
  have h0 : B0 ≤ C0 := rowBound_le_factorCeiling m i0 eta heta
  have h1 : B1 ≤ C1 := rowBound_le_factorCeiling m i1 eta heta
  have h2 : B2 ≤ C2 := rowBound_le_factorCeiling m i2 eta heta
  have h3 : B3 ≤ C3 := rowBound_le_factorCeiling m i3 eta heta
  have hsum :
      B1*B2*B3 + B0*B2*B3 + B0*B1*B3 + B0*B1*B2 ≤
        C1*C2*C3 + C0*C2*C3 + C0*C1*C3 + C0*C1*C2 :=
    Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add
          (triple_mono h1 h2 h3 hB2 hB3 hC1 hC2)
          (triple_mono h0 h2 h3 hB2 hB3 hC0 hC2))
        (triple_mono h0 h1 h3 hB1 hB3 hC0 hC1))
      (triple_mono h0 h1 h2 hB1 hB2 hC0 hC1)
  change rowError eta *
      (B1*B2*B3 + B0*B2*B3 + B0*B1*B3 + B0*B1*B2) ≤
    rowError eta *
      (C1*C2*C3 + C0*C2*C3 + C0*C1*C3 + C0*C1*C2)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hsum
    (rowError_nonnegative eta he)

/-- Finite absolute coefficient sum of the fixed per-monomial strengths. -/
def polynomialGridStrength : RatPoly → Q'
  | [] => 0
  | (m,c) :: rest => Q'.abs c * monomialGridStrength m +
      polynomialGridStrength rest

theorem polynomialGridStrength_nonnegative :
    ∀ p : RatPoly, (0 : Q') ≤ polynomialGridStrength p
  | [] => Q'.le_refl' 0
  | (m,c) :: rest => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (Q'.abs_nonneg c)
        (monomialGridStrength_nonnegative m))
      (polynomialGridStrength_nonnegative rest)

private theorem polynomialGridBudget_le_strength (p : RatPoly)
    (eta : Q') (he : (0 : Q') < eta) (heta : eta ≤ 1) :
    polynomialGridBudget p eta ≤
      rowError eta * polynomialGridStrength p := by
  induction p with
  | nil =>
      change (0 : Q') ≤ rowError eta * 0
      exact Q'.ge_of_eqv (Q'.mul_zero_eqv _)
  | cons term rest ih =>
      rcases term with ⟨m,c⟩
      have ht : Q'.abs c * monomialGridBudget m eta ≤
          Q'.abs c * (rowError eta * monomialGridStrength m) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (monomialGridBudget_le_strength m eta he heta)
          (Q'.abs_nonneg c)
      have hs := Q'.add_le_add ht ih
      have hr : Q'.abs c*(rowError eta*monomialGridStrength m) +
          rowError eta*polynomialGridStrength rest ≈
          rowError eta*(Q'.abs c*monomialGridStrength m+
            polynomialGridStrength rest) :=
        poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.var 3)))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
          (by decide)
          (fun | 0 => Q'.abs c | 1 => rowError eta
               | 2 => monomialGridStrength m | _ => polynomialGridStrength rest)
      exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr)

/-- Positive rational denominator, including empty and zero polynomials. -/
def gridDenominator (p : RatPoly) (epsilon : Q') : Q' :=
  1 + Q'.abs epsilon + polynomialGridStrength p

theorem gridDenominator_positive (p : RatPoly) (epsilon : Q') :
    (0 : Q') < gridDenominator p epsilon :=
  Q'.pos_add_nonneg
    (Q'.pos_add_nonneg (by decide) (Q'.abs_nonneg epsilon))
    (polynomialGridStrength_nonnegative p)

/-- Computable positive row tolerance; no division by a possibly zero K. -/
def gridTolerance (p : RatPoly) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (gridDenominator p epsilon)
    (gridDenominator_positive p epsilon)

theorem gridTolerance_positive (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) : (0 : Q') < gridTolerance p epsilon :=
  Q'.divPos_pos _ _ _ he

theorem gridTolerance_pin (p : RatPoly) (epsilon : Q') :
    gridTolerance p epsilon * gridDenominator p epsilon ≈ epsilon :=
  Q'.divPos_mul_eqv _ _ _

private theorem epsilon_le_denominator (p : RatPoly) (epsilon : Q') :
    epsilon ≤ gridDenominator p epsilon := by
  have h0 : epsilon ≤ Q'.abs epsilon := Q'.le_abs_self epsilon
  have h1 : Q'.abs epsilon ≤ 1 + Q'.abs epsilon :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have h2 : 1 + Q'.abs epsilon ≤ gridDenominator p epsilon :=
    Q'.add_le_self_of_nonneg _ _ (polynomialGridStrength_nonnegative p)
  exact Q'.le_trans' _ _ _ h0 (Q'.le_trans' _ _ _ h1 h2)

theorem gridTolerance_le_one (p : RatPoly) (epsilon : Q') :
    gridTolerance p epsilon ≤ 1 := by
  have he := epsilon_le_denominator p epsilon
  have hmul : epsilon ≤ 1 * gridDenominator p epsilon :=
    Q'.le_trans' _ _ _ he (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  exact Q'.divPos_le_of_le_mul _ _ _ hmul

private theorem strength_le_denominator (p : RatPoly) (epsilon : Q') :
    polynomialGridStrength p ≤ gridDenominator p epsilon := by
  have hsum : (0 : Q') ≤ 1 + Q'.abs epsilon :=
    Q'.zero_le_add _ _ (by decide) (Q'.abs_nonneg epsilon)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hsum)
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

theorem gridTolerance_mul_strength_le (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    gridTolerance p epsilon * polynomialGridStrength p ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (strength_le_denominator p epsilon)
      (Q'.le_of_lt (gridTolerance_positive p epsilon he)))
    (Q'.le_of_eqv (gridTolerance_pin p epsilon))

/-- The aggregate grid-coefficient error occupies at most half the requested
positive rational tolerance. No support hypothesis is needed for this purely
finite arithmetic estimate; the original signed Haar/grid join is separate. -/
theorem polynomialGridBudget_half (p : RatPoly) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    polynomialGridBudget p (gridTolerance p epsilon) ≤
      Q'.invSucc 1 * epsilon := by
  let eta := gridTolerance p epsilon
  have heta : (0 : Q') < eta := gridTolerance_positive p epsilon he
  have heta1 : eta ≤ 1 := gridTolerance_le_one p epsilon
  have hbudget := polynomialGridBudget_le_strength p eta heta heta1
  have hK := gridTolerance_mul_strength_le p epsilon he
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hK
    HalfPow.half_nonneg
  have hassoc : rowError eta * polynomialGridStrength p ≈
      HalfPow.half * (eta * polynomialGridStrength p) :=
    Q'.mul_assoc_eqv _ _ _
  have hhalf : HalfPow.half * epsilon ≈ Q'.invSucc 1 * epsilon :=
    Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half ≈ Q'.invSucc 1)
  exact Q'.le_trans' _ _ _ hbudget
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hhalf)))

end YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget

#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.monomialGridBudget
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.polynomialGridBudget
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.factorCeiling
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.factorCeiling_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.monomialGridStrength
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.monomialGridStrength_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.polynomialGridStrength
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.polynomialGridStrength_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridDenominator
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridDenominator_positive
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridTolerance
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridTolerance_positive
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridTolerance_pin
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridTolerance_le_one
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.gridTolerance_mul_strength_le
#print axioms YMGap.Continuum.QuaternionHaarBernsteinPolynomialBudget.polynomialGridBudget_half

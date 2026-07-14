/-
# Polynomial parity-block orthogonality

This lifts monomial parity orthogonality to arbitrary finite polynomials.  The
result is the exact block-diagonal split used by the constructive positivity
argument: cross products of two different eight-coordinate parity sectors
have zero product-Haar expectation.
-/

import YMGap.Continuum.SU2QuaternionHaarParitySectors

namespace YMGap.Continuum.SU2QuaternionHaarParityPolynomial

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarParitySectors

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

private theorem productHaar_single_pair_cross_zero
    (a b : RatTerm)
    (hpar : exponentParity8 a.1 ≠ exponentParity8 b.1) :
    productHaar (polyMul [a] [b]) ≈ 0 := by
  refine Q'.eqv_trans _ (productHaarLinearSum (polyMul [a] [b])) _
    (productHaar_eqv_linearSum _) ?_
  change (a.2 * b.2) * productHaarMono (monoMul a.1 b.1) + 0 ≈ 0
  rw [Q'.add_zero']
  refine Q'.eqv_trans _ ((a.2 * b.2) * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (productHaarMono_cross_parity_zero_of_ne a.1 b.1 hpar)
  · exact Q'.mul_zero_eqv _

private theorem productHaar_single_left_cross_zero
    (a : RatTerm) : ∀ q : RatPoly,
    (∀ b, b ∈ q → exponentParity8 a.1 ≠ exponentParity8 b.1) →
      productHaar (polyMul [a] q) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | b :: q, hpar => by
      have hmul :
          polyMul [a] (b :: q) = polyMul [a] [b] ++ polyMul [a] q := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (productHaar (polyMul [a] [b]) + productHaar (polyMul [a] q)) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (productHaar_single_pair_cross_zero a b (hpar b (by simp)))
          (productHaar_single_left_cross_zero a q (by
            intro c hc
            exact hpar c (by simp [hc])))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- If every left-right monomial pair lies in different parity sectors, the
whole polynomial pairing vanishes. -/
theorem productHaar_mul_cross_parity_zero : ∀ p q : RatPoly,
    (∀ a, a ∈ p → ∀ b, b ∈ q →
      exponentParity8 a.1 ≠ exponentParity8 b.1) →
    productHaar (polyMul p q) ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | a :: p, q, hpar => by
      have hmul :
          polyMul (a :: p) q = polyMul [a] q ++ polyMul p q := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (productHaar (polyMul [a] q) + productHaar (polyMul p q)) _
        (productHaar_append_eqv _ _) ?_
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (productHaar_single_left_cross_zero a q (by
            intro b hb
            exact hpar a (by simp) b hb))
          (productHaar_mul_cross_parity_zero p q (by
            intro c hc b hb
            exact hpar c (by simp [hc]) b hb))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- A finite polynomial is supported in one explicit parity sector. -/
def AllParity8 (s : Parity8) (p : RatPoly) : Prop :=
  ∀ t, t ∈ p → exponentParity8 t.1 = s

/-- Different polynomial parity sectors form exact orthogonal blocks. -/
theorem productHaar_distinct_parity_sectors_zero
    (s t : Parity8) (p q : RatPoly)
    (hp : AllParity8 s p) (hq : AllParity8 t q) (hst : s ≠ t) :
    productHaar (polyMul p q) ≈ 0 := by
  apply productHaar_mul_cross_parity_zero
  intro a ha b hb
  rw [hp a ha, hq b hb]
  exact hst

end YMGap.Continuum.SU2QuaternionHaarParityPolynomial

#print axioms YMGap.Continuum.SU2QuaternionHaarParityPolynomial.productHaar_mul_cross_parity_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarParityPolynomial.productHaar_distinct_parity_sectors_zero

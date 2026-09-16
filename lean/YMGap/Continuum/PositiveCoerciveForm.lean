/-
# A coercive rational form controls the actual image norm from below

The lower form bound L B(a,a) <= B(a,Pa) and sharp Cauchy--Schwarz
give L^2 B(a,a) <= B(Pa,Pa) on the same carrier. Cancellation is used
only when the rational input norm is strictly positive; the zero-norm
case requires no division. No symmetry or linearity of P is assumed.
-/

import YMGap.Continuum.GNSQuotient

namespace YMGap.Continuum.PositiveCoerciveForm

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

/-- A nonnegative coercivity floor yields a lower squared-norm bound for
the actual map, without choosing an inverse or dividing by a null norm. -/
theorem lower_norm (D : GNSData) (P : D.V → D.V) {L : Q'}
    (hL : (0 : Q') ≤ L)
    (hlower : ∀ a, L * D.B a a ≤ D.B a (P a)) (a : D.V) :
    (L * L) * D.B a a ≤ D.B (P a) (P a) := by
  let A := D.B a a
  let M := D.B a (P a)
  have hLA : (0 : Q') ≤ L * A := Q'.mul_nonneg _ _ hL (D.self_nonneg a)
  have hM : (0 : Q') ≤ M := Q'.le_trans' _ _ _ hLA (hlower a)
  have hsquare : (L * A) * (L * A) ≤ M * M :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (L * A) (hlower a) hLA)
      (Q'.mul_le_mul_of_nonneg_left _ _ M (hlower a) hM)
  have hpin : (L * A) * (L * A) ≈ A * ((L * L) * A) :=
    Q'.eqv_trans _ _ _ (mul4_rearrange L A L A) (mul_pull (L * L) A A)
  have hproduct : A * ((L * L) * A) ≤ A * D.B (P a) (P a) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin)
      (Q'.le_trans' _ _ _ hsquare (D.cauchy_schwarz a (P a)))
  by_cases hA : (0 : Q') < A
  · exact q_cancel_left hA hproduct
  · have hnum : A.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hA ((zero_lt_iff_num_pos A).mpr h))
    have hA0 : A ≤ (0 : Q') := by
      change A.num * (1 : Int) ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (L * L) hA0 (Q'.mul_nonneg _ _ hL hL))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (L * L)))
        (D.self_nonneg (P a)))

end YMGap.Continuum.PositiveCoerciveForm

#print axioms YMGap.Continuum.PositiveCoerciveForm.lower_norm

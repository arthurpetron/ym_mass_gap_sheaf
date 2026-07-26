/-
# Constructive BF4 Gaussian Perron ratio

The five-holonomy Gaussian generalized spectrum is `4,4,4,6,6`.  The
largest non-vacuum Mehler ratio is the mode at generalized eigenvalue four,

  q₀ = 3 - 2 √2.

This module constructs that irrational number as a genuine `CReal`, proves
that its square-root component is exactly `√2`, and supplies strict rational
brackets

  1/20 ≤ q₀ ≤ 9/50 < 1/5.

The shifted Heron presentation is intentional: its approximations already
lie in the positive Perron window, so positivity and the upper bound lift
directly through the constructive-real order.

This is the exact Gaussian spectral input.  It does not identify the
nonlinear BF4 operator with its Gaussian limit.
-/

import YMGap.Continuum.BF4FiveHolonomyGaussian
import YMGap.Continuum.QuadraticKernel

namespace YMGap.Continuum.BF4GaussianPerronRatio

open YMGap.Constructive
open YMGap.Continuum.QuadraticKernel

/-- `7/5`, a positive lower witness whose square is below two. -/
def sevenFifths : Q' := Q'.mkPos 7 5 (by decide)

/-- A sharper rational lower bound on `√2`. -/
def rootLower : Q' := Q'.mkPos 141 100 (by decide)

/-- A rational upper bound on the shifted Heron approximants to `√2`. -/
def rootUpper : Q' := Q'.mkPos 59 40 (by decide)

def oneTwentieth : Q' := Q'.mkPos 1 20 (by decide)
def nineFiftieths : Q' := Q'.mkPos 9 50 (by decide)
def oneFifth : Q' := Q'.mkPos 1 5 (by decide)
def sevenHundredths : Q' := Q'.mkPos 7 100 (by decide)
def oneQuarter : Q' := Q'.mkPos 1 4 (by decide)

theorem sevenFifths_pos : (0 : Q') < sevenFifths := by decide

theorem sevenFifths_sq_le_two :
    sevenFifths * sevenFifths ≤ (2 : Q') := by decide

theorem rootLower_pos : (0 : Q') < rootLower := by decide

theorem rootLower_sq_le_two :
    rootLower * rootLower ≤ (2 : Q') := by decide

/-- `√2` represented by the Heron sequence after two exact startup steps. -/
def sqrtTwo : CReal where
  approx n := CReal.heronSeq 2 (n + 2)
  cauchy := by
    intro ε hε
    let root :=
      CReal.sqrtFrom 2 sevenFifths (by decide)
        sevenFifths_pos sevenFifths_sq_le_two
    obtain ⟨N, hN⟩ := root.cauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have hm' : N ≤ m + 2 := by omega
    have hn' : N ≤ n + 2 := by omega
    simpa [root, CReal.sqrtFrom_approx] using
      hN (m + 2) (n + 2) hm' hn'

/-- The shifted presentation is the same constructive real as the standard
Heron presentation with lower witness `7/5`. -/
theorem sqrtTwo_equiv_sqrtFrom :
    CReal.Equiv sqrtTwo
      (CReal.sqrtFrom 2 sevenFifths (by decide)
        sevenFifths_pos sevenFifths_sq_le_two) := by
  let root :=
    CReal.sqrtFrom 2 sevenFifths (by decide)
      sevenFifths_pos sevenFifths_sq_le_two
  intro ε hε
  obtain ⟨N, hN⟩ := root.cauchy ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hn' : N ≤ n + 2 := by omega
  simpa [sqrtTwo, root, CReal.sqrtFrom_approx] using
    hN (n + 2) n hn' hn

/-- The shifted real is exactly a square root of two. -/
theorem sqrtTwo_sq_equiv_two :
    CReal.Equiv (CReal.mul sqrtTwo sqrtTwo) (CReal.ofQ' 2) := by
  let root :=
    CReal.sqrtFrom 2 sevenFifths (by decide)
      sevenFifths_pos sevenFifths_sq_le_two
  have hroot : CReal.Equiv sqrtTwo root := by
    simpa [root] using sqrtTwo_equiv_sqrtFrom
  have hleft :
      CReal.Equiv (CReal.mul sqrtTwo sqrtTwo)
        (CReal.mul root sqrtTwo) :=
    CReal.mul_congr_left hroot
  have hright :
      CReal.Equiv (CReal.mul root sqrtTwo)
        (CReal.mul root root) :=
    TrigSignedAdd.mul_congr_right hroot
  exact CReal.Equiv.trans hleft
    (CReal.Equiv.trans hright
      (CReal.sqrtFrom_sq_equiv 2 sevenFifths (by decide)
        sevenFifths_pos sevenFifths_sq_le_two))

/-- The shifted approximants retain the sharp elementary lower bound
`141/100 ≤ √2`. -/
theorem rootLower_le_sqrtTwo_approx (n : Nat) :
    rootLower ≤ sqrtTwo.approx n := by
  exact CReal.heronSeq_lb 2 rootLower (by decide)
    rootLower_pos rootLower_sq_le_two (n + 2)

/-- Two startup steps put every retained approximant below `59/40`. -/
theorem sqrtTwo_approx_le_rootUpper (n : Nat) :
    sqrtTwo.approx n ≤ rootUpper := by
  have hmono :
      CReal.heronSeq 2 (n + 2) ≤ CReal.heronSeq 2 2 :=
    CReal.heronSeq_antitone 2 (by decide) (by omega)
  exact Q'.le_trans' _ _ _ hmono (by decide)

/-- The exact Gaussian Perron ratio `3 - 2√2`. -/
def gaussianPerronRatio : CReal :=
  CReal.add (CReal.ofQ' 3)
    (CReal.neg (CReal.mul (CReal.ofQ' 2) sqrtTwo))

/-- Pointwise positive rational floor on the Gaussian ratio. -/
theorem oneTwentieth_le_ratio_approx (n : Nat) :
    oneTwentieth ≤ gaussianPerronRatio.approx n := by
  have hroot := sqrtTwo_approx_le_rootUpper n
  have hmul :
      (2 : Q') * sqrtTwo.approx n ≤ (2 : Q') * rootUpper :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hroot (by decide)
  have hneg :
      -((2 : Q') * rootUpper) ≤ -((2 : Q') * sqrtTwo.approx n) :=
    Q'.neg_le_neg hmul
  have hadd :
      (3 : Q') + -((2 : Q') * rootUpper)
        ≤ (3 : Q') + -((2 : Q') * sqrtTwo.approx n) :=
    Q'.add_le_add_left 3 _ _ hneg
  exact Q'.le_trans' _ _ _
    (by decide :
      oneTwentieth ≤ (3 : Q') + -((2 : Q') * rootUpper))
    (by simpa [gaussianPerronRatio, sqrtTwo] using hadd)

/-- Pointwise strict-buffer upper bracket on the Gaussian ratio. -/
theorem ratio_approx_le_nineFiftieths (n : Nat) :
    gaussianPerronRatio.approx n ≤ nineFiftieths := by
  have hroot := rootLower_le_sqrtTwo_approx n
  have hmul :
      (2 : Q') * rootLower ≤ (2 : Q') * sqrtTwo.approx n :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hroot (by decide)
  have hneg :
      -((2 : Q') * sqrtTwo.approx n) ≤ -((2 : Q') * rootLower) :=
    Q'.neg_le_neg hmul
  have hadd :
      (3 : Q') + -((2 : Q') * sqrtTwo.approx n)
        ≤ (3 : Q') + -((2 : Q') * rootLower) :=
    Q'.add_le_add_left 3 _ _ hneg
  exact Q'.le_trans' _ _ _
    (by simpa [gaussianPerronRatio, sqrtTwo] using hadd)
    (by decide)

/-- The exact Gaussian Perron ratio is constructively strictly positive. -/
theorem gaussianPerronRatio_pos :
    CReal.IsPositive gaussianPerronRatio :=
  CReal.isPositive_of_approx_ge (by decide)
    oneTwentieth_le_ratio_approx

/-- The exact Gaussian Perron ratio is bounded by `9/50`. -/
theorem gaussianPerronRatio_le_nineFiftieths :
    gaussianPerronRatio ≤ CReal.ofQ' nineFiftieths :=
  CReal.le_ofQ'_of_approx_le ratio_approx_le_nineFiftieths

/-- The rational buffer is strictly below the target quarter-independent
bound `1/5`. -/
theorem nineFiftieths_lt_oneFifth :
    nineFiftieths < oneFifth := by decide

/-- The exact distance from the proved `9/50` upper bracket to `1/4` is
`7/100`.  This is the perturbative room available to the nonlinear
Hilbert--Schmidt comparison. -/
theorem nineFiftieths_add_buffer_eqv_quarter :
    Q'.eqv (nineFiftieths + sevenHundredths) oneQuarter := by decide

/-- Every constructive approximation to the Gaussian ratio retains the
full `7/100` buffer below `1/4`. -/
theorem ratio_approx_add_buffer_le_quarter (n : Nat) :
    gaussianPerronRatio.approx n + sevenHundredths ≤ oneQuarter := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right
      (gaussianPerronRatio.approx n) nineFiftieths
      sevenHundredths
      (ratio_approx_le_nineFiftieths n))
    (Q'.le_of_eqv nineFiftieths_add_buffer_eqv_quarter)

/-- **Quantitative nonlinear handoff.**  Any rational spectral ratio known
to lie within the explicit `7/100` upper buffer of one Gaussian
approximation is already at most `1/4`.  The missing BF4 analytic theorem
must supply the premise from the normalized operator perturbation. -/
theorem perturbed_ratio_le_quarter
    {q : Q'} (n : Nat)
    (hpert :
      q ≤ gaussianPerronRatio.approx n + sevenHundredths) :
    q ≤ oneQuarter :=
  Q'.le_trans' _ _ _ hpert (ratio_approx_add_buffer_le_quarter n)

end YMGap.Continuum.BF4GaussianPerronRatio

#print axioms YMGap.Continuum.BF4GaussianPerronRatio.sqrtTwo_equiv_sqrtFrom
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.sqrtTwo_sq_equiv_two
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.rootLower_le_sqrtTwo_approx
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.sqrtTwo_approx_le_rootUpper
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.gaussianPerronRatio_pos
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.gaussianPerronRatio_le_nineFiftieths
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.nineFiftieths_lt_oneFifth
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.ratio_approx_add_buffer_le_quarter
#print axioms YMGap.Continuum.BF4GaussianPerronRatio.perturbed_ratio_le_quarter

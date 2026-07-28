/-
# A scalar Hilbert--Schmidt norm does not determine a Perron ratio

The cutoff-free nonlinear completion
`SU2NonlinearFiveFusionCompletion.nonlinearFiveHaarL2SqLimit` is a genuine
constructive scalar, but it has no source/target indices.  This module gives
an exact finite fence against using equality or convergence of that one
scalar as if it determined a transfer-operator ratio.

Two strictly positive two-state stochastic kernels are constructed:

    A = [[4/5, 1/5], [9/10, 1/10]],
    B = [[1/5, 4/5], [9/10, 1/10]].

They have the same entrywise Hilbert--Schmidt square `3/2`.  For a two-state
row-stochastic kernel the nonconstant eigenvalue is the difference of the
first-column entries, so the absolute ratios are respectively `1/10` and
`7/10`.  The first is below `1/4` and the second is above `1/4`.

Thus even strict positivity, row normalization, and an exact scalar
Hilbert--Schmidt norm leave the quarter-ratio question underdetermined.  A
proof of the BF4 nonlinear ratio must retain the actual source/target
operator (or an equivalent complete Gram/Choi carrier).

## Constructivity

The argument uses closed exact rational computation only; every theorem is
checked below with its exact dependency footprint.
-/

import YMGap.Continuum.BF4GaussianPerronRatio

namespace YMGap.Continuum.ScalarHilbertSchmidtPerronFence

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

def fourFifths : Q' := Q'.mkPos 4 5 (by decide)
def oneFifth : Q' := Q'.mkPos 1 5 (by decide)
def nineTenths : Q' := Q'.mkPos 9 10 (by decide)
def oneTenth : Q' := Q'.mkPos 1 10 (by decide)
def sevenTenths : Q' := Q'.mkPos 7 10 (by decide)
def threeHalves : Q' := Q'.mkPos 3 2 (by decide)

/-- The first strictly positive stochastic kernel. -/
def firstKernel : Bool → Bool → Q'
  | false, false => fourFifths
  | false, true => oneFifth
  | true, false => nineTenths
  | true, true => oneTenth

/-- The second strictly positive stochastic kernel.  It changes only the
orientation of the first row on the same Hilbert--Schmidt sphere. -/
def secondKernel : Bool → Bool → Q'
  | false, false => oneFifth
  | false, true => fourFifths
  | true, false => nineTenths
  | true, true => oneTenth

/-- Entrywise Hilbert--Schmidt square of a two-by-two rational kernel. -/
def boolKernelHSSq (kernel : Bool → Bool → Q') : Q' :=
  kernel false false * kernel false false +
    kernel false true * kernel false true +
    kernel true false * kernel true false +
    kernel true true * kernel true true

/-- The absolute nonconstant eigenvalue of a two-state row-stochastic
kernel, written directly in terms of its first column. -/
def boolStochasticNonvacuumRatio
    (kernel : Bool → Bool → Q') : Q' :=
  Q'.abs (kernel false false + -(kernel true false))

/-- Every entry of the first kernel is strictly positive. -/
theorem firstKernel_positive (source target : Bool) :
    (0 : Q') < firstKernel source target := by
  cases source <;> cases target <;> decide

/-- Every entry of the second kernel is strictly positive. -/
theorem secondKernel_positive (source target : Bool) :
    (0 : Q') < secondKernel source target := by
  cases source <;> cases target <;> decide

/-- Every row of the first kernel has unit mass. -/
theorem firstKernel_row_normalized (source : Bool) :
    firstKernel source false + firstKernel source true ≈ 1 := by
  cases source <;> decide

/-- Every row of the second kernel has unit mass. -/
theorem secondKernel_row_normalized (source : Bool) :
    secondKernel source false + secondKernel source true ≈ 1 := by
  cases source <;> decide

/-- Both strictly positive stochastic kernels have Hilbert--Schmidt square
exactly `3/2`. -/
theorem kernels_same_hilbertSchmidt_square :
    boolKernelHSSq firstKernel ≈ threeHalves ∧
      boolKernelHSSq secondKernel ≈ threeHalves := by
  decide

/-- The first kernel's nonconstant ratio is exactly `1/10`. -/
theorem firstKernel_ratio :
    boolStochasticNonvacuumRatio firstKernel ≈ oneTenth := by
  decide

/-- The second kernel's nonconstant ratio is exactly `7/10`. -/
theorem secondKernel_ratio :
    boolStochasticNonvacuumRatio secondKernel ≈ sevenTenths := by
  decide

/-- The first ratio lies safely below the target quarter. -/
theorem firstKernel_ratio_le_quarter :
    boolStochasticNonvacuumRatio firstKernel ≤
      BF4GaussianPerronRatio.oneQuarter := by
  decide

/-- The second ratio is strictly above the target quarter. -/
theorem quarter_lt_secondKernel_ratio :
    BF4GaussianPerronRatio.oneQuarter <
      boolStochasticNonvacuumRatio secondKernel := by
  decide

/-- **Hilbert--Schmidt/Perron underdetermination fence.**  Strict positivity,
row normalization, and equality of the scalar Hilbert--Schmidt square do not
determine on which side of `1/4` the nonconstant transfer ratio lies. -/
theorem same_hilbertSchmidt_square_opposite_quarter_sides :
    (∀ source target, (0 : Q') < firstKernel source target) ∧
    (∀ source target, (0 : Q') < secondKernel source target) ∧
    (∀ source,
      firstKernel source false + firstKernel source true ≈ 1) ∧
    (∀ source,
      secondKernel source false + secondKernel source true ≈ 1) ∧
    boolKernelHSSq firstKernel ≈ boolKernelHSSq secondKernel ∧
    boolStochasticNonvacuumRatio firstKernel ≤
      BF4GaussianPerronRatio.oneQuarter ∧
    BF4GaussianPerronRatio.oneQuarter <
      boolStochasticNonvacuumRatio secondKernel := by
  refine
    ⟨firstKernel_positive,
      secondKernel_positive,
      firstKernel_row_normalized,
      secondKernel_row_normalized,
      ?_, firstKernel_ratio_le_quarter,
      quarter_lt_secondKernel_ratio⟩
  exact Q'.eqv_trans _ threeHalves _
    kernels_same_hilbertSchmidt_square.1
    (Q'.eqv_symm kernels_same_hilbertSchmidt_square.2)

end YMGap.Continuum.ScalarHilbertSchmidtPerronFence

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.firstKernel_positive
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.secondKernel_positive
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.firstKernel_row_normalized
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.secondKernel_row_normalized
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.kernels_same_hilbertSchmidt_square
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.firstKernel_ratio
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.secondKernel_ratio
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.firstKernel_ratio_le_quarter
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.quarter_lt_secondKernel_ratio
#print axioms YMGap.Continuum.ScalarHilbertSchmidtPerronFence.same_hilbertSchmidt_square_opposite_quarter_sides

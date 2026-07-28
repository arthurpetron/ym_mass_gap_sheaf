/-
# Dimension-free finite-carrier Hilbert--Schmidt Perron perturbation

The five BF4 holonomies are configuration coordinates, not five basis
vectors of the transfer-operator Hilbert space.  After a character cutoff,
the normalized transfer operator acts on a finite function-space carrier
whose dimension grows with the cutoff.  Therefore a valid
Hilbert--Schmidt-to-Perron argument must be uniform in an arbitrary carrier
size `N`.

This module proves the required finite algebra.  For a rational matrix `E`
and vector `v`,

    |<v,E v>| <= epsilon <v,v>

follows from the dimension-free Hilbert--Schmidt condition

    ||E||_HS^2 <= epsilon^2.

The proof applies rational Cauchy--Schwarz first to every row and then to the
outer row sum.  No square root is introduced.  If a reference operator has
Rayleigh absolute value at most `g <v,v>`, a nonlinear operator differs from
it by such an `E`, and `v` is a nonzero eigenmode of ratio `q`, then

    q <= g + epsilon.

Specializing `g` to a constructive approximation of the Gaussian BF4 ratio
and `epsilon` to `7/100` gives `q <= 1/4`.

Honest remaining input: this theorem requires the *actual normalized
source/target matrix* on one common finite carrier and an HS comparison of
that matrix with the Gaussian Mehler operator on the same carrier.  A scalar
Haar square of a fifth-power class polynomial is not such a matrix.

## Constructivity

The proof uses finite exact `Q'` sums only; every theorem is checked below
with its exact dependency footprint.
-/

import YMGap.Continuum.BF4GaussianPerronRatio
import YMGap.Continuum.BakryEmery
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Continuum.ThetaExponentConvexity

namespace YMGap.Continuum.FiniteCarrierHSPerronPerturbation

open YMGap.Constructive
open YMGap.Continuum.BF4GaussianPerronRatio
open YMGap.Continuum.BondMovingStep

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_mono_local
    {lower upper : Nat → Q'}
    (termwise : ∀ i, lower i ≤ upper i) :
    ∀ N, fsum lower N ≤ fsum upper N
  | 0 => Q'.le_refl' 0
  | N + 1 =>
      Q'.add_le_add
        (fsum_mono_local termwise N)
        (termwise N)

private theorem fsum_eqv_congr_local
    (left right : Nat → Q')
    (termwise : ∀ i, left i ≈ right i) :
    ∀ N, fsum left N ≈ fsum right N
  | 0 => Q'.eqv_refl 0
  | N + 1 =>
      Q'.add_eqv_congr'
        (fsum_eqv_congr_local left right termwise N)
        (termwise N)

private theorem mul_swap_four
    (a b c d : Q') :
    (a * b) * (c * d) ≈
      (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    ?_ (Q'.eqv_symm
      (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

/-! ## 1. Arbitrary finite matrix carrier -/

/-- Rational square matrices are totalized on `Nat`; only indices below the
displayed carrier size are used. -/
abbrev RationalMatrix := Nat → Nat → Q'

/-- Rational vectors on the same totalized carrier. -/
abbrev RationalVector := Nat → Q'

/-- Squared finite `l²` norm. -/
def vectorNormSq
    (vector : RationalVector) (N : Nat) : Q' :=
  fsum (fun i => vector i * vector i) N

/-- Application of one matrix row. -/
def rowApply
    (matrix : RationalMatrix)
    (vector : RationalVector)
    (N row : Nat) : Q' :=
  fsum (fun column =>
    matrix row column * vector column) N

/-- Squared Hilbert--Schmidt mass of one row. -/
def rowHSSq
    (matrix : RationalMatrix)
    (N row : Nat) : Q' :=
  fsum (fun column =>
    matrix row column * matrix row column) N

/-- Squared Hilbert--Schmidt norm on the `N × N` carrier. -/
def matrixHSSq
    (matrix : RationalMatrix) (N : Nat) : Q' :=
  fsum (fun row => rowHSSq matrix N row) N

/-- Sum of squared row actions. -/
def rowActionSqSum
    (matrix : RationalMatrix)
    (vector : RationalVector)
    (N : Nat) : Q' :=
  fsum (fun row =>
    rowApply matrix vector N row *
      rowApply matrix vector N row) N

/-- The finite quadratic matrix coefficient `<v,Tv>`. -/
def matrixQuadratic
    (matrix : RationalMatrix)
    (vector : RationalVector)
    (N : Nat) : Q' :=
  fsum (fun row =>
    vector row * rowApply matrix vector N row) N

/-- Entrywise matrix difference. -/
def matrixDifference
    (nonlinear gaussian : RationalMatrix) :
    RationalMatrix :=
  fun row column =>
    nonlinear row column + (-(gaussian row column))

theorem vectorNormSq_nonnegative
    (vector : RationalVector) (N : Nat) :
    (0 : Q') ≤ vectorNormSq vector N := by
  unfold vectorNormSq
  exact fsum_nonneg
    (fun i =>
      SumOfSquares.q_mul_self_nonneg (vector i)) N

theorem rowHSSq_nonnegative
    (matrix : RationalMatrix) (N row : Nat) :
    (0 : Q') ≤ rowHSSq matrix N row := by
  unfold rowHSSq
  exact fsum_nonneg
    (fun column =>
      SumOfSquares.q_mul_self_nonneg
        (matrix row column)) N

theorem matrixHSSq_nonnegative
    (matrix : RationalMatrix) (N : Nat) :
    (0 : Q') ≤ matrixHSSq matrix N := by
  unfold matrixHSSq
  exact fsum_nonneg
    (fun row => rowHSSq_nonnegative matrix N row) N

theorem rowActionSqSum_nonnegative
    (matrix : RationalMatrix)
    (vector : RationalVector) (N : Nat) :
    (0 : Q') ≤ rowActionSqSum matrix vector N := by
  unfold rowActionSqSum
  exact fsum_nonneg
    (fun row =>
      SumOfSquares.q_mul_self_nonneg
        (rowApply matrix vector N row)) N

/-! ## 2. Dimension-free Hilbert--Schmidt quadratic bound -/

/-- Cauchy--Schwarz on one arbitrary finite row. -/
theorem rowApply_sq_le
    (matrix : RationalMatrix)
    (vector : RationalVector)
    (N row : Nat) :
    rowApply matrix vector N row *
        rowApply matrix vector N row ≤
      rowHSSq matrix N row *
        vectorNormSq vector N := by
  exact ThetaExponentConvexity.cauchy_schwarz
    (matrix row) vector N

/-- Sum the rowwise Cauchy--Schwarz inequalities. -/
theorem rowActionSqSum_le
    (matrix : RationalMatrix)
    (vector : RationalVector)
    (N : Nat) :
    rowActionSqSum matrix vector N ≤
      matrixHSSq matrix N *
        vectorNormSq vector N := by
  have hsum :
      rowActionSqSum matrix vector N ≤
        fsum
          (fun row =>
            rowHSSq matrix N row *
              vectorNormSq vector N)
          N := by
    unfold rowActionSqSum
    exact fsum_mono_local
      (fun row =>
        rowApply_sq_le matrix vector N row) N
  have hpull :
      fsum
          (fun row =>
            rowHSSq matrix N row *
              vectorNormSq vector N)
          N ≈
        matrixHSSq matrix N *
          vectorNormSq vector N := by
    exact Q'.eqv_symm
      (CubeRatioBounds.fsum_mul_const
        (fun row => rowHSSq matrix N row)
        (vectorNormSq vector N) N)
  exact Q'.le_trans' _ _ _
    hsum (Q'.le_of_eqv hpull)

/-- **Dimension-free finite Hilbert--Schmidt quadratic estimate.**

`<v,E v>² <= ||E||_HS² <v,v>²` for every carrier size `N`. -/
theorem matrixQuadratic_sq_le
    (matrix : RationalMatrix)
    (vector : RationalVector)
    (N : Nat) :
    matrixQuadratic matrix vector N *
        matrixQuadratic matrix vector N ≤
      matrixHSSq matrix N *
        (vectorNormSq vector N *
          vectorNormSq vector N) := by
  have houter :=
    ThetaExponentConvexity.cauchy_schwarz
      vector
      (fun row => rowApply matrix vector N row)
      N
  have hscaled :
      vectorNormSq vector N *
          rowActionSqSum matrix vector N ≤
        vectorNormSq vector N *
          (matrixHSSq matrix N *
            vectorNormSq vector N) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (rowActionSqSum_le matrix vector N)
      (vectorNormSq_nonnegative vector N)
  have hreindex :
      vectorNormSq vector N *
          (matrixHSSq matrix N *
            vectorNormSq vector N) ≈
        matrixHSSq matrix N *
          (vectorNormSq vector N *
            vectorNormSq vector N) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (vectorNormSq vector N)
          (matrixHSSq matrix N)
          (vectorNormSq vector N))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (vectorNormSq vector N *
          matrixHSSq matrix N)
        (matrixHSSq matrix N *
          vectorNormSq vector N)
        (vectorNormSq vector N)
        (Q'.mul_comm_eqv
          (vectorNormSq vector N)
          (matrixHSSq matrix N))) ?_
    exact Q'.mul_assoc_eqv
      (matrixHSSq matrix N)
      (vectorNormSq vector N)
      (vectorNormSq vector N)
  exact Q'.le_trans' _ _ _ houter
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv hreindex))

/-- A rational HS error budget gives the linear Rayleigh error without a
dimension factor and without taking a square root. -/
theorem abs_matrixQuadratic_le_of_hs
    {matrix : RationalMatrix}
    {vector : RationalVector}
    {N : Nat} {epsilon : Q'}
    (epsilon_pos : (0 : Q') < epsilon)
    (vectorNorm_pos :
      (0 : Q') < vectorNormSq vector N)
    (hs_bound :
      matrixHSSq matrix N ≤ epsilon * epsilon) :
    Q'.abs (matrixQuadratic matrix vector N) ≤
      epsilon * vectorNormSq vector N := by
  let norm := vectorNormSq vector N
  have hnormSq_nonnegative :
      (0 : Q') ≤ norm * norm :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt vectorNorm_pos)
      (Q'.le_of_lt vectorNorm_pos)
  have hscaled :
      matrixHSSq matrix N * (norm * norm) ≤
        (epsilon * epsilon) * (norm * norm) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hs_bound hnormSq_nonnegative
  have hreindex :
      (epsilon * epsilon) * (norm * norm) ≈
        (epsilon * norm) * (epsilon * norm) :=
    mul_swap_four epsilon epsilon norm norm
  have hsquare :
      matrixQuadratic matrix vector N *
          matrixQuadratic matrix vector N ≤
        (epsilon * norm) * (epsilon * norm) :=
    Q'.le_trans' _ _ _
      (matrixQuadratic_sq_le matrix vector N)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv hreindex))
  exact Q'.abs_le_of_sq_le_sq
    (Q'.mul_pos epsilon_pos vectorNorm_pos)
    hsquare

/-! ## 3. Exact matrix difference algebra -/

/-- Matrix application splits into reference plus entrywise error. -/
theorem rowApply_difference
    (nonlinear gaussian : RationalMatrix)
    (vector : RationalVector)
    (N row : Nat) :
    rowApply nonlinear vector N row ≈
      rowApply gaussian vector N row +
        rowApply
          (matrixDifference nonlinear gaussian)
          vector N row := by
  unfold rowApply matrixDifference
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr_local
      (fun column =>
        nonlinear row column * vector column)
      (fun column =>
        gaussian row column * vector column +
          (nonlinear row column +
            (-gaussian row column)) * vector column)
      (fun column => by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (nonlinear row column)
            (gaussian row column +
              (nonlinear row column +
                (-gaussian row column)))
            (vector column)
            (Q'.add_sub_cancel_eqv
              (nonlinear row column)
              (gaussian row column))) ?_
        exact Q'.add_mul_eqv
          (gaussian row column)
          (nonlinear row column +
            (-gaussian row column))
          (vector column))
      N) ?_
  exact CubeRatioBounds.fsum_add
    (fun column =>
      gaussian row column * vector column)
    (fun column =>
      (nonlinear row column +
        (-gaussian row column)) * vector column)
    N

/-- The nonlinear quadratic is exactly reference quadratic plus error
quadratic. -/
theorem matrixQuadratic_difference
    (nonlinear gaussian : RationalMatrix)
    (vector : RationalVector)
    (N : Nat) :
    matrixQuadratic nonlinear vector N ≈
      matrixQuadratic gaussian vector N +
        matrixQuadratic
          (matrixDifference nonlinear gaussian)
          vector N := by
  unfold matrixQuadratic
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr_local
      (fun row =>
        vector row *
          rowApply nonlinear vector N row)
      (fun row =>
        vector row *
            rowApply gaussian vector N row +
          vector row *
            rowApply
              (matrixDifference nonlinear gaussian)
              vector N row)
      (fun row =>
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (vector row)
            (rowApply nonlinear vector N row)
            (rowApply gaussian vector N row +
              rowApply
                (matrixDifference nonlinear gaussian)
                vector N row)
            (rowApply_difference
              nonlinear gaussian vector N row))
          (Q'.mul_add_eqv
            (vector row)
            (rowApply gaussian vector N row)
            (rowApply
              (matrixDifference nonlinear gaussian)
              vector N row)))
      N) ?_
  exact CubeRatioBounds.fsum_add
    (fun row =>
      vector row * rowApply gaussian vector N row)
    (fun row =>
      vector row *
        rowApply
          (matrixDifference nonlinear gaussian)
          vector N row)
    N

/-! ## 4. Same-carrier nonlinear eigenmodes -/

/-- A genuine nonzero eigenmode of a finite source/target operator.  The
entrywise eigen-equation, rather than a freely supplied Rayleigh quotient,
is retained. -/
structure FiniteCarrierEigenmode
    (matrix : RationalMatrix) (N : Nat) : Type where
  ratio : Q'
  vector : RationalVector
  ratio_nonnegative : (0 : Q') ≤ ratio
  vectorNorm_pos :
    (0 : Q') < vectorNormSq vector N
  eigen_equation :
    ∀ row, row < N →
      rowApply matrix vector N row ≈
        ratio * vector row

namespace FiniteCarrierEigenmode

variable {matrix : RationalMatrix} {N : Nat}
    (mode : FiniteCarrierEigenmode matrix N)

/-- The entrywise eigen-equation gives the exact quadratic eigenvalue
identity. -/
theorem quadratic_eigen :
    matrixQuadratic matrix mode.vector N ≈
      mode.ratio * vectorNormSq mode.vector N := by
  unfold matrixQuadratic vectorNormSq
  refine Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_eqv_congr_lt
      (fun row =>
        mode.vector row *
          rowApply matrix mode.vector N row)
      (fun row =>
        (mode.vector row * mode.vector row) *
          mode.ratio)
      N
      (fun row hrow => by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (mode.vector row)
            (rowApply matrix mode.vector N row)
            (mode.ratio * mode.vector row)
            (mode.eigen_equation row hrow)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (mode.vector row)
              mode.ratio (mode.vector row))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (mode.vector row * mode.ratio)
            (mode.ratio * mode.vector row)
            (mode.vector row)
            (Q'.mul_comm_eqv
              (mode.vector row) mode.ratio)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv
            mode.ratio (mode.vector row)
            (mode.vector row)) ?_
        exact Q'.mul_comm_eqv
          mode.ratio
          (mode.vector row * mode.vector row))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (CubeRatioBounds.fsum_mul_const
        (fun row =>
          mode.vector row * mode.vector row)
        mode.ratio N)) ?_
  exact Q'.mul_comm_eqv
    (fsum
      (fun row =>
        mode.vector row * mode.vector row) N)
    mode.ratio

end FiniteCarrierEigenmode

/-! ## 5. Dimension-free Perron perturbation -/

/-- Same-carrier finite HS perturbation data.  The carrier size is arbitrary
and may grow with the representation cutoff. -/
structure FiniteCarrierHSPerturbation
    (nonlinear gaussian : RationalMatrix)
    (N : Nat) (gaussianRate epsilon : Q') : Type where
  gaussianRate_nonnegative :
    (0 : Q') ≤ gaussianRate
  epsilon_pos : (0 : Q') < epsilon
  gaussian_quadratic :
    ∀ vector,
      Q'.abs
          (matrixQuadratic gaussian vector N) ≤
        gaussianRate * vectorNormSq vector N
  nonlinear_gaussian_hs :
    matrixHSSq
        (matrixDifference nonlinear gaussian) N ≤
      epsilon * epsilon

namespace FiniteCarrierHSPerturbation

variable
    {nonlinear gaussian : RationalMatrix}
    {N : Nat} {gaussianRate epsilon : Q'}
    (perturbation :
      FiniteCarrierHSPerturbation
        nonlinear gaussian N gaussianRate epsilon)

include perturbation

/-- The nonlinear quadratic form itself has the uniform rate
`gaussianRate + epsilon` on every nonzero vector.  This is stronger than
bounding one selected eigenmode. -/
theorem nonlinear_quadratic_abs_le
    (vector : RationalVector)
    (vectorNorm_pos :
      (0 : Q') < vectorNormSq vector N) :
    Q'.abs
        (matrixQuadratic nonlinear vector N) ≤
      (gaussianRate + epsilon) *
        vectorNormSq vector N := by
  let norm := vectorNormSq vector N
  let error := matrixDifference nonlinear gaussian
  have herror :
      Q'.abs
          (matrixQuadratic error vector N) ≤
        epsilon * norm :=
    abs_matrixQuadratic_le_of_hs
      perturbation.epsilon_pos
      vectorNorm_pos
      perturbation.nonlinear_gaussian_hs
  have hsplit :
      Q'.abs
          (matrixQuadratic nonlinear vector N) ≤
        Q'.abs
            (matrixQuadratic gaussian vector N) +
          Q'.abs
            (matrixQuadratic error vector N) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (matrixQuadratic_difference
            nonlinear gaussian vector N)))
      (Q'.abs_add_le'
        (matrixQuadratic gaussian vector N)
        (matrixQuadratic error vector N))
  refine Q'.le_trans' _ _ _ hsplit
    (Q'.le_trans' _ _ _
      (Q'.add_le_add
        (perturbation.gaussian_quadratic vector)
        herror) ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.add_mul_eqv
        gaussianRate epsilon norm))

/-- Every nonnegative eigenmode ratio of the nonlinear operator is bounded
by the reference rate plus the HS error, uniformly in carrier dimension. -/
theorem eigenmode_ratio_le
    (mode : FiniteCarrierEigenmode nonlinear N) :
    mode.ratio ≤ gaussianRate + epsilon := by
  let norm := vectorNormSq mode.vector N
  have hupper :
      Q'.abs
          (matrixQuadratic nonlinear mode.vector N) ≤
        (gaussianRate + epsilon) * norm := by
    exact perturbation.nonlinear_quadratic_abs_le
      mode.vector mode.vectorNorm_pos
  have hmodeToAbs :
      mode.ratio * norm ≤
        Q'.abs
          (matrixQuadratic nonlinear mode.vector N) := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv mode.quadratic_eigen)
      (Q'.le_abs_self
        (matrixQuadratic nonlinear mode.vector N))
  have hscaled :
      mode.ratio * norm ≤
        (gaussianRate + epsilon) * norm :=
    Q'.le_trans' _ _ _ hmodeToAbs hupper
  exact BakryEmery.le_of_mul_le_mul_right_pos
    mode.vectorNorm_pos hscaled

end FiniteCarrierHSPerturbation

/-! ## 6. Exact BF4 Gaussian buffer -/

/-- Specialize the arbitrary finite carrier to the exact BF4 Gaussian
approximation and `7/100` HS budget. -/
abbrev BF4BufferedFiniteCarrierHSPerturbation
    (nonlinear gaussian : RationalMatrix)
    (N approximation : Nat) : Type :=
  FiniteCarrierHSPerturbation
    nonlinear gaussian N
    (gaussianPerronRatio.approx approximation)
    sevenHundredths

/-- **Dimension-free BF4 nonlinear quarter theorem.**  On any common finite
function-space carrier, the exact `7/100` HS comparison with the Gaussian
reference forces every nonnegative nonlinear eigenmode ratio below
`1/4`. -/
theorem bf4_nonlinear_eigenmode_ratio_le_quarter
    {nonlinear gaussian : RationalMatrix}
    {N approximation : Nat}
    (perturbation :
      BF4BufferedFiniteCarrierHSPerturbation
        nonlinear gaussian N approximation)
    (mode : FiniteCarrierEigenmode nonlinear N) :
    mode.ratio ≤ oneQuarter := by
  exact Q'.le_trans' _ _ _
    (perturbation.eigenmode_ratio_le mode)
    (ratio_approx_add_buffer_le_quarter approximation)

/-- The exact BF4 buffer gives a global quarter Rayleigh bound on every
nonzero vector of the arbitrary finite function-space carrier. -/
theorem bf4_nonlinear_quadratic_abs_le_quarter
    {nonlinear gaussian : RationalMatrix}
    {N approximation : Nat}
    (perturbation :
      BF4BufferedFiniteCarrierHSPerturbation
        nonlinear gaussian N approximation)
    (vector : RationalVector)
    (vectorNorm_pos :
      (0 : Q') < vectorNormSq vector N) :
    Q'.abs
        (matrixQuadratic nonlinear vector N) ≤
      oneQuarter * vectorNormSq vector N := by
  exact Q'.le_trans' _ _ _
    (perturbation.nonlinear_quadratic_abs_le
      vector vectorNorm_pos)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (ratio_approx_add_buffer_le_quarter approximation)
      (Q'.le_of_lt vectorNorm_pos))

end YMGap.Continuum.FiniteCarrierHSPerronPerturbation

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.rowApply_sq_le
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.rowActionSqSum_le
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.matrixQuadratic_sq_le
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.abs_matrixQuadratic_le_of_hs
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.rowApply_difference
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.matrixQuadratic_difference
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.FiniteCarrierEigenmode.quadratic_eigen
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.FiniteCarrierHSPerturbation.nonlinear_quadratic_abs_le
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.FiniteCarrierHSPerturbation.eigenmode_ratio_le
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.bf4_nonlinear_eigenmode_ratio_le_quarter
#print axioms YMGap.Continuum.FiniteCarrierHSPerronPerturbation.bf4_nonlinear_quadratic_abs_le_quarter

/-
# Exact BF4 five-holonomy Gaussian transfer algebra

The nonlinear BF4 boundary transfer reduces, at its flat-orbit quadratic
limit, to five transmitted holonomy coordinates.  This module ports the exact
integer/rational algebra of that reduction into the constructive Lean
substrate.

It proves:

* the spatial precision `S`;
* the temporal quotient precision `K`, represented without division by
  `K24 = 24 K`;
* the exact generalized operator `A = K⁻¹S`, certified division-free by
  `K24 A = 24 S`;
* the minimal-polynomial identity `(A - 4I)(A - 6I) = 0`;
* three explicit eigenvectors at eigenvalue four and two at eigenvalue six.

These are necessary finite-dimensional inputs to the nonlinear
Hilbert--Schmidt limit.  This file does not assert that nonlinear limit: the
Haar/Peter--Weyl `L²` convergence and its cutoff modulus are separate analytic
obligations.

All entries and contractions are exact `Q'` computations.  No numerical
approximation, classical choice, `native_decide`, or unproved analytic input
is used.
-/

import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.BF4FiveHolonomyGaussian

open YMGap.Constructive
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

/-- A finite five-coordinate rational matrix, represented on `Fin 5`. -/
abbrev Matrix5 := Fin 5 → Fin 5 → Q'

/-- A five-coordinate rational column vector. -/
abbrev Vector5 := Fin 5 → Q'

private def row0 : Fin 5 := ⟨0, by decide⟩
private def row1 : Fin 5 := ⟨1, by decide⟩
private def row2 : Fin 5 := ⟨2, by decide⟩
private def row3 : Fin 5 := ⟨3, by decide⟩
private def row4 : Fin 5 := ⟨4, by decide⟩

/-- The ordered list of all five contraction indices. -/
def indices : List (Fin 5) := [row0, row1, row2, row3, row4]

/-- Exact finite sum over the five transmitted coordinates. -/
def sum5 (f : Fin 5 → Q') : Q' :=
  indices.foldl (fun total i => total + f i) 0

/-- Five-by-five matrix multiplication in the exact rational setoid. -/
def matMul (A B : Matrix5) : Matrix5 :=
  fun r c => sum5 (fun k => A r k * B k c)

/-- Matrix-vector multiplication. -/
def matVec (A : Matrix5) (v : Vector5) : Vector5 :=
  fun r => sum5 (fun k => A r k * v k)

/-- Scalar diagonal matrix. -/
def scalarMatrix (q : Q') : Matrix5 :=
  fun r c => if r = c then q else 0

/-- Entrywise matrix subtraction. -/
def matSub (A B : Matrix5) : Matrix5 :=
  fun r c => A r c - B r c

/-- Entrywise semantic equivalence of matrices. -/
def MatrixEqv (A B : Matrix5) : Prop :=
  ∀ r c, A r c ≈ B r c

/-- Entrywise semantic equivalence of vectors. -/
def VectorEqv (u v : Vector5) : Prop :=
  ∀ r, u r ≈ v r

/-- Convert an integer table into a rational matrix.  The table is total:
out-of-range accesses are zero, although all uses below are on `Fin 5`. -/
def integerMatrix (rows : List (List Int)) : Matrix5 :=
  fun r c => Q'.ofInt ((rows.getD r.val []).getD c.val 0)

/-- The exact spatial Schur precision matrix `S`. -/
def spatialS : Matrix5 :=
  integerMatrix
    [[2, 0, 0, 0, -1],
     [0, 2, -1, -1, 1],
     [0, -1, 2, 1, -1],
     [0, -1, 1, 2, -1],
     [-1, 1, -1, -1, 2]]

/-- The exact temporal quotient precision, scaled integrally as `K24 = 24 K`. -/
def kineticK24 : Matrix5 :=
  integerMatrix
    [[10, 1, -2, -1, -4],
     [1, 10, -5, -4, 5],
     [-2, -5, 10, 5, -4],
     [-1, -4, 5, 10, -5],
     [-4, 5, -4, -5, 10]]

/-- The exact generalized operator `A = K⁻¹S`. -/
def generalizedA : Matrix5 :=
  integerMatrix
    [[5, -1, 1, 1, -1],
     [0, 5, 0, -1, 0],
     [1, 0, 5, 0, -1],
     [0, -1, 0, 5, 0],
     [0, -1, 0, 1, 4]]

/-- Eigenbasis matrix with columns `(eig4a,eig4b,eig4c,eig6a,eig6b)`. -/
def eigenbasisP : Matrix5 :=
  integerMatrix
    [[-1, 0, 1, 1, 1],
     [0, 1, 0, 0, -1],
     [1, 0, 0, 1, 0],
     [0, 1, 0, 0, 1],
     [0, 0, 1, 0, 1]]

/-- Twice the inverse eigenbasis.  Keeping the factor two outside makes the
invertibility certificate division-free. -/
def eigenbasisInverse2 : Matrix5 :=
  integerMatrix
    [[-1, 0, 1, 0, 1],
     [0, 1, 0, 1, 0],
     [0, 1, 0, -1, 2],
     [1, 0, 1, 0, -1],
     [0, -1, 0, 1, 0]]

/-- Spectral diagonal with multiplicities `4×3` and `6×2`. -/
def spectralDiagonal : Matrix5 :=
  integerMatrix
    [[4, 0, 0, 0, 0],
     [0, 4, 0, 0, 0],
     [0, 0, 4, 0, 0],
     [0, 0, 0, 6, 0],
     [0, 0, 0, 0, 6]]

/-- The spatial matrix multiplied by 24, used in the division-free
generalized-eigenvalue certificate. -/
def spatialS24 : Matrix5 :=
  fun r c => Q'.ofNat 24 * spatialS r c

/-- **Division-free identification of the generalized operator:**
`(24K) A = 24S`. -/
theorem kinetic_mul_generalized :
    MatrixEqv (matMul kineticK24 generalizedA) spatialS24 := by
  unfold MatrixEqv
  decide

/-- **Exact minimal polynomial:** `(A - 4I)(A - 6I) = 0`. -/
theorem generalized_minimal_polynomial :
    MatrixEqv
      (matMul
        (matSub generalizedA (scalarMatrix 4))
      (matSub generalizedA (scalarMatrix 6)))
      (scalarMatrix 0) := by
  unfold MatrixEqv
  decide

/-- The displayed five eigenvectors form a basis: `P·(2P⁻¹)=2I`. -/
theorem eigenbasis_right_inverse2 :
    MatrixEqv (matMul eigenbasisP eigenbasisInverse2) (scalarMatrix 2) := by
  unfold MatrixEqv
  decide

/-- The matching left-inverse identity `(2P⁻¹)·P=2I`. -/
theorem eigenbasis_left_inverse2 :
    MatrixEqv (matMul eigenbasisInverse2 eigenbasisP) (scalarMatrix 2) := by
  unfold MatrixEqv
  decide

/-- **Exact spectral decomposition:** `A P = P diag(4,4,4,6,6)`.  Together
with the two inverse identities this certifies the generalized spectrum and
its multiplicities without determinants, roots, or classical eigenvalue
selection. -/
theorem generalized_spectral_decomposition :
    MatrixEqv (matMul generalizedA eigenbasisP)
      (matMul eigenbasisP spectralDiagonal) := by
  unfold MatrixEqv
  decide

/-- First eigenvector at generalized eigenvalue four. -/
def eig4a : Vector5 :=
  fun i => integerMatrix [[-1], [0], [1], [0], [0]] i row0

/-- Second eigenvector at generalized eigenvalue four. -/
def eig4b : Vector5 :=
  fun i => integerMatrix [[0], [1], [0], [1], [0]] i row0

/-- Third eigenvector at generalized eigenvalue four. -/
def eig4c : Vector5 :=
  fun i => integerMatrix [[1], [0], [0], [0], [1]] i row0

/-- First eigenvector at generalized eigenvalue six. -/
def eig6a : Vector5 :=
  fun i => integerMatrix [[1], [0], [1], [0], [0]] i row0

/-- Second eigenvector at generalized eigenvalue six. -/
def eig6b : Vector5 :=
  fun i => integerMatrix [[1], [-1], [0], [1], [1]] i row0

/-- Scalar multiplication of a five-coordinate vector. -/
def vecScale (q : Q') (v : Vector5) : Vector5 :=
  fun i => q * v i

theorem eig4a_equation : VectorEqv (matVec generalizedA eig4a) (vecScale 4 eig4a) := by
  unfold VectorEqv
  decide

theorem eig4b_equation : VectorEqv (matVec generalizedA eig4b) (vecScale 4 eig4b) := by
  unfold VectorEqv
  decide

theorem eig4c_equation : VectorEqv (matVec generalizedA eig4c) (vecScale 4 eig4c) := by
  unfold VectorEqv
  decide

theorem eig6a_equation : VectorEqv (matVec generalizedA eig6a) (vecScale 6 eig6a) := by
  unfold VectorEqv
  decide

theorem eig6b_equation : VectorEqv (matVec generalizedA eig6b) (vecScale 6 eig6b) := by
  unfold VectorEqv
  decide

end YMGap.Continuum.BF4FiveHolonomyGaussian

#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.kinetic_mul_generalized
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.generalized_minimal_polynomial
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eigenbasis_right_inverse2
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eigenbasis_left_inverse2
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.generalized_spectral_decomposition
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eig4a_equation
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eig4b_equation
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eig4c_equation
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eig6a_equation
#print axioms YMGap.Continuum.BF4FiveHolonomyGaussian.eig6b_equation

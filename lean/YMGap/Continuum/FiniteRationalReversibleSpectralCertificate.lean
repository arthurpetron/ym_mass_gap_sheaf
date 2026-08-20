/-
# Constructive finite reversible spectral certificates

For a finite reversible kernel `K`, stationary weights `d`, and a rational
contraction candidate `q`, the rank-one-penalized quadratic is

  q * <x,x>_d - <x,Kx> + (<x,d>)^2.

If an exact finite matrix certificate proves this expression nonnegative, then
on the explicitly centered subspace `<x,d> = 0` it proves the raw contraction

  <x,Kx> <= q * <x,x>_d.

The theorem below is deliberately algebraic.  It does not identify an external
matrix table with a physical Yang--Mills kernel, and it makes no cutoff-uniform,
infinite-volume, continuum, or Clay claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalLDLCertificate

namespace YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- The exact weighted mean of a finite coefficient vector. -/
def finiteWeightedMean
    (n : Nat) (weight coefficient : Nat → Q') : Q' :=
  listQSum (fun i => coefficient i * weight i) (List.range n)

/-- The exact diagonal quadratic `sum_i d_i x_i^2`. -/
def finiteDiagonalQuadratic
    (n : Nat) (weight coefficient : Nat → Q') : Q' :=
  listQSum
    (fun i => (coefficient i * coefficient i) * weight i)
    (List.range n)

/-- The scalar quadratic represented by `q D - K + d d^T`. -/
def finitePenalizedReversibleQuadratic
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (coefficient : Nat → Q') : Q' :=
  q * finiteDiagonalQuadratic n weight coefficient +
      -(finiteMatrixQuadratic n kernel coefficient) +
    finiteWeightedMean n weight coefficient *
      finiteWeightedMean n weight coefficient

/-- On the weighted mean-zero subspace, the rank-one penalty vanishes exactly. -/
theorem finitePenalizedReversibleQuadratic_centered
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    {coefficient : Nat → Q'}
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finitePenalizedReversibleQuadratic n q weight kernel coefficient ≈
      q * finiteDiagonalQuadratic n weight coefficient +
        -(finiteMatrixQuadratic n kernel coefficient) := by
  have hsquare :
      finiteWeightedMean n weight coefficient *
          finiteWeightedMean n weight coefficient ≈ 0 := by
    refine Q'.eqv_trans _
      (0 * finiteWeightedMean n weight coefficient) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hcenter
    · exact Q'.zero_mul_eqv _
  unfold finitePenalizedReversibleQuadratic
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hsquare)
    (Q'.eqv_of_eq (Q'.add_zero' _))

/-- Nonnegativity of the penalized quadratic restricts to nonnegativity of
`q D - K` on a coefficient vector carrying an exact weighted-centering proof. -/
theorem finiteCenteredDifference_nonnegative_of_penalized
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    {coefficient : Nat → Q'}
    (hpenalized : (0 : Q') ≤
      finitePenalizedReversibleQuadratic n q weight kernel coefficient)
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    (0 : Q') ≤
      q * finiteDiagonalQuadratic n weight coefficient +
        -(finiteMatrixQuadratic n kernel coefficient) :=
  Q'.le_trans' _ _ _ hpenalized
    (Q'.le_of_eqv
      (finitePenalizedReversibleQuadratic_centered hcenter))

/-- Exact reversible contraction on the weighted mean-zero subspace. -/
theorem finiteReversibleContraction_of_penalized
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel : Nat → Nat → Q'}
    {coefficient : Nat → Q'}
    (hpenalized : (0 : Q') ≤
      finitePenalizedReversibleQuadratic n q weight kernel coefficient)
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteMatrixQuadratic n kernel coefficient ≤
      q * finiteDiagonalQuadratic n weight coefficient := by
  let diagonalValue := q * finiteDiagonalQuadratic n weight coefficient
  let kernelValue := finiteMatrixQuadratic n kernel coefficient
  have hnonnegative : (0 : Q') ≤ diagonalValue + -kernelValue :=
    finiteCenteredDifference_nonnegative_of_penalized hpenalized hcenter
  have hadd : (0 : Q') + kernelValue ≤
      (diagonalValue + -kernelValue) + kernelValue :=
    Q'.add_le_add_right _ _ kernelValue hnonnegative
  have hleft : (0 : Q') + kernelValue ≈ kernelValue :=
    Q'.eqv_of_eq (Q'.zero_add' kernelValue)
  have hright : (diagonalValue + -kernelValue) + kernelValue ≈
      diagonalValue := by
    refine Q'.eqv_trans _ (diagonalValue + (-kernelValue + kernelValue)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ (diagonalValue + 0) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv kernelValue)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' diagonalValue)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-- Composition point for an exact finite-matrix PSD certificate.  The producer
must separately identify its certified matrix quadratic with the penalized
reversible quadratic; this assumption is an equality obligation, not positivity
or a spectral assumption. -/
theorem finiteReversibleContraction_of_matrix_nonnegative
    {n : Nat} {q : Q'} {weight : Nat → Q'}
    {kernel certifiedMatrix : Nat → Nat → Q'}
    {coefficient : Nat → Q'}
    (hmatrix : (0 : Q') ≤
      finiteMatrixQuadratic n certifiedMatrix coefficient)
    (hidentify : finiteMatrixQuadratic n certifiedMatrix coefficient ≈
      finitePenalizedReversibleQuadratic n q weight kernel coefficient)
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteMatrixQuadratic n kernel coefficient ≤
      q * finiteDiagonalQuadratic n weight coefficient := by
  apply finiteReversibleContraction_of_penalized
  · exact Q'.le_trans' _ _ _ hmatrix (Q'.le_of_eqv hidentify)
  · exact hcenter

end YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

#print axioms
  YMGap.Continuum.FiniteRationalReversibleSpectralCertificate.finitePenalizedReversibleQuadratic_centered
#print axioms
  YMGap.Continuum.FiniteRationalReversibleSpectralCertificate.finiteReversibleContraction_of_penalized
#print axioms
  YMGap.Continuum.FiniteRationalReversibleSpectralCertificate.finiteReversibleContraction_of_matrix_nonnegative

/-
# Constructive Schur uniqueness for diagonal binary-form endomorphisms

Weight support reduces an endomorphism of one binary-form irreducible to a
diagonal coefficient sequence.  Commutation with the lowering operator then
forces adjacent diagonal coefficients to agree; positive rational
cancellation propagates one scalar across the entire representation.  This is
the constant-coefficient mechanism missing from shellwise Hahn inversion.
-/

import YMGap.Continuum.BinaryForms
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.SU2DiagonalSchurUniqueness

open YMGap.Constructive
open YMGap.Continuum.BinaryForms

local infix:50 " ≈ " => Q'.eqv

/-- The weight-diagonal linear endomorphism with coefficients `coeff`. -/
def diagonalMap (coeff : Nat → Q') (x : BForm) : BForm :=
  fun s => coeff s * x s

/-- Lowering covariance tested on the complete monomial basis. -/
def DiagonalLoweringCovariant (n : Nat) (coeff : Nat → Q') : Prop :=
  ∀ k, k < n + 1 →
    FormEqv (n + 1)
      (diagonalMap coeff (Fop n (mono k)))
      (Fop n (diagonalMap coeff (mono k)))

/-- Lowering covariance identifies every adjacent pair of diagonal entries. -/
theorem diagonal_coeff_adjacent (n : Nat) (coeff : Nat → Q')
    (hF : DiagonalLoweringCovariant n coeff) (s : Nat) (hs : s < n) :
    coeff (s + 1) ≈ coeff s := by
  have h := hF (s + 1) (by omega) s (by omega)
  let p := Q'.ofNat (s + 1)
  have h' : coeff s * (p * 1) ≈ p * (coeff (s + 1) * 1) := by
    simpa only [diagonalMap, Fop, mono, if_pos, p] using h
  have hscaled : p * coeff s ≈ p * coeff (s + 1) := by
    refine Q'.eqv_trans _ (coeff s * p) _ (Q'.mul_comm_eqv _ _) ?_
    refine Q'.eqv_trans _ (coeff s * (p * 1)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv p))) ?_
    refine Q'.eqv_trans _ (p * (coeff (s + 1) * 1)) _ h' ?_
    exact Q'.mul_eqv_congr_left p _ _ (Q'.mul_one_eqv _)
  simpa only [p] using Q'.eqv_symm
    (Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos s) hscaled)

/-- **Constructive diagonal Schur lemma.**  One coefficient determines the
entire weight-diagonal lowering intertwiner. -/
theorem diagonal_coeff_constant (n : Nat) (coeff : Nat → Q')
    (hF : DiagonalLoweringCovariant n coeff) :
    ∀ s, s < n + 1 → coeff s ≈ coeff 0 := by
  intro s hs
  induction s with
  | zero => exact Q'.eqv_refl _
  | succ s ih =>
      exact Q'.eqv_trans _ _ _
        (diagonal_coeff_adjacent n coeff hF s (by omega))
        (ih (by omega))

/-- Consequently the complete map is the scalar identity on the physical
window. -/
theorem diagonalMap_eq_scalar_identity (n : Nat) (coeff : Nat → Q')
    (hF : DiagonalLoweringCovariant n coeff) (x : BForm) :
    FormEqv (n + 1) (diagonalMap coeff x)
      (fun s => coeff 0 * x s) := by
  intro s hs
  exact Q'.mul_eqv_congr_right _ _ _
    (diagonal_coeff_constant n coeff hF s hs)

/-- The degree-dependent twist from the obstruction cannot commute with
lowering on degree one. -/
def twistCoeff (s : Nat) : Q' := if s = 0 then 1 else 2

theorem twistCoeff_not_lowering_covariant :
    ¬ DiagonalLoweringCovariant 1 twistCoeff := by
  intro hF
  have hconstant := diagonal_coeff_constant 1 twistCoeff hF 1 (by omega)
  have hfalse : (2 : Q') ≈ 1 := by
    simpa only [twistCoeff, if_neg (by omega : ¬ 1 = 0), if_pos] using hconstant
  have hne : ¬ ((2 : Q') ≈ 1) := by decide
  exact hne hfalse

end YMGap.Continuum.SU2DiagonalSchurUniqueness

#print axioms YMGap.Continuum.SU2DiagonalSchurUniqueness.diagonal_coeff_adjacent
#print axioms YMGap.Continuum.SU2DiagonalSchurUniqueness.diagonal_coeff_constant
#print axioms YMGap.Continuum.SU2DiagonalSchurUniqueness.diagonalMap_eq_scalar_identity
#print axioms YMGap.Continuum.SU2DiagonalSchurUniqueness.twistCoeff_not_lowering_covariant

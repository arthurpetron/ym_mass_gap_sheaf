/-
`QuadraticCutoffSchedule` — a coupled truncation schedule with an exact,
inverse-square-summable rational tail envelope.

This module is deliberately independent of the still-missing general spectral
tail theorem.  It supplies the arithmetic object that theorem can target.

We choose the slightly sharper quadratic cutoff

  Ncut(k) = (k + 2)^2

(rather than `(k+1)^2`) and the exact rational envelope

  tailCut(k) = 3 / (2*Ncut(k) + 3).

The sharper offset has two advantages.  First it still implies the requested
`tailCut(k) <= 3/(k+1)^2`.  Second it lands definitionally on the existing
`SummableInverseSquare.invSqTerm 2` machinery, giving the exact
`TrueMarginRecursionPhysical`-shaped window estimate

  tailSum tailCut N M <= 3 * pot 2 N.

We also return the existing explicit dyadic Cauchy modulus as Type-level data.
No spectral estimate is assumed or advertised: a future character-tail theorem
only has to prove that its derived error is bounded by `tailCut`.

Constructive contract: exact `Q'`/`Nat`; no `Classical`, `Real`,
`native_decide`, axioms, or holes.
-/

import YMGap.Continuum.SummableInverseSquare

namespace YMGap.Continuum.QuadraticCutoffSchedule

open YMGap.Constructive
open YMGap.Continuum.SummableInverseSquare

/-! ## 1. The coupled cutoff and exact rational envelope -/

/-- The coupled cutoff `Ncut(k) = (k+2)^2`. -/
def Ncut (k : Nat) : Nat := (k + 2) * (k + 2)

/-- The cutoff is strictly positive. -/
theorem Ncut_pos (k : Nat) : 0 < Ncut k := by
  unfold Ncut
  exact Nat.mul_pos (by omega) (by omega)

/-- The sharper cutoff dominates the requested `(k+1)^2` schedule. -/
theorem succSq_le_Ncut (k : Nat) :
    (k + 1) * (k + 1) <= Ncut k := by
  unfold Ncut
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The positive denominator `2*Ncut(k)+3` of the exact tail envelope. -/
theorem tailDenom_pos (k : Nat) : 0 < 2 * Ncut k + 3 := by omega

/-- The exact rational tail envelope `3/(2*Ncut(k)+3)`.  It is written as
`3 * unit(2*Ncut+3)` so denominator antitonicity composes directly with the
existing inverse-square library. -/
def tailCut (k : Nat) : Q' :=
  Q'.ofNat 3 * unit (2 * Ncut k + 3) (tailDenom_pos k)

/-- The tail envelope is strictly positive. -/
theorem tailCut_pos (k : Nat) : (0 : Q') < tailCut k := by
  unfold tailCut
  exact Q'.mul_pos (by decide) (unit_pos _ _)

/-- The tail envelope is nonnegative. -/
theorem tailCut_nonneg (k : Nat) : (0 : Q') <= tailCut k :=
  Q'.le_of_lt (tailCut_pos k)

/-! ## 2. Requested inverse-square envelope -/

/-- `3/(k+1)^2`, retained as an exact `Q'` comparison target. -/
def threeOverSuccSq (k : Nat) : Q' :=
  Q'.ofNat 3 *
    unit ((k + 1) * (k + 1)) (Nat.mul_pos (by omega) (by omega))

/-- **Requested cutoff estimate.**  The exact envelope obeys
`tailCut(k) <= 3/(k+1)^2`. -/
theorem tailCut_le_threeOverSuccSq (k : Nat) :
    tailCut k <= threeOverSuccSq k := by
  have hNden : Ncut k <= 2 * Ncut k + 3 := by omega
  have hden : (k + 1) * (k + 1) <= 2 * Ncut k + 3 :=
    Nat.le_trans (succSq_le_Ncut k) hNden
  have hu :
      unit (2 * Ncut k + 3) (tailDenom_pos k) <=
        unit ((k + 1) * (k + 1)) (Nat.mul_pos (by omega) (by omega)) :=
    unit_antitone (Nat.mul_pos (by omega) (by omega))
      (tailDenom_pos k) hden
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3) hu (by decide)

/-! ## 3. Landing on the existing offset-2 inverse-square machinery -/

/-- The exact envelope is bounded by `3 * invSqTerm 2 k`, definitionally
`3/(k+2)^2`.  This is the interface consumed by the existing tail theorem. -/
theorem tailCut_le_three_invSqTerm (k : Nat) :
    tailCut k <= (Q'.ofNat 3) * invSqTerm 2 (by decide) k := by
  have hden : Ncut k <= 2 * Ncut k + 3 := by omega
  have hu :
      unit (2 * Ncut k + 3) (tailDenom_pos k) <=
        unit (Ncut k) (Ncut_pos k) :=
    unit_antitone (Ncut_pos k) (tailDenom_pos k) hden
  have hmul :
      Q'.ofNat 3 * unit (2 * Ncut k + 3) (tailDenom_pos k) <=
        Q'.ofNat 3 * unit (Ncut k) (Ncut_pos k) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3) hu (by decide)
  simpa [tailCut, invSqTerm, Ncut] using hmul

/-- **True-margin-compatible window modulus.**  Every finite tail window is
bounded by the exact constant `3` times `pot 2 N = 1/(N+1)`, in precisely the
shape of `TrueMarginRecursionPhysical.budget_modulus`. -/
theorem tailCut_window_modulus (N M : Nat) :
    tailSum tailCut N M <=
      Q'.ofNat 3 * pot 2 (by decide) N :=
  summableBound_of_invSq 2 (by decide) (Q'.ofNat 3) (by decide)
    tailCut tailCut_le_three_invSqTerm N M

/-- The explicit dyadic Cauchy modulus for `tailCut`, returned as Type-level
data.  Its witness is the existing `invSqModulus 3`. -/
def tailCut_dyadic_modulus :
    Σ' modulus : Nat -> Nat,
      ∀ r M, tailSum tailCut (modulus r) M <= HalfPow.half ^ r :=
  summable_of_inverse_square_bound (Q'.ofNat 3) 2 (by decide) (by decide)
    tailCut tailCut_nonneg tailCut_le_three_invSqTerm

/-- The extracted dyadic modulus is definitionally `invSqModulus 3`. -/
theorem tailCut_dyadic_modulus_fst :
    tailCut_dyadic_modulus.1 = invSqModulus (Q'.ofNat 3) :=
  rfl

end YMGap.Continuum.QuadraticCutoffSchedule

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.QuadraticCutoffSchedule.Ncut_pos
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.succSq_le_Ncut
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.tailCut_pos
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.tailCut_le_threeOverSuccSq
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.tailCut_le_three_invSqTerm
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.tailCut_window_modulus
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.tailCut_dyadic_modulus
#print axioms YMGap.Continuum.QuadraticCutoffSchedule.tailCut_dyadic_modulus_fst

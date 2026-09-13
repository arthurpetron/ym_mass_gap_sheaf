/-
# Rate-preserving centered approximation and represented-family limits

The original centering map is nonexpansive in squared distance. Therefore
centering the original expression approximants preserves their epsilon
bound, and centering supplied Cauchy rows preserves their outer modulus.
Their constructed limits commute with centering by uniqueness.

Approximating expressions are returned as data from a supplied Cauchy
representative. These are exactly centered completed expression states,
not rational expressions asserted to be exactly orthogonal. No arbitrary
quotient representative is selected, and full quotient completeness is
not asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion
import YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "u" => completedUnit w hw0 hw1 half
local notation "B" => completedInner w hw0 hw1

def centeredExpression (e : PlaquetteExpression half) : UnitComplement w hw0 hw1 half :=
  centeredState w hw0 hw1 (embedExpression w hw0 hw1 e)

theorem centeredExpression_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    RCle (completedDist w hw0 hw1 (centeredExpression w hw0 hw1 (X.seq n)).val
      (center w hw0 hw1 (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  RCle_trans (center_nonexpansive w hw0 hw1 (embedExpression w hw0 hw1 (X.seq n)) (Quotient.mk (D).completionSetoid X))
    (constantApproximation_bound w hw0 hw1 X epsilon he n hn)

def centeredApproximant (X : (D).Cauchy) (n : Nat) : UnitComplement w hw0 hw1 half :=
  centeredExpression w hw0 hw1 (approximant w hw0 hw1 X n)

theorem centeredApproximant_bound (X : (D).Cauchy) (n : Nat) :
    RCle (completedDist w hw0 hw1 (centeredApproximant w hw0 hw1 X n).val
      (center w hw0 hw1 (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) :=
  RCle_trans (center_nonexpansive w hw0 hw1 (embedExpression w hw0 hw1 (approximant w hw0 hw1 X n))
    (Quotient.mk (D).completionSetoid X)) (approximant_bound w hw0 hw1 X n)

/-- The approximating original expression is a returned witness, not a Prop existential. -/
def approximateCentered (X : (D).Cauchy) (hX : B (Quotient.mk (D).completionSetoid X) u = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {e : PlaquetteExpression half // RCle (completedDist w hw0 hw1 (centeredExpression w hw0 hw1 e).val
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨X.seq (X.modulus epsilon), by
    have h := centeredExpression_bound w hw0 hw1 X epsilon he (X.modulus epsilon) (Nat.le_refl _)
    rw [(center_fixed_iff w hw0 hw1 _).mpr hX] at h
    exact h⟩

def centeredRows (R : CauchyRows w hw0 hw1 half) : CauchyRows w hw0 hw1 half where
  row n := centerCauchy w hw0 hw1 (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact RCle_trans (center_nonexpansive w hw0 hw1 (rowPoint w hw0 hw1 R m) (rowPoint w hw0 hw1 R n))
      (R.isCauchy epsilon he m n hm hn)

theorem centeredRows_rowPoint (R : CauchyRows w hw0 hw1 half) (n : Nat) :
    rowPoint w hw0 hw1 (centeredRows w hw0 hw1 R) n = center w hw0 hw1 (rowPoint w hw0 hw1 R n) := rfl

theorem rowLimit_centeredRows (R : CauchyRows w hw0 hw1 half) :
    rowLimit w hw0 hw1 (centeredRows w hw0 hw1 R) = center w hw0 hw1 (rowLimit w hw0 hw1 R) := by
  apply rowLimit_eq_of_bound w hw0 hw1 (centeredRows w hw0 hw1 R) _ (rowLimitRate w hw0 hw1 R)
  intro epsilon he n hn
  exact RCle_trans (center_nonexpansive w hw0 hw1 (rowPoint w hw0 hw1 R n) (rowLimit w hw0 hw1 R))
    (rowLimit_bound w hw0 hw1 R epsilon he n hn)

/-- Closedness for supplied represented Cauchy families, with no quotient choice. -/
theorem rowLimit_orthogonal (R : CauchyRows w hw0 hw1 half)
    (h : ∀ n, B (rowPoint w hw0 hw1 R n) u = RCzero) : B (rowLimit w hw0 hw1 R) u = RCzero := by
  have heq : rowLimit w hw0 hw1 (centeredRows w hw0 hw1 R) = rowLimit w hw0 hw1 R :=
    rowLimit_independent w hw0 hw1 _ _ (fun n => (center_fixed_iff w hw0 hw1 _).mpr (h n))
  rw [rowLimit_centeredRows] at heq
  exact (center_fixed_iff w hw0 hw1 _).mp heq

def complementRowLimit (R : CauchyRows w hw0 hw1 half)
    (h : ∀ n, B (rowPoint w hw0 hw1 R n) u = RCzero) : UnitComplement w hw0 hw1 half :=
  ⟨rowLimit w hw0 hw1 R, rowLimit_orthogonal w hw0 hw1 R h⟩

theorem complementRowLimit_bound (R : CauchyRows w hw0 hw1 half)
    (h : ∀ n, B (rowPoint w hw0 hw1 R n) u = RCzero) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : rowLimitRate w hw0 hw1 R epsilon ≤ n) :
    RCle (completedDist w hw0 hw1 (rowPoint w hw0 hw1 R n) (complementRowLimit w hw0 hw1 R h).val)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := rowLimit_bound w hw0 hw1 R epsilon he n hn

theorem rowLimit_centeredExpressionRows (X : (D).Cauchy) :
    rowLimit w hw0 hw1 (centeredRows w hw0 hw1 (expressionRows w hw0 hw1 X)) =
      center w hw0 hw1 (Quotient.mk (D).completionSetoid X) := by
  rw [rowLimit_centeredRows, rowLimit_expressionRows]

end YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.centeredExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.centeredExpression_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.centeredApproximant
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.centeredApproximant_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.approximateCentered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.centeredRows
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.centeredRows_rowPoint
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.rowLimit_centeredRows
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.rowLimit_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.complementRowLimit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.complementRowLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity.rowLimit_centeredExpressionRows

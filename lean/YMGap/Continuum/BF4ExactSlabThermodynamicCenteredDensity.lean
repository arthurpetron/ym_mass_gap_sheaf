/-
# Rate-preserving approximation and row limits in the original unit complement

The SAME thermodynamic centering map is nonexpansive in completed squared
distance. It therefore preserves the original approximation errors and
represented-row outer moduli. Constructed row limits commute with centering,
and orthogonal represented families have a limit in the unit complement.

The approximating presentation is actual returned data from a supplied
Cauchy representative. Its centered completed state is exactly orthogonal;
the raw rational presentation is not asserted to be so. No arbitrary
quotient representative or full quotient-level completeness is supplied.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
import YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion

local notation "D" => seminorm
local notation "u" => completedUnit
local notation "B" => completedInner

def centeredPresentation (e : Presentation) : UnitComplement :=
  centeredState (embedPresentation e)

theorem centeredPresentation_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : X.modulus epsilon ≤ n) :
    RCle (completedDist (centeredPresentation (X.seq n)).val
      (center (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  RCle_trans (center_nonexpansive (embedPresentation (X.seq n)) (Quotient.mk (D).completionSetoid X))
    (constantApproximation_bound X epsilon he n hn)

def centeredApproximant (X : (D).Cauchy) (n : Nat) : UnitComplement :=
  centeredPresentation (approximant X n)

theorem centeredApproximant_bound (X : (D).Cauchy) (n : Nat) :
    RCle (completedDist (centeredApproximant X n).val
      (center (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) :=
  RCle_trans (center_nonexpansive (embedPresentation (approximant X n))
    (Quotient.mk (D).completionSetoid X)) (approximant_bound X n)

/-- The approximating original expression is a returned witness, not a Prop existential. -/
def approximateCentered (X : (D).Cauchy) (hX : B (Quotient.mk (D).completionSetoid X) u = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {e : Presentation // RCle (completedDist (centeredPresentation e).val
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨X.seq (X.modulus epsilon), by
    have h := centeredPresentation_bound X epsilon he (X.modulus epsilon) (Nat.le_refl _)
    rw [(center_fixed_iff _).mpr hX] at h
    exact h⟩

def centeredRows (R : CauchyRows) : CauchyRows where
  row n := centerCauchy (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact RCle_trans (center_nonexpansive (rowPoint R m) (rowPoint R n))
      (R.isCauchy epsilon he m n hm hn)

theorem centeredRows_rowPoint (R : CauchyRows) (n : Nat) :
    rowPoint (centeredRows R) n = center (rowPoint R n) := rfl

theorem rowLimit_centeredRows (R : CauchyRows) :
    rowLimit (centeredRows R) = center (rowLimit R) := by
  apply rowLimit_eq_of_bound (centeredRows R) _ (rowLimitRate R)
  intro epsilon he n hn
  exact RCle_trans (center_nonexpansive (rowPoint R n) (rowLimit R))
    (rowLimit_bound R epsilon he n hn)

/-- Closedness for supplied represented Cauchy families, with no quotient choice. -/
theorem rowLimit_orthogonal (R : CauchyRows)
    (h : ∀ n, B (rowPoint R n) u = RCzero) : B (rowLimit R) u = RCzero := by
  have heq : rowLimit (centeredRows R) = rowLimit R :=
    rowLimit_independent _ _ (fun n => (center_fixed_iff _).mpr (h n))
  rw [rowLimit_centeredRows] at heq
  exact (center_fixed_iff _).mp heq

def complementRowLimit (R : CauchyRows)
    (h : ∀ n, B (rowPoint R n) u = RCzero) : UnitComplement :=
  ⟨rowLimit R, rowLimit_orthogonal R h⟩

theorem complementRowLimit_bound (R : CauchyRows)
    (h : ∀ n, B (rowPoint R n) u = RCzero) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : rowLimitRate R epsilon ≤ n) :
    RCle (completedDist (rowPoint R n) (complementRowLimit R h).val)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := rowLimit_bound R epsilon he n hn

theorem rowLimit_centeredPresentationRows (X : (D).Cauchy) :
    rowLimit (centeredRows (presentationRows X)) =
      center (Quotient.mk (D).completionSetoid X) := by
  rw [rowLimit_centeredRows, rowLimit_presentationRows]

end YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.centeredPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.centeredPresentation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.centeredApproximant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.centeredApproximant_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.approximateCentered
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.centeredRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.centeredRows_rowPoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.rowLimit_centeredRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.rowLimit_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.complementRowLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.complementRowLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity.rowLimit_centeredPresentationRows

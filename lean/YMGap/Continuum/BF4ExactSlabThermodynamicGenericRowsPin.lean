/-
# Generic represented row limits recover the ORIGINAL thermodynamic limits

The generic distance data below are supplied entirely by the existing
thermodynamic completed geometry. Converting a represented Cauchy family
retains its literal rows and outer modulus. The dense diagonal, its Cauchy
representative, its completion class, and both convergence rates therefore
agree with the existing construction by definitional equality.

This is a regression pin on the original thermodynamic completion, not an
identification with a different physical carrier. Neither construction
selects representatives of an arbitrary stream of quotient points.
-/

import YMGap.Continuum.CRealSeminormCauchyRows
import YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry

/-- Every field is an already-proved law of the SAME old completion. -/
def distanceData : CRealSeminormCompletedApproximation.DistanceData seminorm where
  representativeDist := representativeDist
  representativeDist_converges := representativeDist_converges
  completedDist := completedDist
  completedDist_mk := completedDist_mk
  completedDist_nonnegative := completedDist_nonnegative
  completedDist_symm := completedDist_symm
  completedDist_triangle := completedDist_triangle
  completedDist_zero_iff := completedDist_zero_iff

/-- The conversion changes no representative and no outer rate. -/
def toGenericRows (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) :
    CRealSeminormCauchyRows.CauchyRows distanceData where
  row := R.row
  modulus := R.modulus
  isCauchy := R.isCauchy

theorem toGenericRows_row (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) :
    (toGenericRows R).row = R.row := rfl

theorem toGenericRows_modulus (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) :
    (toGenericRows R).modulus = R.modulus := rfl

theorem approximant_pin (X : (seminorm).Cauchy) (n : Nat) :
    CRealSeminormCompletedApproximation.approximant distanceData X n =
      BF4ExactSlabThermodynamicCompletedApproximation.approximant X n := rfl

theorem rowPoint_pin (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) (n : Nat) :
    CRealSeminormCauchyRows.rowPoint distanceData (toGenericRows R) n =
      BF4ExactSlabThermodynamicCauchyRows.rowPoint R n := rfl

theorem diagonal_pin (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) (n : Nat) :
    CRealSeminormCauchyRows.diagonal distanceData (toGenericRows R) n =
      BF4ExactSlabThermodynamicCauchyRows.diagonal R n := rfl

theorem diagonalRate_pin (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows)
    (epsilon : Q') :
    CRealSeminormCauchyRows.diagonalRate distanceData (toGenericRows R) epsilon =
      BF4ExactSlabThermodynamicCauchyRows.diagonalRate R epsilon := rfl

/-- Proof irrelevance accounts for the two derivations of the same Cauchy bound. -/
theorem diagonalCauchy_pin (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) :
    CRealSeminormCauchyRows.diagonalCauchy distanceData (toGenericRows R) =
      BF4ExactSlabThermodynamicCauchyRows.diagonalCauchy R := rfl

/-- The generic constructor returns the literal old completion class. -/
theorem rowLimit_pin (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows) :
    CRealSeminormCauchyRows.rowLimit distanceData (toGenericRows R) =
      BF4ExactSlabThermodynamicCauchyRows.rowLimit R := rfl

theorem rowLimitRate_pin (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows)
    (epsilon : Q') :
    CRealSeminormCauchyRows.rowLimitRate distanceData (toGenericRows R) epsilon =
      BF4ExactSlabThermodynamicCauchyRows.rowLimitRate R epsilon := rfl

/-- The generic theorem proves the existing old bound at its unchanged rate. -/
theorem rowLimit_bound (R : BF4ExactSlabThermodynamicCauchyRows.CauchyRows)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k : Nat)
    (hk : BF4ExactSlabThermodynamicCauchyRows.rowLimitRate R epsilon ≤ k) :
    RCle (completedDist (BF4ExactSlabThermodynamicCauchyRows.rowPoint R k)
      (BF4ExactSlabThermodynamicCauchyRows.rowLimit R))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  CRealSeminormCauchyRows.rowLimit_bound distanceData (toGenericRows R) epsilon he k hk

end YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.distanceData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.toGenericRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.toGenericRows_row
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.toGenericRows_modulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.approximant_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.rowPoint_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.diagonal_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.diagonalRate_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.diagonalCauchy_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.rowLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.rowLimitRate_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGenericRowsPin.rowLimit_bound

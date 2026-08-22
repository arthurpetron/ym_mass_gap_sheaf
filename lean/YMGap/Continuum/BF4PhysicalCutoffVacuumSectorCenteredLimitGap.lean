/-
# Cofinal strict gap for the centered vacuum-sector form limits

The literal moving centered diagonal and reflected quadratic sequences are
now Bishop reals for every fixed base-sector coefficient.  A strict limit
comparison does not require a bound at every later representation cutoff:
their Cauchy moduli make a constructively cofinal family of exact finite
bounds sufficient.

This file states that weakest same-object certificate at an arbitrary
rational rate `q` with `0 <= q < 1` and proves that it contracts to the two
new centered form limits.  No inhabitant of the certificate is constructed;
that uniform finite estimate is the remaining analytic frontier.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.CRealComplete
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

/-! ## 1. The exact cofinal same-object input -/

/-- One strict rational rate, independent of the fixed base component and
later representation cutoff, certified on a constructively cofinal sequence
of later cutoffs for every base-sector coefficient. -/
structure FixedNomeCofinalVacuumSectorCenteredStrictGap
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  centeredGap :
    ∀ base threshold (coefficient : Nat → Q'),
      Q'.abs
          (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base (anchor base threshold) half
            (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
              w hw base (anchor base threshold) half coefficient)) ≤
        q *
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base (anchor base threshold) half
            (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
              w hw base (anchor base threshold) half coefficient)

namespace FixedNomeCofinalVacuumSectorCenteredStrictGap

/-! ## 2. Contraction to the two centered Bishop-real limits -/

/-- Exact strictness on any constructively cofinal family of later cutoffs
survives as the same strict comparison between the literal moving centered
form limits for every fixed base-sector coefficient. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate :
      FixedNomeCofinalVacuumSectorCenteredStrictGap
        w (Q'.le_of_lt hw0) half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) := by
  let matrix :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
      hw0 hw1 base half coefficient
  let diagonal :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
      hw0 hw1 base half coefficient
  intro epsilon hepsilon
  let delta := HalfPow.half * epsilon
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨matrixCutoff, hmatrix⟩ := matrix.cauchy delta hdelta
  obtain ⟨diagonalCutoff, hdiagonal⟩ := diagonal.cauchy delta hdelta
  let threshold := max matrixCutoff diagonalCutoff
  let anchor := certificate.anchor base threshold
  have hanchorGe : max base threshold ≤ anchor :=
    certificate.anchor_ge base threshold
  have hthresholdAnchor : threshold ≤ anchor :=
    Nat.le_trans (Nat.le_max_right _ _) hanchorGe
  have hmatrixAnchor : matrixCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_left _ _) hthresholdAnchor
  have hdiagonalAnchor : diagonalCutoff ≤ anchor :=
    Nat.le_trans (Nat.le_max_right _ _) hthresholdAnchor
  refine ⟨threshold, ?_⟩
  intro later hlater
  have hmatrixLater : matrixCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hdiagonalLater : diagonalCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  have hmatrixToAnchor :
      matrix.approx later ≤ matrix.approx anchor + delta :=
    (hmatrix later anchor hmatrixLater hmatrixAnchor).1
  have hdiagonalFromAnchor :
      diagonal.approx anchor ≤ diagonal.approx later + delta :=
    (hdiagonal anchor later hdiagonalAnchor hdiagonalLater).1
  have hanchorGap :
      matrix.approx anchor ≤ q * diagonal.approx anchor := by
    refine Q'.le_trans' _
      (Q'.abs (matrix.approx anchor)) _
      (Q'.le_abs_self _) ?_
    exact certificate.centeredGap base threshold coefficient
  have hscaledDiagonal :
      q * diagonal.approx anchor ≤
        q * (diagonal.approx later + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalFromAnchor
      certificate.rate_nonnegative
  have hscaleDelta : q * delta ≤ delta := by
    exact Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt certificate.rate_lt_one)
        (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : q * delta + delta ≤ epsilon := by
    exact Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  refine Q'.le_trans' _ _ _ hmatrixToAnchor ?_
  refine Q'.le_trans' _ (q * diagonal.approx anchor + delta) _
    (Q'.add_le_add_right _ _ delta hanchorGap) ?_
  refine Q'.le_trans' _
    (q * (diagonal.approx later + delta) + delta) _
    (Q'.add_le_add_right _ _ delta hscaledDiagonal) ?_
  refine Q'.le_trans' _
    (q * diagonal.approx later + (q * delta + delta)) _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((q * diagonal.approx later + q * delta) + delta) _
        (Q'.add_eqv_congr_right _ _ delta
          (Q'.mul_add_eqv q (diagonal.approx later) delta))
        (Q'.add_assoc_eqv
          (q * diagonal.approx later) (q * delta) delta))) ?_
  exact Q'.add_le_add_left
    (q * diagonal.approx later) (q * delta + delta) epsilon herror

end FixedNomeCofinalVacuumSectorCenteredStrictGap

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap.FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal

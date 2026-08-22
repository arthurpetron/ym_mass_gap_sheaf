/-
# Every fixed BF4 carrier contracts to a same-object Bishop-real gap

The arbitrary-base Poincare theorem supplies one rational rate below one for
every fixed finite vacuum carrier, uniformly at all later representation
cutoffs.  The moving matrix and diagonal sequences are already Bishop reals.
Their Cauchy moduli therefore pass the eventual finite estimate, with the exact
same rate, to a same-object cutoff-limit inequality.

The resulting rate may depend on the fixed base carrier.  This file does not
claim one rate on a cofinal carrier family, a completed Hilbert-space gap, a
thermodynamic limit, a continuum QFT, or the Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

/-! ## 1. A reusable eventual finite-gap contraction -/

/-- If two Bishop-real approximant sequences obey one eventual rational
absolute-value gap, with a nonnegative rate below one, then their limits obey
the corresponding eventual-order comparison at exactly that rate. -/
theorem cReal_leEv_of_eventual_abs_gap
    (matrix diagonal : CReal) (rate : Q')
    (hrate0 : (0 : Q') ≤ rate) (hrate1 : rate < (1 : Q'))
    (gapAnchor : Nat)
    (hgap : ∀ stage, gapAnchor ≤ stage →
      Q'.abs (matrix.approx stage) ≤ rate * diagonal.approx stage) :
    CReal.leEv matrix (CReal.mul (CReal.ofQ' rate) diagonal) := by
  intro tolerance htolerance
  let delta := HalfPow.half * tolerance
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos tolerance htolerance
  obtain ⟨matrixCutoff, hmatrix⟩ := matrix.cauchy delta hdelta
  obtain ⟨diagonalCutoff, hdiagonal⟩ := diagonal.cauchy delta hdelta
  let threshold := max matrixCutoff diagonalCutoff
  let anchor := max gapAnchor threshold
  have hgapAnchor : gapAnchor ≤ anchor := Nat.le_max_left _ _
  have hthresholdAnchor : threshold ≤ anchor := Nat.le_max_right _ _
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
  have hmatrixToAnchor : matrix.approx later ≤
      matrix.approx anchor + delta :=
    (hmatrix later anchor hmatrixLater hmatrixAnchor).1
  have hdiagonalFromAnchor : diagonal.approx anchor ≤
      diagonal.approx later + delta :=
    (hdiagonal anchor later hdiagonalAnchor hdiagonalLater).1
  have hanchorGap : matrix.approx anchor ≤
      rate * diagonal.approx anchor := by
    exact Q'.le_trans' _ (Q'.abs (matrix.approx anchor)) _
      (Q'.le_abs_self _) (hgap anchor hgapAnchor)
  have hscaledDiagonal : rate * diagonal.approx anchor ≤
      rate * (diagonal.approx later + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalFromAnchor hrate0
  have hscaleDelta : rate * delta ≤ delta :=
    Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt hrate1) (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : rate * delta + delta ≤ tolerance :=
    Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves tolerance))
  refine Q'.le_trans' _ _ _ hmatrixToAnchor ?_
  refine Q'.le_trans' _ (rate * diagonal.approx anchor + delta) _
    (Q'.add_le_add_right _ _ delta hanchorGap) ?_
  refine Q'.le_trans' _
    (rate * (diagonal.approx later + delta) + delta) _
    (Q'.add_le_add_right _ _ delta hscaledDiagonal) ?_
  refine Q'.le_trans' _
    (rate * diagonal.approx later + (rate * delta + delta)) _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((rate * diagonal.approx later + rate * delta) + delta) _
        (Q'.add_eqv_congr_right _ _ delta
          (Q'.mul_add_eqv rate (diagonal.approx later) delta))
        (Q'.add_assoc_eqv
          (rate * diagonal.approx later) (rate * delta) delta))) ?_
  exact Q'.add_le_add_left
    (rate * diagonal.approx later) (rate * delta + delta)
    tolerance herror

/-! ## 2. Same-object cutoff-limit gap on every fixed carrier -/

/-- The fixed carrier's exact later-uniform Poincare rate survives unchanged
between its moving centered matrix and diagonal Bishop-real limits. -/
theorem centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat)
    (certificate :
      FixedBasePulledPositiveEdgeFloor w (Q'.le_of_lt hw0) base half)
    (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ'
          (FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate))
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) := by
  apply cReal_leEv_of_eventual_abs_gap
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
      hw0 hw1 base half coefficient)
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
      hw0 hw1 base half coefficient)
    (FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate)
    (FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_nonnegative
      certificate)
    (FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_lt_one certificate)
    certificate.start
  intro later hlater
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx]
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit_approx]
  exact FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate
    certificate later hlater coefficient

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap.cReal_leEv_of_eventual_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap.centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal

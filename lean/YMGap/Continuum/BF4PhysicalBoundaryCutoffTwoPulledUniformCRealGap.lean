/-
# The fixed pulled edge floor contracts to the same-object Bishop-real gap

The uniform finite Poincare theorem holds at every cutoff after the one start
carried by the edge-floor certificate.  Exact projection recodings transfer
it to the literal approximants of the moving matrix and diagonal Bishop
reals.  A generic eventual-order argument then passes the same rational rate,
without any relaxation, to the same-object CReal form inequality.

The common positive-edge-floor certificate is not inhabited here.  No
completed Hilbert-space gap, thermodynamic limit, continuum QFT, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact projection to the literal moving approximants -/

theorem cutoffTwoActualMoving_abs_gap_at_uniformPoincareRate
    (certificate : CutoffTwoPulledUniformPositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    Q'.abs (cutoffTwoActualMovingMatrixAt later coefficient) ≤
      CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate certificate *
        cutoffTwoActualMovingDiagonalAt later coefficient := by
  have hpulled :=
    CutoffTwoPulledUniformPositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate
      certificate later hlater coefficient
  have hmatrix := cutoffTwoActualMovingMatrixAt_eqv_pulled
    later coefficient
  have hdiagonal := cutoffTwoActualMovingDiagonalAt_eqv_pulled
    later coefficient
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hmatrix))
    (Q'.le_trans' _ _ _ hpulled
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate
            certificate) _ _ (Q'.eqv_symm hdiagonal))))

/-! ## 2. An eventual-order compiler preserving the exact rational rate -/

private theorem cReal_leEv_of_eventual_abs_gap
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

/-! ## 3. Same-object cutoff-limit gap at the unrelaxed uniform rate -/

theorem centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal
    (certificate : CutoffTwoPulledUniformPositiveEdgeFloor)
    (coefficient : Nat → Q') :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ'
          (CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate
            certificate))
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  apply cReal_leEv_of_eventual_abs_gap
    (cutoffTwoMovingMatrixLimit coefficient)
    (cutoffTwoMovingDiagonalLimit coefficient)
    (CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate certificate)
    (CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate_nonnegative
      certificate)
    (CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate_lt_one
      certificate)
    certificate.start
  intro later hlater
  exact cutoffTwoActualMoving_abs_gap_at_uniformPoincareRate
    certificate later hlater coefficient

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap.cutoffTwoActualMoving_abs_gap_at_uniformPoincareRate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap.centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal

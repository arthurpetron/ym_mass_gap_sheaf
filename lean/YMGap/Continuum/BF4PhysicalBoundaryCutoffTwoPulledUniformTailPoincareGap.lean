/-
# A uniform tail Poincare rate contracts to the same-object CReal gap

Every finite moving cutoff-two approximant already has the strict Poincare
rate `q(cutoff)`.  This module isolates the remaining uniform analytic datum:
after one global cutoff, all those rates are bounded by one common rational
`q < 1`.

That datum automatically aligns with the verified coefficientwise moving-form
tail modulus.  For a given coefficient, take the maximum of the global rate
start and the modulus start.  Pairwise tail stability remains valid there,
while the finite Poincare theorem supplies the seed gap.  The existing
adaptive bridge then gives the same-object Bishop-real form gap at one common
strict rate.

The coefficientwise modulus starts are obtained inside a Prop-valued limit
proof; no choice function is formed.  No cutoff-uniform rate is constructed
here, and no completed Hilbert gap, continuum QFT, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

local infix:50 " ≈ " => Q'.eqv

private theorem add_neg_eqv_congr
    (first second recodedFirst recodedSecond : Q')
    (hfirst : first ≈ recodedFirst)
    (hsecond : second ≈ recodedSecond) :
    first + (-second) ≈ recodedFirst + (-recodedSecond) := by
  refine Q'.eqv_trans _ (recodedFirst + (-second)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ hfirst
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ hsecond)

/-! ## 1. The exact remaining uniform rate datum -/

/-- One common strict rational upper bound for all finite Poincare rates after
a global representation cutoff.  This contains no coefficientwise gap or
tail-alignment field. -/
structure CutoffTwoUniformTailPoincareRateBound (q : Q') : Type 1 where
  q_nonnegative : (0 : Q') ≤ q
  q_lt_one : q < (1 : Q')
  start : Nat
  rate_le : ∀ cutoff : Nat, start ≤ cutoff →
    cutoffTwoPulledPoincareRateAt cutoff ≤ q

namespace CutoffTwoUniformTailPoincareRateBound

theorem rowFloorAnchor_ge_two :
    2 ≤ cutoffTwoPulledRowFloorAnchor := by
  unfold cutoffTwoPulledRowFloorAnchor
  exact Nat.le_max_left _ _

/-! ## 2. Automatic alignment with each coefficient's tail -/

/-- A uniform tail rate bound and the already verified pairwise tail modulus
produce an aligned adaptive seed for each requested coefficient.  `Nonempty`
keeps the modulus witness inside Prop and therefore uses no choice function. -/
theorem nonempty_adaptiveTailSeedGapAt
    {q : Q'} (bound : CutoffTwoUniformTailPoincareRateBound q)
    (coefficient : Nat → Q') :
    Nonempty (CutoffTwoPulledAdaptiveTailSeedGapAt q coefficient) := by
  obtain ⟨tailStart, hfloor, htail⟩ :=
    movingForm_relative_errors_for_every_positive coefficient
      (cutoffTwoAdaptiveTailSeedRelativeError q)
      (cutoffTwoAdaptiveTailSeedRelativeError_pos bound.q_lt_one)
  let seed := max tailStart bound.start
  have htailSeed : tailStart ≤ seed := Nat.le_max_left _ _
  have hboundSeed : bound.start ≤ seed := Nat.le_max_right _ _
  have hfloorSeed : cutoffTwoPulledRowFloorAnchor ≤ seed :=
    Nat.le_trans hfloor htailSeed
  have htwoSeed : 2 ≤ seed :=
    Nat.le_trans rowFloorAnchor_ge_two hfloorSeed
  have hpoincare :=
    cutoffTwoActualMoving_abs_gap_at_poincareRate
      seed htwoSeed coefficient
  have hseedGap :
      Q'.abs (cutoffTwoActualMovingMatrixAt seed coefficient) ≤
        q * cutoffTwoActualMovingDiagonalAt seed coefficient := by
    exact Q'.le_trans' _ _ _ hpoincare
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (bound.rate_le seed hboundSeed)
        (cutoffTwoActualMovingDiagonalAt_nonnegative seed coefficient))
  refine ⟨{
    seed := seed
    seed_ge_floor := hfloorSeed
    seed_gap := hseedGap
    stability := ?_ }⟩
  intro later hseedLater
  have htailLater : tailStart ≤ later :=
    Nat.le_trans htailSeed hseedLater
  have hphysical := htail seed later htailSeed htailLater
  have hmatrixSeed :=
    cutoffTwoActualMovingMatrixAt_eqv_pulled seed coefficient
  have hmatrixLater :=
    cutoffTwoActualMovingMatrixAt_eqv_pulled later coefficient
  have hdiagonalSeed :=
    cutoffTwoActualMovingDiagonalAt_eqv_pulled seed coefficient
  have hdiagonalLater :=
    cutoffTwoActualMovingDiagonalAt_eqv_pulled later coefficient
  constructor
  · have hdifference :
        cutoffTwoActualMovingMatrixAt seed coefficient +
            (-cutoffTwoActualMovingMatrixAt later coefficient) ≈
          cutoffTwoPulledMatrixAt seed
              (cutoffTwoPulledMovingCenteredCoefficientAt seed coefficient) +
            (-cutoffTwoPulledMatrixAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt
                later coefficient)) :=
      add_neg_eqv_congr _ _ _ _ hmatrixSeed hmatrixLater
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
      (Q'.le_trans' _ _ _ hphysical.1
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            (cutoffTwoAdaptiveTailSeedRelativeError q) _ _
            (Q'.eqv_symm hdiagonalLater))))
  · have hdifference :
        cutoffTwoActualMovingDiagonalAt seed coefficient +
            (-cutoffTwoActualMovingDiagonalAt later coefficient) ≈
          cutoffTwoPulledDiagonalAt seed
              (cutoffTwoPulledMovingCenteredCoefficientAt seed coefficient) +
            (-cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt
                later coefficient)) :=
      add_neg_eqv_congr _ _ _ _ hdiagonalSeed hdiagonalLater
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
      (Q'.le_trans' _ _ _ hphysical.2
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            (cutoffTwoAdaptiveTailSeedRelativeError q) _ _
            (Q'.eqv_symm hdiagonalLater))))

/-! ## 3. Contraction to one uniform same-object CReal rate -/

/-- The sole uniform tail-rate datum contracts directly to the same-object
Bishop-real gap for every coefficient. -/
theorem centeredMatrixCutoffLimit_leEv_adaptiveRate_mul_diagonal
    {q : Q'} (bound : CutoffTwoUniformTailPoincareRateBound q)
    (coefficient : Nat → Q') :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' (cutoffTwoAdaptiveTailSeedRate q))
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  obtain ⟨certificate⟩ := bound.nonempty_adaptiveTailSeedGapAt coefficient
  exact
    CutoffTwoPulledAdaptiveTailSeedGapAt.centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal
      certificate bound.q_nonnegative bound.q_lt_one

theorem adaptiveRate_nonnegative
    {q : Q'} (bound : CutoffTwoUniformTailPoincareRateBound q) :
    (0 : Q') ≤ cutoffTwoAdaptiveTailSeedRate q :=
  cutoffTwoAdaptiveTailSeedRate_nonnegative
    bound.q_nonnegative bound.q_lt_one

theorem adaptiveRate_lt_one
    {q : Q'} (bound : CutoffTwoUniformTailPoincareRateBound q) :
    cutoffTwoAdaptiveTailSeedRate q < (1 : Q') :=
  cutoffTwoAdaptiveTailSeedRate_lt_one bound.q_lt_one

end CutoffTwoUniformTailPoincareRateBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap.CutoffTwoUniformTailPoincareRateBound.rowFloorAnchor_ge_two
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap.CutoffTwoUniformTailPoincareRateBound.nonempty_adaptiveTailSeedGapAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap.CutoffTwoUniformTailPoincareRateBound.centeredMatrixCutoffLimit_leEv_adaptiveRate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap.CutoffTwoUniformTailPoincareRateBound.adaptiveRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap.CutoffTwoUniformTailPoincareRateBound.adaptiveRate_lt_one

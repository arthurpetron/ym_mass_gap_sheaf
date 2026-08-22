/-
# A single tail-seed gap contracts to the cutoff-two same-object limit gap

Full moving-form tail stability cannot transport the verified cutoff-two gap
across an uncontrolled finite prefix.  It does, however, reduce the missing
input to one sharply stated finite datum: a strict gap at a cutoff which is
already a stability start.  From that one seed, every later cutoff inherits a
uniform strict rate, and the moving Bishop-real forms inherit the same rate.

The certificate below is intentionally not inhabited here.  Its stability
field is known to exist coefficientwise by the preceding tail theorem; the
remaining analytic content is alignment of a finite strict-gap seed with such
a stability start.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A fixed strict slack budget -/

/-- One two-hundredth of the later diagonal is reserved separately for law
and recentering composition after the seed. -/
def cutoffTwoTailSeedRelativeError : Q' :=
  Q'.mkPos 1 200 (by decide)

/-- The propagated rate is `49/50 * (1 + 1/200) + 1/200 = 9899/10000`. -/
def cutoffTwoTailSeedRate : Q' :=
  cutoffTwoAnchorRate * ((1 : Q') + cutoffTwoTailSeedRelativeError) +
    cutoffTwoTailSeedRelativeError

theorem cutoffTwoTailSeedRelativeError_pos :
    (0 : Q') < cutoffTwoTailSeedRelativeError := by decide

theorem cutoffTwoTailSeedRate_nonnegative :
    (0 : Q') ≤ cutoffTwoTailSeedRate := by decide

theorem cutoffTwoTailSeedRate_lt_one :
    cutoffTwoTailSeedRate < (1 : Q') := by decide

/-! ## 2. The exact remaining finite certificate -/

def cutoffTwoActualMovingMatrixAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoPulledMovingMatrix cutoff coefficient

def cutoffTwoActualMovingDiagonalAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoPulledMovingDiagonal cutoff coefficient

/-- One coefficient has a cutoff which is simultaneously a start of the
verified full moving-form tail and a finite `49/50` strict-gap seed. -/
structure CutoffTwoPulledTailSeedGapAt
    (coefficient : Nat → Q') : Type 1 where
  seed : Nat
  seed_ge_floor : cutoffTwoPulledRowFloorAnchor ≤ seed
  seed_gap :
    Q'.abs (cutoffTwoActualMovingMatrixAt seed coefficient) ≤
      cutoffTwoAnchorRate *
        cutoffTwoActualMovingDiagonalAt seed coefficient
  stability : ∀ later : Nat, seed ≤ later →
    Q'.abs
        (cutoffTwoActualMovingMatrixAt seed coefficient +
          (-cutoffTwoActualMovingMatrixAt later coefficient)) ≤
        cutoffTwoTailSeedRelativeError *
          cutoffTwoActualMovingDiagonalAt later coefficient ∧
      Q'.abs
        (cutoffTwoActualMovingDiagonalAt seed coefficient +
          (-cutoffTwoActualMovingDiagonalAt later coefficient)) ≤
        cutoffTwoTailSeedRelativeError *
          cutoffTwoActualMovingDiagonalAt later coefficient

/-- The stability half of the seed certificate is already available for
every coefficient.  Only a `49/50` gap at the returned start is not supplied
by tail Cauchy control. -/
theorem exists_cutoffTwoPulledTailStabilityStart
    (coefficient : Nat → Q') :
    ∃ seed : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ seed ∧
      ∀ later : Nat, seed ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt seed
                (cutoffTwoPulledMovingCenteredCoefficientAt seed coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            cutoffTwoTailSeedRelativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt seed
                (cutoffTwoPulledMovingCenteredCoefficientAt seed coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            cutoffTwoTailSeedRelativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  obtain ⟨seed, hfloor, htail⟩ :=
    movingForm_relative_errors_for_every_positive coefficient
      cutoffTwoTailSeedRelativeError cutoffTwoTailSeedRelativeError_pos
  exact ⟨seed, hfloor, fun later hlater =>
    htail seed later (Nat.le_refl _) hlater⟩

namespace CutoffTwoPulledTailSeedGapAt

private theorem diagonal_inflation
    {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledTailSeedGapAt coefficient)
    {later : Nat} (hlater : certificate.seed ≤ later) :
    cutoffTwoActualMovingDiagonalAt certificate.seed coefficient ≤
      ((1 : Q') + cutoffTwoTailSeedRelativeError) *
        cutoffTwoActualMovingDiagonalAt later coefficient := by
  have herror := (certificate.stability later hlater).2
  have hadd := ExpNeg.le_add_of_abs_sub_le herror
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((1 : Q') * cutoffTwoActualMovingDiagonalAt later coefficient +
          cutoffTwoTailSeedRelativeError *
            cutoffTwoActualMovingDiagonalAt later coefficient) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv _)))
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))))

/-- The seed gap propagates to every later cutoff at the explicit strict rate
`9899/10000`. -/
theorem later_abs_gap
    {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledTailSeedGapAt coefficient)
    (later : Nat) (hlater : certificate.seed ≤ later) :
    Q'.abs (cutoffTwoActualMovingMatrixAt later coefficient) ≤
      cutoffTwoTailSeedRate *
        cutoffTwoActualMovingDiagonalAt later coefficient := by
  let seedMatrix := cutoffTwoActualMovingMatrixAt certificate.seed coefficient
  let laterMatrix := cutoffTwoActualMovingMatrixAt later coefficient
  let laterDiagonal := cutoffTwoActualMovingDiagonalAt later coefficient
  have hreverseTriangle := Q'.abs_le_abs_add_abs_sub
    laterMatrix seedMatrix
  have hcommuted : Q'.abs (laterMatrix + (-seedMatrix)) ≤
      cutoffTwoTailSeedRelativeError * laterDiagonal := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          laterMatrix seedMatrix))
      (certificate.stability later hlater).1
  have hseedScaled : cutoffTwoAnchorRate *
      cutoffTwoActualMovingDiagonalAt certificate.seed coefficient ≤
      cutoffTwoAnchorRate *
        (((1 : Q') + cutoffTwoTailSeedRelativeError) * laterDiagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (certificate.diagonal_inflation hlater)
      cutoffTwoSectorRate49Over50_nonnegative
  have hsum : Q'.abs seedMatrix +
        Q'.abs (laterMatrix + (-seedMatrix)) ≤
      cutoffTwoAnchorRate *
          (((1 : Q') + cutoffTwoTailSeedRelativeError) * laterDiagonal) +
        cutoffTwoTailSeedRelativeError * laterDiagonal :=
    Q'.add_le_add
      (Q'.le_trans' _ _ _ certificate.seed_gap hseedScaled)
      hcommuted
  refine Q'.le_trans' _ _ _ hreverseTriangle
    (Q'.le_trans' _ _ _ hsum ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      ((cutoffTwoAnchorRate *
            ((1 : Q') + cutoffTwoTailSeedRelativeError)) * laterDiagonal +
        cutoffTwoTailSeedRelativeError * laterDiagonal) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv cutoffTwoAnchorRate
            ((1 : Q') + cutoffTwoTailSeedRelativeError) laterDiagonal)))
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (cutoffTwoAnchorRate *
            ((1 : Q') + cutoffTwoTailSeedRelativeError))
          cutoffTwoTailSeedRelativeError laterDiagonal)))

theorem cutoffTwoMovingMatrixLimit_approx_eq_movingForm
    (coefficient : Nat → Q') (later : Nat) :
    (cutoffTwoMovingMatrixLimit coefficient).approx later =
      cutoffTwoActualMovingMatrixAt later coefficient := rfl

theorem cutoffTwoMovingDiagonalLimit_approx_eq_movingForm
    (coefficient : Nat → Q') (later : Nat) :
    (cutoffTwoMovingDiagonalLimit coefficient).approx later =
      cutoffTwoActualMovingDiagonalAt later coefficient := rfl

/-! ## 3. Contraction to the same-object Bishop-real limit -/

/-- One aligned tail seed is sufficient for the same coefficient's literal
moving matrix and diagonal Bishop-real limits to satisfy the strict rate. -/
theorem centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal
    {coefficient : Nat → Q'}
    (certificate : CutoffTwoPulledTailSeedGapAt coefficient) :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' cutoffTwoTailSeedRate)
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  let matrix := cutoffTwoMovingMatrixLimit coefficient
  let diagonal := cutoffTwoMovingDiagonalLimit coefficient
  intro tolerance htolerance
  let delta := HalfPow.half * tolerance
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos tolerance htolerance
  obtain ⟨matrixCutoff, hmatrix⟩ := matrix.cauchy delta hdelta
  obtain ⟨diagonalCutoff, hdiagonal⟩ := diagonal.cauchy delta hdelta
  let threshold := max matrixCutoff diagonalCutoff
  let anchor := max certificate.seed threshold
  have hseedAnchor : certificate.seed ≤ anchor := Nat.le_max_left _ _
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
      cutoffTwoTailSeedRate * diagonal.approx anchor := by
    refine Q'.le_trans' _ (Q'.abs (matrix.approx anchor)) _
      (Q'.le_abs_self _) ?_
    exact certificate.later_abs_gap anchor hseedAnchor
  have hscaledDiagonal :
      cutoffTwoTailSeedRate * diagonal.approx anchor ≤
        cutoffTwoTailSeedRate * (diagonal.approx later + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalFromAnchor
      cutoffTwoTailSeedRate_nonnegative
  have hscaleDelta : cutoffTwoTailSeedRate * delta ≤ delta :=
    Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt cutoffTwoTailSeedRate_lt_one)
        (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : cutoffTwoTailSeedRate * delta + delta ≤ tolerance :=
    Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves tolerance))
  refine Q'.le_trans' _ _ _ hmatrixToAnchor ?_
  refine Q'.le_trans' _
    (cutoffTwoTailSeedRate * diagonal.approx anchor + delta) _
    (Q'.add_le_add_right _ _ delta hanchorGap) ?_
  refine Q'.le_trans' _
    (cutoffTwoTailSeedRate * (diagonal.approx later + delta) + delta) _
    (Q'.add_le_add_right _ _ delta hscaledDiagonal) ?_
  refine Q'.le_trans' _
    (cutoffTwoTailSeedRate * diagonal.approx later +
      (cutoffTwoTailSeedRate * delta + delta)) _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((cutoffTwoTailSeedRate * diagonal.approx later +
            cutoffTwoTailSeedRate * delta) + delta) _
        (Q'.add_eqv_congr_right _ _ delta
          (Q'.mul_add_eqv cutoffTwoTailSeedRate
            (diagonal.approx later) delta))
        (Q'.add_assoc_eqv
          (cutoffTwoTailSeedRate * diagonal.approx later)
          (cutoffTwoTailSeedRate * delta) delta))) ?_
  exact Q'.add_le_add_left
    (cutoffTwoTailSeedRate * diagonal.approx later)
    (cutoffTwoTailSeedRate * delta + delta) tolerance herror

end CutoffTwoPulledTailSeedGapAt

/-! ## 4. The coefficientwise finite-seed frontier -/

/-- Exact remaining input for the whole cutoff-two physical vacuum carrier:
each coefficient supplies one aligned finite tail seed.  The rate and error
budgets are uniform; only the finite seed cutoff may depend on the vector. -/
structure CutoffTwoCoefficientwiseTailSeedGap : Type 1 where
  seedGapAt : ∀ coefficient : Nat → Q',
    CutoffTwoPulledTailSeedGapAt coefficient

namespace CutoffTwoCoefficientwiseTailSeedGap

/-- A coefficientwise family of aligned finite seeds contracts to the
uniform strict same-object CReal form gap at rate `9899/10000`. -/
theorem centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal
    (family : CutoffTwoCoefficientwiseTailSeedGap)
    (coefficient : Nat → Q') :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' cutoffTwoTailSeedRate)
        (cutoffTwoMovingDiagonalLimit coefficient)) :=
  CutoffTwoPulledTailSeedGapAt.centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal
    (family.seedGapAt coefficient)

end CutoffTwoCoefficientwiseTailSeedGap

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge.exists_cutoffTwoPulledTailStabilityStart
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge.CutoffTwoPulledTailSeedGapAt.later_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge.CutoffTwoPulledTailSeedGapAt.centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge.CutoffTwoCoefficientwiseTailSeedGap.centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal

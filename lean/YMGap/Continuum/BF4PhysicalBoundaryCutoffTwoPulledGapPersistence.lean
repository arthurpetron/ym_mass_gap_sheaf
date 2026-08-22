/-
# Persistence compiler from the cutoff-two vacuum gap

The exact cutoff-two anchor does not by itself control later representation
cutoffs.  This module isolates a non-tautological sufficient comparison.  For
each later moving-centered coefficient, provide a coefficient centered at the
cutoff-two weights, compare the later matrix form with the cutoff-two matrix
form up to `epsilon` times the later diagonal, and dominate the cutoff-two
diagonal by the later diagonal.  The verified `49/50` anchor then gives the
later rate `49/50 + epsilon`.

A constructively cofinal family of these comparisons with relaxed rate below
one contracts to the existing Bishop-real moving-form limits on the fixed
cutoff-two vacuum sector.  The comparison family is not constructed here.
The imported zero-error cutoff-two anchor shows that the finite starting
point is inhabited; persistence away from that anchor remains the frontier.

No thermodynamic or continuum limit, continuum QFT, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.FiniteDeterministicKernelPushforward

local infix:50 " ≈ " => Q'.eqv

abbrev cutoffTwoAnchorRate : Q' :=
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorRate49Over50

def cutoffTwoRelaxedRate (epsilon : Q') : Q' :=
  cutoffTwoAnchorRate + epsilon

/-- The later coefficient used by the same-object cutoff architecture: keep
the cutoff-two index vector and center it against weights pulled from `later`
by changing only the root coordinate. -/
def cutoffTwoLaterMovingCoefficient
    (later : Nat) (coefficient : Nat → Q') : Nat → Q' :=
  centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient

/-- The moving centered matrix sequence at fixed base cutoff two, packaged
once so later comparison statements do not repeatedly elaborate its full
physical expression. -/
def cutoffTwoMovingMatrixLimit (coefficient : Nat → Q') : CReal :=
  centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 2 0 coefficient

/-- The matching moving centered diagonal sequence. -/
def cutoffTwoMovingDiagonalLimit (coefficient : Nat → Q') : CReal :=
  centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 2 0 coefficient

/-- Compact aliases keep the full physical expressions out of structure
elaboration while preserving them definitionally. -/
def cutoffTwoBaseWeightedMean (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorWeightedMean
    cutoffTwoHalfCoupling (by decide) 2 0 coefficient

def cutoffTwoBaseMatrix (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorMatrixQuadratic
    cutoffTwoHalfCoupling (by decide) 2 0 coefficient

def cutoffTwoBaseDiagonal (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    cutoffTwoHalfCoupling (by decide) 2 0 coefficient

def cutoffTwoPulledMovingMatrix
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  (cutoffTwoMovingMatrixLimit coefficient).approx later

def cutoffTwoPulledMovingDiagonal
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  (cutoffTwoMovingDiagonalLimit coefficient).approx later

/-! ## 1. One later-cutoff persistence comparison -/

/-- A sufficient, genuinely comparative persistence certificate at one later
cutoff.  `recentered` lives on the same 65-dimensional cutoff-two index set
and is exactly centered for the cutoff-two weights. -/
structure CutoffTwoPulledGapPersistenceAt
    (later : Nat) (epsilon : Q') : Type 1 where
  later_ge : 2 ≤ later
  recentered : (Nat → Q') → Nat → Q'
  recentered_centered : ∀ coefficient,
    cutoffTwoBaseWeightedMean (recentered coefficient) ≈ 0
  matrix_comparison : ∀ coefficient,
    Q'.abs (cutoffTwoPulledMovingMatrix later coefficient) ≤
      Q'.abs (cutoffTwoBaseMatrix (recentered coefficient)) +
        epsilon * cutoffTwoPulledMovingDiagonal later coefficient
  diagonal_comparison : ∀ coefficient,
    cutoffTwoBaseDiagonal (recentered coefficient) ≤
      cutoffTwoPulledMovingDiagonal later coefficient

namespace CutoffTwoPulledGapPersistenceAt

/-- The two comparison inequalities compile with the exact anchor theorem to
the relaxed later-cutoff gap `49/50 + epsilon`. -/
theorem relaxed_abs_gap
    {later : Nat} {epsilon : Q'}
    (certificate : CutoffTwoPulledGapPersistenceAt later epsilon)
    (coefficient : Nat → Q') :
    Q'.abs (cutoffTwoPulledMovingMatrix later coefficient) ≤
      cutoffTwoRelaxedRate epsilon *
        cutoffTwoPulledMovingDiagonal later coefficient := by
  let baseMatrix := cutoffTwoBaseMatrix (certificate.recentered coefficient)
  let baseDiagonal := cutoffTwoBaseDiagonal (certificate.recentered coefficient)
  let laterDiagonal := cutoffTwoPulledMovingDiagonal later coefficient
  have hbase : Q'.abs baseMatrix ≤ cutoffTwoAnchorRate * baseDiagonal :=
    cutoffTwoCanonicalVacuumFinite_abs_gap
      (certificate.recentered coefficient)
      (certificate.recentered_centered coefficient)
  have hscaled :
      cutoffTwoAnchorRate * baseDiagonal ≤
        cutoffTwoAnchorRate * laterDiagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (certificate.diagonal_comparison coefficient)
      cutoffTwoSectorRate49Over50_nonnegative
  have hadd :
      Q'.abs baseMatrix + epsilon * laterDiagonal ≤
        cutoffTwoAnchorRate * laterDiagonal +
          epsilon * laterDiagonal :=
    Q'.add_le_add
      (Q'.le_trans' _ _ _ hbase hscaled)
      (Q'.le_refl' _)
  refine Q'.le_trans' _ _ _
    (certificate.matrix_comparison coefficient)
    (Q'.le_trans' _ _ _ hadd ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.add_mul_eqv cutoffTwoAnchorRate epsilon laterDiagonal))

end CutoffTwoPulledGapPersistenceAt

/-! ## 2. Cofinal persistence and the fixed-sector Bishop-real gap -/

/-- One uniform error budget and one persistence comparison at a
constructively cofinal sequence of later cutoffs. -/
structure CutoffTwoCofinalPulledGapPersistence
    (epsilon : Q') : Type 1 where
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  relaxed_rate_lt_one : cutoffTwoRelaxedRate epsilon < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ threshold, max 2 threshold ≤ anchor threshold
  persistence : ∀ threshold,
    CutoffTwoPulledGapPersistenceAt (anchor threshold) epsilon

namespace CutoffTwoCofinalPulledGapPersistence

theorem anchor_abs_gap
    {epsilon : Q'}
    (family : CutoffTwoCofinalPulledGapPersistence epsilon)
    (threshold : Nat) (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledMovingMatrix
          (family.anchor threshold) coefficient) ≤
      cutoffTwoRelaxedRate epsilon *
        cutoffTwoPulledMovingDiagonal
          (family.anchor threshold) coefficient :=
  (family.persistence threshold).relaxed_abs_gap
    coefficient

/-- A cofinal persistence family contracts to a strict comparison of the
moving centered Bishop-real limits on the fixed cutoff-two vacuum sector. -/
theorem centeredMatrixCutoffLimit_leEv_relaxedRate_mul_diagonal
    {epsilon : Q'}
    (family : CutoffTwoCofinalPulledGapPersistence epsilon)
    (coefficient : Nat → Q') :
    CReal.leEv
      (cutoffTwoMovingMatrixLimit coefficient)
      (CReal.mul
        (CReal.ofQ' (cutoffTwoRelaxedRate epsilon))
        (cutoffTwoMovingDiagonalLimit coefficient)) := by
  let q := cutoffTwoRelaxedRate epsilon
  let matrix :=
    cutoffTwoMovingMatrixLimit coefficient
  let diagonal :=
    cutoffTwoMovingDiagonalLimit coefficient
  have hq0 : (0 : Q') ≤ q :=
    Q'.zero_le_add cutoffTwoAnchorRate epsilon
      cutoffTwoSectorRate49Over50_nonnegative
      family.epsilon_nonnegative
  intro tolerance htolerance
  let delta := HalfPow.half * tolerance
  have hdelta : (0 : Q') < delta :=
    ExpNeg.half_mul_pos tolerance htolerance
  obtain ⟨matrixCutoff, hmatrix⟩ := matrix.cauchy delta hdelta
  obtain ⟨diagonalCutoff, hdiagonal⟩ := diagonal.cauchy delta hdelta
  let threshold := max matrixCutoff diagonalCutoff
  let anchor := family.anchor threshold
  have hanchorGe : max 2 threshold ≤ anchor :=
    family.anchor_ge threshold
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
    refine Q'.le_trans' _ (Q'.abs (matrix.approx anchor)) _
      (Q'.le_abs_self _) ?_
    exact family.anchor_abs_gap threshold coefficient
  have hscaledDiagonal :
      q * diagonal.approx anchor ≤
        q * (diagonal.approx later + delta) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiagonalFromAnchor hq0
  have hscaleDelta : q * delta ≤ delta := by
    exact Q'.le_trans' _ ((1 : Q') * delta) _
      (Q'.mul_le_mul_of_nonneg_right _ _ delta
        (Q'.le_of_lt family.relaxed_rate_lt_one)
        (Q'.le_of_lt hdelta))
      (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  have herror : q * delta + delta ≤ tolerance := by
    exact Q'.le_trans' _ (delta + delta) _
      (Q'.add_le_add_right _ _ delta hscaleDelta)
      (Q'.le_of_eqv (ExpNeg.two_halves tolerance))
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
    (q * diagonal.approx later) (q * delta + delta) tolerance herror

end CutoffTwoCofinalPulledGapPersistence

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence.CutoffTwoPulledGapPersistenceAt.relaxed_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence.CutoffTwoCofinalPulledGapPersistence.anchor_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence.CutoffTwoCofinalPulledGapPersistence.centeredMatrixCutoffLimit_leEv_relaxedRate_mul_diagonal

/-
# A nontrivial observable on the constructed fixed pulled-carrier gap

The cutoff-two pulled carrier already has an unconditional uniform strict
form bound.  This module supplies a concrete coefficient on that same carrier:
the indicator of the vacuum-root index.  Its diagonal is strictly positive at
every later representation cutoff, and the existing uniform rate therefore
gives a strict finite-stage contraction for this explicit observable.

This is a fixed finite SU(2) carrier statement.  It does not identify the
pulled carrier with the cofinal physical carrier, does not prove a matched
capacity family, and makes no thermodynamic, continuum, QFT, or Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledNontrivialGapObservable

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

local infix:50 " ≈ " => Q'.eqv

/-- The coefficient supported at the vacuum-root index of the fixed pulled
carrier. -/
def cutoffTwoPulledRootIndicator : Nat → Q' :=
  fun index => if index = 0 then 1 else 0

theorem cutoffTwoPulledRootIndicator_mem :
    0 ∈ cutoffTwoPulledStates := by
  unfold cutoffTwoPulledStates
  exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 0

private theorem rootIndicator_term_nonnegative
    (later index : Nat) :
    (0 : Q') ≤
      (cutoffTwoPulledRootIndicator index *
        cutoffTwoPulledRootIndicator index) *
        cutoffTwoPulledWeightAt later index := by
  unfold cutoffTwoPulledRootIndicator
  by_cases hindex : index = 0
  · subst index
    simp only [if_pos rfl]
    have hweight : (0 : Q') ≤ cutoffTwoPulledWeightAt later 0 := by
      unfold cutoffTwoPulledWeightAt
      apply centralPhysicalFinitePulledWeight_nonnegative
    exact Q'.mul_nonneg _ _ (by decide)
      hweight
  · simp only [if_neg hindex]
    have hweight : (0 : Q') ≤ cutoffTwoPulledWeightAt later index := by
      unfold cutoffTwoPulledWeightAt
      apply centralPhysicalFinitePulledWeight_nonnegative
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (by decide))
      hweight

/-- The root indicator has a strictly positive diagonal at every later
representation cutoff. -/
theorem cutoffTwoPulledRootIndicator_diagonal_pos
    (later : Nat) :
    (0 : Q') <
      cutoffTwoPulledDiagonalAt later cutoffTwoPulledRootIndicator := by
  let term : Nat → Q' := fun index =>
    (cutoffTwoPulledRootIndicator index *
      cutoffTwoPulledRootIndicator index) *
      cutoffTwoPulledWeightAt later index
  have hrootTerm : term 0 ≈ cutoffTwoPulledWeightAt later 0 := by
    unfold term cutoffTwoPulledRootIndicator
    simp only [if_pos rfl]
    refine Q'.eqv_trans _
      ((1 : Q') * cutoffTwoPulledWeightAt later 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q'))
    · exact Q'.one_mul_eqv _
  have htermLe : term 0 ≤ listQSum term cutoffTwoPulledStates := by
    exact YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.listQSum_member_le term
      (fun index => rootIndicator_term_nonnegative later index)
      cutoffTwoPulledStates cutoffTwoPulledRootIndicator_mem
  have htermPos : (0 : Q') < term 0 := by
    unfold term cutoffTwoPulledWeightAt
    have hweight : (0 : Q') < cutoffTwoPulledWeightAt later 0 := by
      unfold cutoffTwoPulledWeightAt
      apply centralPhysicalFinitePulledWeight_zero_pos
    exact Q'.pos_of_lt_of_le hweight
      (Q'.le_of_eqv (Q'.eqv_symm hrootTerm))
  exact Q'.pos_of_lt_of_le htermPos htermLe

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledNontrivialGapObservable

/-
# Root/vacuum versus non-root strict contraction on the pulled carrier

The fixed cutoff-two pulled carrier already has a constructive dichotomy for
each coefficient: either all non-root coordinates vanish, or an explicit
non-root coordinate has positive magnitude.  This module connects that
dichotomy to the existing same-carrier uniform rate.  Root-supported data are
annihilated by the moving root-centering map, while the non-root branch has a
strict form inequality at every later cutoff covered by the finite certificate.

This is still a fixed finite SU(2) carrier.  It is not a cofinal capacity
comparison, a completed vacuum-complement theorem for the physical family, an
OS/continuum construction, or a Clay result.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSectorGrowth

local infix:50 " ≈ " => Q'.eqv

/-- Root-supported coefficients are killed by the moving centering map in both
the pulled matrix and pulled diagonal, for every pair of cutoffs. -/
theorem rootSupported_centered_forms_eqv_zero
    {coefficient : Nat → Q'}
    (witness : CutoffTwoRootSupportedWitness coefficient)
    (lawCutoff centeringCutoff : Nat) :
    cutoffTwoPulledMatrixAt lawCutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt
          centeringCutoff coefficient) ≈ 0 ∧
      cutoffTwoPulledDiagonalAt lawCutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt
          centeringCutoff coefficient) ≈ 0 := by
  exact ⟨
    cutoffTwoRootSupported_movingMatrix_eqv_zero
      witness.supported lawCutoff centeringCutoff,
    cutoffTwoRootSupported_movingDiagonal_eqv_zero
      witness.supported lawCutoff centeringCutoff⟩

/-- An explicit non-root coordinate makes the centered later diagonal
strictly positive, and the existing uniform finite certificate then yields a
strict form inequality for that same centered coefficient. -/
theorem nonRoot_strict_form_gap
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (later : Nat)
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later) :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) <
      cutoffTwoPulledDiagonalAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let centered := cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let rate := cutoffTwoConstructedUniformGapData.rate
  let diagonal := cutoffTwoPulledDiagonalAt later centered
  have htwo : 2 ≤ later := by
    exact Nat.le_trans
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two hlater
  have hgap := cutoffTwoConstructedUniformGapData.moving_abs_gap
    later hlater centered
  have hdiag : (0 : Q') < diagonal := by
    exact CutoffTwoNonRootCoefficientWitness.movingDiagonalAt_pos
      witness htwo
  have hrate : rate < (1 : Q') :=
    cutoffTwoConstructedUniformGapData.rate_lt_one
  have hscaled : rate * diagonal < (1 : Q') * diagonal :=
    mul_lt_mul_of_pos_right hdiag hrate
  have hscaled' : rate * diagonal < diagonal := by
    exact Q'.lt_of_le_of_lt hscaled
      (Q'.lt_of_eqv (Q'.one_mul_eqv diagonal))
  exact Q'.lt_of_le_of_lt hgap hscaled'

/-- The coefficientwise fixed-carrier split: root-supported data are
annihilated by centering, while the non-root branch supplies the strict form
gap at every later cutoff covered by the certificate. -/
theorem coefficient_centered_gap_split
    (coefficient : Nat → Q') :
    Sum
      (CutoffTwoRootSupportedWitness coefficient)
      (∀ witness : CutoffTwoNonRootCoefficientWitness coefficient,
        ∀ later : Nat,
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later →
          Q'.abs
              (cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient)) <
            cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt
                later coefficient)) := by
  cases cutoffTwoRootSupported_orNonRootData coefficient with
  | inl witness =>
      exact Sum.inl witness
  | inr witness =>
      exact Sum.inr (fun selected later hlater =>
        nonRoot_strict_form_gap selected later hlater)

/-! ## A concrete non-root excitation -/

def cutoffTwoPulledConstantOneCoefficient : Nat → Q' :=
  fun _index => 1

private theorem length_le_one_of_all_zero_nodup
    (states : List Nat)
    (hnodup : states.Nodup)
    (hall : ∀ index, index ∈ states → index = 0) :
    states.length ≤ 1 := by
  cases states with
  | nil => simp
  | cons head tail =>
      cases tail with
      | nil => simp
      | cons next rest =>
          have hhead : head = 0 := hall head (by simp)
          have hnext : next = 0 := hall next (by simp)
          have hnot : head ∉ next :: rest := hnodup.1
          exfalso
          apply hnot
          simp [hhead, hnext]

private theorem exists_nonroot_index_in_cutoffTwoPulledStates :
    ∃ index, index ∈ cutoffTwoPulledStates ∧ index ≠ 0 := by
  have hlength : 3 ≤ cutoffTwoPulledStates.length := by
    unfold cutoffTwoPulledStates
    exact centralPhysicalFiniteVacuumSectorIndices_length_ge_cutoff_succ
      (by decide : (0 : Q') < cutoffTwoHalfCoupling) 2
  by_contra hnone
  have hall : ∀ index, index ∈ cutoffTwoPulledStates → index = 0 := by
    intro index hindex
    by_contra hne
    exact hnone ⟨index, hindex, hne⟩
  have hle := length_le_one_of_all_zero_nodup
    cutoffTwoPulledStates
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      cutoffTwoHalfCoupling (by decide) 2 0)
    hall
  omega

/-- The constant-one coefficient has a concrete non-root witness on the
cutoff-two pulled carrier. -/
theorem cutoffTwoPulledConstantOne_nonRootWitness :
    CutoffTwoNonRootCoefficientWitness
      cutoffTwoPulledConstantOneCoefficient := by
  cases cutoffTwoRootSupported_orNonRootData
      cutoffTwoPulledConstantOneCoefficient with
  | inl rootSupported =>
      obtain ⟨index, hindex, hne⟩ :=
        exists_nonroot_index_in_cutoffTwoPulledStates
      have hzero := rootSupported.supported index hindex hne
      have hone : (1 : Q') ≈ 0 := by
        simpa [cutoffTwoPulledConstantOneCoefficient] using hzero
      have hnot : ¬ ((1 : Q') ≈ 0) := by decide
      exact False.elim (hnot hone)
  | inr witness =>
      exact witness

/-- The explicit constant-one excitation is strictly contracted after moving
root centering at every later cutoff covered by the fixed certificate. -/
theorem cutoffTwoPulledConstantOne_strict_form_gap
    (later : Nat)
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later) :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later
            cutoffTwoPulledConstantOneCoefficient)) <
      cutoffTwoPulledDiagonalAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later
          cutoffTwoPulledConstantOneCoefficient) := by
  exact nonRoot_strict_form_gap
    cutoffTwoPulledConstantOne_nonRootWitness later hlater

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.rootSupported_centered_forms_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.nonRoot_strict_form_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.coefficient_centered_gap_split
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.cutoffTwoPulledConstantOne_nonRootWitness
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.cutoffTwoPulledConstantOne_strict_form_gap

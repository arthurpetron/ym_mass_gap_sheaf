/-
# Exact centered-diagonal trace for the physical BF4 new tail

The component-centered BF4 boundary transform is a genuine weighted Gram.
This module applies the finite trace theorem to the actual new-state block.
For every new coordinate, divide its centered Gram diagonal by its strictly
positive stationary weight.  The sum of these exact normalized diagonals
then bounds the complete centered quadratic form of every displayed new-tail
linear combination.

The remaining analytic datum is now one scalar inequality: an upper bound on
this explicit finite trace.  A large finite computation may generate that
inequality as an exact rational certificate, but Lean checks the coordinate
definitions, positivity, trace sum, and full-form consequence.

No cutoff-uniform trace estimate is asserted in this module.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
import YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
import YMGap.Continuum.FiniteWeightedGramGNSData

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FinitePositiveFormTraceGluing
open YMGap.Continuum.FiniteWeightedGramGNSData
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The actual centered physical Gram form -/

/-- The component-centered physical BF4 boundary Gram, packaged as a
constructive GNS datum on coefficient functions. -/
def centralPhysicalFiniteVacuumSectorCenteredGramGNSData
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : GNSData :=
  finiteWeightedGramGNSData
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralBoundaryChannels cutoff half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
      w hw cutoff half)
    (fun boundary hboundary =>
      centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
        boundary hboundary)

/-- Exact rational coordinate vector at one finite-sector index. -/
def centralPhysicalFiniteVacuumSectorCoordinate
    (selected index : Nat) : Q' :=
  if index = selected then 1 else 0

/-- A duplicate-free list of coordinate deltas reassembles the coefficient
function on that list and vanishes away from it. -/
theorem centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_mask
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    ∀ indices : List Nat, indices.Nodup → ∀ index : Nat,
      (finiteLinearCombination
          (centralPhysicalFiniteVacuumSectorCenteredGramGNSData
            w hw cutoff half)
          centralPhysicalFiniteVacuumSectorCoordinate
          coefficient indices) index ≈
        if index ∈ indices then coefficient index else 0
  | [], _hnodup, index => by
      exact Q'.eqv_refl 0
  | selected :: rest, hnodup, index => by
      have hparts := List.nodup_cons.mp hnodup
      have ih :=
        centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_mask
          w hw cutoff half coefficient rest hparts.2 index
      unfold finiteLinearCombination
      change coefficient selected *
            centralPhysicalFiniteVacuumSectorCoordinate selected index +
          (finiteLinearCombination
            (centralPhysicalFiniteVacuumSectorCenteredGramGNSData
              w hw cutoff half)
            centralPhysicalFiniteVacuumSectorCoordinate
            coefficient rest) index ≈
        if index ∈ selected :: rest then coefficient index else 0
      by_cases hsame : index = selected
      · subst index
        rw [if_pos List.mem_cons_self]
        unfold centralPhysicalFiniteVacuumSectorCoordinate
        rw [if_pos rfl]
        rw [if_neg hparts.1] at ih
        refine Q'.eqv_trans _ (coefficient selected + 0) _ ?_ ?_
        · exact Q'.add_eqv_congr' (Q'.mul_one_eqv _) ih
        · exact Q'.eqv_of_eq (Q'.add_zero' _)
      · unfold centralPhysicalFiniteVacuumSectorCoordinate
        rw [if_neg hsame]
        by_cases hrest : index ∈ rest
        · rw [if_pos hrest] at ih
          rw [if_pos (List.mem_cons_of_mem selected hrest)]
          refine Q'.eqv_trans _ (0 + coefficient index) _ ?_ ?_
          · exact Q'.add_eqv_congr' (Q'.mul_zero_eqv _) ih
          · exact Q'.eqv_of_eq (Q'.zero_add' _)
        · rw [if_neg hrest] at ih
          have hcons : index ∉ selected :: rest := by
            intro hmem
            rcases List.mem_cons.mp hmem with hhead | htail
            · exact hsame hhead
            · exact hrest htail
          rw [if_neg hcons]
          refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
          · exact Q'.add_eqv_congr' (Q'.mul_zero_eqv _) ih
          · exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- On the later physical carrier, the coordinate expansion over the new
block is the already-defined literal new-tail coefficient. -/
theorem centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_newTail_on
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (index : Nat)
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw later half) :
    (finiteLinearCombination
        (centralPhysicalFiniteVacuumSectorCenteredGramGNSData
          w hw later half)
        centralPhysicalFiniteVacuumSectorCoordinate
        coefficient
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half)) index ≈
      centralPhysicalFiniteVacuumSectorNewTailCoefficient
        w hw base later half coefficient index := by
  have hmask :=
    centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_mask
      w hw later half coefficient
      (centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorNewBlockIndices_nodup
        w hw base later half)
      index
  by_cases himage : index ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half
  · have hnotnew : index ∉
        centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half := by
      intro hnew
      exact
        (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp
          hnew).2 himage
    rw [if_neg hnotnew] at hmask
    unfold centralPhysicalFiniteVacuumSectorNewTailCoefficient
      centralPhysicalFiniteEmbeddedVacuumSectorB
    rw [decide_eq_true himage, if_pos rfl]
    exact hmask
  · have hnew : index ∈
        centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half :=
      mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mpr
        ⟨hindex, himage⟩
    rw [if_pos hnew] at hmask
    unfold centralPhysicalFiniteVacuumSectorNewTailCoefficient
      centralPhysicalFiniteEmbeddedVacuumSectorB
    rw [decide_eq_false himage]
    simp only [Bool.false_eq_true, if_false]
    exact hmask

/-- The centered Gram of the coordinate expansion is exactly the centered
Gram of the literal physical new tail; coefficients outside the finite
carrier do not enter either channel transform. -/
theorem centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_self_eqv_newTail
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half
    let assembled := finiteLinearCombination D
      centralPhysicalFiniteVacuumSectorCoordinate coefficient
      (centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half)
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w hw base later half coefficient
    D.B assembled assembled ≈ D.B tail tail := by
  dsimp only
  unfold centralPhysicalFiniteVacuumSectorCenteredGramGNSData
    finiteWeightedGramGNSData
  exact weightedGramBilinear_congr_on
    (centralPhysicalFiniteVacuumSectorIndices w hw later half)
    (centralBoundaryChannels later half)
    (centralPhysicalFiniteVacuumSectorGramWeight w hw later half)
    (centralPhysicalFiniteVacuumSectorCenteredGramAmplitude
      w hw later half)
    (centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_newTail_on
      w hw base later half coefficient)
    (centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_newTail_on
      w hw base later half coefficient)

/-! ## 2. Exact normalized centered diagonals -/

/-- Centered Gram diagonal of one coordinate vector. -/
def centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half index : Nat) : Q' :=
  let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
    w hw cutoff half
  D.B
    (centralPhysicalFiniteVacuumSectorCoordinate index)
    (centralPhysicalFiniteVacuumSectorCoordinate index)

/-- The centered coordinate diagonal divided by the physical stationary
weight on the sector, and zero away from the sector. -/
def centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half index : Nat) : Q' :=
  if hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half then
    Q'.divPos
      (centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal
        w hw cutoff half index)
      (centralPhysicalFiniteWeight w hw cutoff half index)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hindex)
  else 0

theorem centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half index : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
        w hw cutoff half index := by
  unfold centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
  by_cases hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  · rw [dif_pos hindex]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      ((centralPhysicalFiniteVacuumSectorCenteredGramGNSData
        w hw cutoff half).self_nonneg
          (centralPhysicalFiniteVacuumSectorCoordinate index))
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  · rw [dif_neg hindex]
    exact Q'.le_refl' 0

/-- Each exact normalized centered diagonal pays for its own coordinate
against the stationary diagonal weight. -/
theorem centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal_le_rate_mul_weight
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal
          w hw cutoff half index ≤
      centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
          w hw cutoff half index *
        centralPhysicalFiniteWeight w hw cutoff half index := by
  unfold centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
  rw [dif_pos hindex]
  exact Q'.ge_of_eqv
    (Q'.divPos_mul_eqv
      (centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal
        w hw cutoff half index)
      (centralPhysicalFiniteWeight w hw cutoff half index)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hindex))

/-! ## 3. The exact new-tail trace and its form consequence -/

/-- Sum of normalized centered coordinate diagonals on the genuinely new
block relative to a displayed base cutoff. -/
def centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
      w hw later half)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half)

/-- Stationary diagonal norm restricted to the genuinely new block. -/
def centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index =>
      (coefficient index * coefficient index) *
        centralPhysicalFiniteWeight w hw later half index)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half)

theorem centralPhysicalFiniteVacuumSectorExactNewTailTraceRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
        w hw base later half := by
  unfold centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
  exact listQSum_nonnegative_on _ _
    (fun index _ =>
      centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate_nonnegative
        w hw later half index)

theorem centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
        w hw base later half coefficient := by
  unfold centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
  apply listQSum_nonnegative_on
  intro index hindex
  have hlater :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hindex).1
  exact Q'.mul_nonneg _ _
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (coefficient index))
    (Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hlater))

/-- The finite new-block budget is exactly the stationary diagonal norm of
the literal new-tail coefficient on the whole later carrier. -/
theorem centralPhysicalFiniteVacuumSectorDiagonalQuadratic_newTail_eqv_budget
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw later half
        (centralPhysicalFiniteVacuumSectorNewTailCoefficient
          w hw base later half coefficient) ≈
      centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
        w hw base later half coefficient := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw later half
  let oldTest := centralPhysicalFiniteEmbeddedVacuumSectorB
    w hw base later half
  let newTest := fun index => !(oldTest index)
  let value := fun index =>
    (coefficient index * coefficient index) *
      centralPhysicalFiniteWeight w hw later half index
  refine Q'.eqv_trans _
    (listQSum (finiteMaskedValue newTest value) states) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    apply listQSum_congr_on
    intro index _hindex
    unfold finiteMaskedValue newTest oldTest value
      centralPhysicalFiniteVacuumSectorNewTailCoefficient
    cases htest : centralPhysicalFiniteEmbeddedVacuumSectorB
        w hw base later half index with
    | false =>
        simp only [Bool.false_eq_true, if_false,
          Bool.not_false, if_true]
        exact Q'.eqv_refl _
    | true =>
        simp only [if_true, Bool.not_true,
          Bool.false_eq_true, if_false]
        refine Q'.eqv_trans _
          (0 * centralPhysicalFiniteWeight w hw later half index) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv 0)
        · exact Q'.zero_mul_eqv _
  · unfold centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
      centralPhysicalFiniteVacuumSectorNewBlockIndices
    exact listQSum_finiteMaskedValue_eqv_filter newTest value states

/-- The exact new-tail normalized diagonal trace bounds the complete
component-centered Gram form of the corresponding coordinate expansion. -/
theorem centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_le_exactTrace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half
    let indices := centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half
    let assembled := finiteLinearCombination D
      centralPhysicalFiniteVacuumSectorCoordinate coefficient indices
    D.B assembled assembled ≤
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
          w hw base later half *
        centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
          w hw base later half coefficient := by
  dsimp only
  exact finiteLinearCombination_self_le_traceBudget
    (centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half)
    centralPhysicalFiniteVacuumSectorCoordinate
    (centralPhysicalFiniteWeight w hw later half)
    (centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate
      w hw later half)
    coefficient
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half)
    (fun index hindex =>
      Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp
            hindex).1))
    (fun index _ =>
      centralPhysicalFiniteVacuumSectorNormalizedCenteredCoordinateRate_nonnegative
        w hw later half index)
    (fun index hindex =>
      centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal_le_rate_mul_weight
        (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp
          hindex).1)

/-- A certified scalar upper bound on the exact trace immediately gives the
same full-form bound on every new-tail coordinate expansion. -/
theorem centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_le_of_traceBound
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (tau : Q')
    (htrace :
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
        w hw base later half ≤ tau) :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half
    let indices := centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half
    let assembled := finiteLinearCombination D
      centralPhysicalFiniteVacuumSectorCoordinate coefficient indices
    D.B assembled assembled ≤
      tau * centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
        w hw base later half coefficient := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_le_exactTrace
      w hw base later half coefficient)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ htrace
      (centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget_nonnegative
        w hw base later half coefficient))

/-! ## 4. Contraction to the literal physical new tail -/

/-- The exact normalized trace now bounds the centered Gram form of the
literal new-tail coefficient used in the physical old/new decomposition. -/
theorem centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_exactTrace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w hw base later half coefficient
    D.B tail tail ≤
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
          w hw base later half *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half tail := by
  dsimp only
  have hgram :=
    centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_self_eqv_newTail
      w hw base later half coefficient
  dsimp only at hgram
  have hassembled :=
    centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_le_exactTrace
      w hw base later half coefficient
  dsimp only at hassembled
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic_newTail_eqv_budget
      w hw base later half coefficient
  have hright :
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
            w hw base later half *
          centralPhysicalFiniteVacuumSectorNewTailDiagonalBudget
            w hw base later half coefficient ≈
        centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
            w hw base later half *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw later half
            (centralPhysicalFiniteVacuumSectorNewTailCoefficient
              w hw base later half coefficient) :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hdiagonal)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hgram)
    (OSReconstructionProgress.le_of_le_eqv hassembled hright)

/-- Any certified scalar upper bound on the exact trace gives the
corresponding centered physical tail-form estimate. -/
theorem centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_of_traceBound
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (tau : Q')
    (htrace :
      centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
        w hw base later half ≤ tau) :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData
      w hw later half
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w hw base later half coefficient
    D.B tail tail ≤
      tau * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw later half tail := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_exactTrace
      w hw base later half coefficient)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ htrace
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
        w hw later half
        (centralPhysicalFiniteVacuumSectorNewTailCoefficient
          w hw base later half coefficient)))

end YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorCenteredGramGNSData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorCenteredCoordinateDiagonal_le_rate_mul_weight
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_le_exactTrace
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorCenteredNewTailLinearCombination_le_of_traceBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorCoordinateCombination_eqv_newTail_on
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorDiagonalQuadratic_newTail_eqv_budget
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace.centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_of_traceBound

/-
# Raw-row ratio form of the cutoff-two novel-flow ceiling

Every retained stationary weight is the corresponding unnormalised BF4
reflected-kernel row mass times one common partition reciprocal.  This module
proves that the common factor cancels exactly from each positive-edge
stationary ratio.  Consequently the previously constructed finite
reverse/forward conditional ceiling is exactly the located maximum of raw
BF4 row-mass ratios over positive physical edges.

This is a genuine normalization cancellation: the remaining scalar is a sum
of unnormalised reflected spin-foam kernel entries and no longer contains the
global slab partition.  It does not bound those local raw-row ratios uniformly
in the cutoff, pay the resulting flow load, construct a thermodynamic or
continuum limit, or prove the Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The common partition factor -/

/-- Unnormalised reflected-kernel row mass of an indexed cutoff-two vacuum
sector state, summed over the literal positive-row carrier. -/
def cutoffTwoRawStationaryRowMass (later state : Nat) : Q' :=
  listQSum
    (centralPhysicalReflectedKernel
      cutoffTwoHalfCoupling later 0
      (centralPhysicalFiniteStateAt
        cutoffTwoHalfCoupling (by decide) later 0 state))
    (centralPositiveHalfStates
      cutoffTwoHalfCoupling (by decide) later 0)

theorem cutoffTwoRawStationaryRowMass_nonnegative
    (later state : Nat) :
    (0 : Q') ≤ cutoffTwoRawStationaryRowMass later state := by
  unfold cutoffTwoRawStationaryRowMass
  apply listQSum_nonnegative_on
  intro target _htarget
  exact
    BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
      (by decide) later 0 _ target

def cutoffTwoCommonPartitionReciprocal (later : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorPartitionReciprocal
    cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoCommonPartitionReciprocal_pos
    (later : Nat) :
    (0 : Q') < cutoffTwoCommonPartitionReciprocal later := by
  unfold cutoffTwoCommonPartitionReciprocal
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
  exact Q'.recipPos_pos _ _

/-- Every retained stationary weight factors through the same global
partition reciprocal. -/
theorem cutoffTwoEdgeLoadWeight_eqv_rawRowMass_mul_commonReciprocal
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoEdgeLoadWeight later state ≈
      cutoffTwoRawStationaryRowMass later state *
        cutoffTwoCommonPartitionReciprocal later := by
  have hpositive :=
    centralPhysicalFiniteStateAt_mem_positive
      cutoffTwoHalfCoupling (by decide) later 0
      (centralPhysicalFiniteVacuumSectorIndex_lt
        cutoffTwoHalfCoupling (by decide) later 0 hstate)
  have hhalf := (mem_centralPositiveHalfStates_iff.mp hpositive).1
  unfold cutoffTwoEdgeLoadWeight centralPhysicalFiniteWeight
    cutoffTwoRawStationaryRowMass cutoffTwoCommonPartitionReciprocal
  exact
    centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
      hhalf

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-- Retention in the physical vacuum carrier constructively implies strict
positivity of the corresponding unnormalised reflected row mass. -/
theorem cutoffTwoRawStationaryRowMass_pos
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadFullStates later) :
    (0 : Q') < cutoffTwoRawStationaryRowMass later state := by
  have hweight : (0 : Q') < cutoffTwoEdgeLoadWeight later state :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w := cutoffTwoHalfCoupling) (hw := by decide) hstate
  have hfactor :=
    cutoffTwoEdgeLoadWeight_eqv_rawRowMass_mul_commonReciprocal hstate
  have hproduct :
      (0 : Q') <
        cutoffTwoRawStationaryRowMass later state *
          cutoffTwoCommonPartitionReciprocal later :=
    Q'.pos_of_lt_of_le hweight (Q'.le_of_eqv hfactor)
  exact q_left_pos_of_mul_pos_local
    (Q'.le_of_lt (cutoffTwoCommonPartitionReciprocal_pos later)) hproduct

/-! ## 2. Exact cancellation in one stationary ratio -/

private theorem divPos_eqv_divPos_of_cross_local
    {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul hq hcancel

theorem cutoffTwoStationaryWeightRatio_eqv_rawRowMassRatio
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    Q'.divPos
        (cutoffTwoEdgeLoadWeight later left)
        (cutoffTwoEdgeLoadWeight later right)
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (w := cutoffTwoHalfCoupling) (hw := by decide) hright) ≈
      Q'.divPos
        (cutoffTwoRawStationaryRowMass later left)
        (cutoffTwoRawStationaryRowMass later right)
        (cutoffTwoRawStationaryRowMass_pos hright) := by
  apply divPos_eqv_divPos_of_cross_local
  let reciprocal := cutoffTwoCommonPartitionReciprocal later
  have hleftFactor :=
    cutoffTwoEdgeLoadWeight_eqv_rawRowMass_mul_commonReciprocal hleft
  have hrightFactor :=
    cutoffTwoEdgeLoadWeight_eqv_rawRowMass_mul_commonReciprocal hright
  refine Q'.eqv_trans _
    ((cutoffTwoRawStationaryRowMass later left * reciprocal) *
      cutoffTwoRawStationaryRowMass later right) _
    (Q'.mul_eqv_congr_right _ _ _ hleftFactor) ?_
  refine Q'.eqv_trans _
    (cutoffTwoRawStationaryRowMass later left *
      (reciprocal * cutoffTwoRawStationaryRowMass later right)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (cutoffTwoRawStationaryRowMass later left *
      (cutoffTwoRawStationaryRowMass later right * reciprocal)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv reciprocal
        (cutoffTwoRawStationaryRowMass later right))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hrightFactor)

/-! ## 3. Positive-edge raw ratio and its exact finite maximum -/

/-- Raw reflected-row-mass ratio on a positive physical edge, totalized by
zero away from the literal domain. -/
def cutoffTwoPositiveEdgeRawRowMassRatio
    (later left right : Nat) : Q' :=
  if _hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      if _hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right then
        Q'.divPos
          (cutoffTwoRawStationaryRowMass later left)
          (cutoffTwoRawStationaryRowMass later right)
          (cutoffTwoRawStationaryRowMass_pos hright)
      else 0
    else 0
  else 0

theorem cutoffTwoPositiveEdgeRawRowMassRatio_nonnegative
    (later left right : Nat) :
    (0 : Q') ≤ cutoffTwoPositiveEdgeRawRowMassRatio later left right := by
  unfold cutoffTwoPositiveEdgeRawRowMassRatio
  split
  · split
    · split
      · unfold Q'.divPos
        exact Q'.mul_nonneg _ _
          (cutoffTwoRawStationaryRowMass_nonnegative later left)
          (Q'.le_of_lt (Q'.recipPos_pos _ _))
      · exact Q'.le_refl' 0
    · exact Q'.le_refl' 0
  · exact Q'.le_refl' 0

theorem cutoffTwoPositiveEdgeStationaryWeightRatio_eqv_rawRowMassRatio
    (later left right : Nat) :
    cutoffTwoPositiveEdgeStationaryWeightRatio later left right ≈
      cutoffTwoPositiveEdgeRawRowMassRatio later left right := by
  unfold cutoffTwoPositiveEdgeStationaryWeightRatio
    cutoffTwoPositiveEdgeRawRowMassRatio
  by_cases hleft : left ∈ cutoffTwoEdgeLoadFullStates later
  · rw [dif_pos hleft, dif_pos hleft]
    by_cases hright : right ∈ cutoffTwoEdgeLoadFullStates later
    · rw [dif_pos hright, dif_pos hright]
      by_cases hforward : (0 : Q') <
          cutoffTwoEdgeLoadKernel later left right
      · rw [dif_pos hforward, dif_pos hforward]
        exact cutoffTwoStationaryWeightRatio_eqv_rawRowMassRatio
          hleft hright
      · rw [dif_neg hforward, dif_neg hforward]
        exact Q'.eqv_refl 0
    · rw [dif_neg hright, dif_neg hright]
      exact Q'.eqv_refl 0
  · rw [dif_neg hleft, dif_neg hleft]
    exact Q'.eqv_refl 0

theorem cutoffTwoConditionalReverseForwardRatio_eqv_rawRowMassRatio
    (later left right : Nat) :
    cutoffTwoConditionalReverseForwardRatio later left right ≈
      cutoffTwoPositiveEdgeRawRowMassRatio later left right :=
  Q'.eqv_trans _ _ _
    (cutoffTwoConditionalReverseForwardRatio_eqv_positiveEdgeStationaryWeightRatio
      later left right)
    (cutoffTwoPositiveEdgeStationaryWeightRatio_eqv_rawRowMassRatio
      later left right)

/-- Located maximum of raw row-mass ratios over exactly the positive physical
edges in the finite vacuum-sector carrier. -/
def cutoffTwoPositiveEdgeRawRowMassFiniteCeiling (later : Nat) : Q' :=
  listQMaxZero
    (fun pair : Nat × Nat =>
      cutoffTwoPositiveEdgeRawRowMassRatio later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later))

theorem cutoffTwoPositiveEdgeRawRowMassFiniteCeiling_nonnegative
    (later : Nat) :
    (0 : Q') ≤ cutoffTwoPositiveEdgeRawRowMassFiniteCeiling later := by
  unfold cutoffTwoPositiveEdgeRawRowMassFiniteCeiling
  apply listQMaxZero_nonnegative
  intro pair
  exact cutoffTwoPositiveEdgeRawRowMassRatio_nonnegative
    later pair.1 pair.2

/-- The concrete conditional ceiling contains no residual global partition:
it is exactly the maximum of unnormalised BF4 row-mass ratios on positive
edges. -/
theorem cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_rawRowMassFiniteCeiling
    (later : Nat) :
    cutoffTwoConditionalReverseForwardFiniteCeiling later ≈
      cutoffTwoPositiveEdgeRawRowMassFiniteCeiling later := by
  unfold cutoffTwoConditionalReverseForwardFiniteCeiling
    cutoffTwoPositiveEdgeRawRowMassFiniteCeiling
  apply Q'.eqv_of_le_le
  · apply listQMaxZero_mono
    intro pair
    exact Q'.le_of_eqv
      (cutoffTwoConditionalReverseForwardRatio_eqv_rawRowMassRatio
        later pair.1 pair.2)
  · apply listQMaxZero_mono
    intro pair
    exact Q'.ge_of_eqv
      (cutoffTwoConditionalReverseForwardRatio_eqv_rawRowMassRatio
        later pair.1 pair.2)

/-! ## 4. Raw-row payment compiler -/

def cutoffTwoPositiveEdgeRawRowMassFiniteCeilingData
    (later : Nat) :
    CutoffTwoConditionalReverseForwardCeilingAt later
      (cutoffTwoPositiveEdgeRawRowMassFiniteCeiling later) where
  rho_nonnegative :=
    cutoffTwoPositiveEdgeRawRowMassFiniteCeiling_nonnegative later
  ratio_le := fun _left hleft _right hright hforward =>
    Q'.le_trans' _ _ _
      (cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling
        hleft hright hforward)
      (Q'.le_of_eqv
        (cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_rawRowMassFiniteCeiling
          later))

def cutoffTwoNovelConditionalRawRowMassRatioLoad
    (later source target : Nat) : Q' :=
  cutoffTwoNovelConditionalRatioCeilingLoad
    (cutoffTwoPositiveEdgeRawRowMassFiniteCeiling later)
    later source target

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_rawRowMassRatio
    (later : Nat)
    (hraw : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadFullStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalRawRowMassRatioLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling
    (cutoffTwoPositiveEdgeRawRowMassFiniteCeilingData later)
  exact hraw

structure CutoffTwoCofinalNovelConditionalRawRowMassRatioBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  raw_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalRawRowMassRatioLoad
            (anchor request) source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalRawRowMassRatioBound

def toCofinalNovelConditionalRatioCeilingBound
    (bound : CutoffTwoCofinalNovelConditionalRawRowMassRatioBound) :
    CutoffTwoCofinalNovelConditionalRatioCeilingBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  rho := fun request =>
    cutoffTwoPositiveEdgeRawRowMassFiniteCeiling
      (bound.anchor request)
  local_ceiling := fun request =>
    cutoffTwoPositiveEdgeRawRowMassFiniteCeilingData
      (bound.anchor request)
  ceiling_capacity := fun request => bound.raw_capacity request

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelConditionalRawRowMassRatioBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalRawRowMassRatioBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.cutoffTwoEdgeLoadWeight_eqv_rawRowMass_mul_commonReciprocal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.cutoffTwoRawStationaryRowMass_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.cutoffTwoStationaryWeightRatio_eqv_rawRowMassRatio
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.cutoffTwoConditionalReverseForwardRatio_eqv_rawRowMassRatio
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_rawRowMassFiniteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_rawRowMassRatio
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.CutoffTwoCofinalNovelConditionalRawRowMassRatioBound.toCompletedStrictContractionData

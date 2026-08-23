/-
# Support-aware boundary defect for the cutoff-two novel-flow ceiling

A pure pointwise multiplicative comparison of adjacent BF4 half-amplitude
rows is incompatible with the literal cutoff-two support: the fundamental
cube row is positive on a boundary channel where the vacuum row vanishes,
even though the cube and vacuum are joined by a positive physical edge.

This module first turns that known support witness into a no-go theorem for
the pointwise Harnack interface.  It then replaces the invalid shortcut by an
exact, zero-tolerant decomposition.  For a nonnegative core factor `rho`, the
absolute residual

  |leftAmplitude - rho * rightAmplitude|

is weighted by the same boundary weight and total target amplitude as the
raw row moment.  The raw row ratio is bounded by `rho` plus this defect moment
divided by the positive right raw mass.  A located finite maximum of those
defect fractions therefore supplies a concrete support-aware conditional
ceiling and a cofinal payment compiler.

No uniform defect estimate or payment is proved.  No completed gap
inhabitant, thermodynamic/continuum construction, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment
import YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveStar
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumHub
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalVacuumSectorProjectiveObstruction
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The pure multiplicative shortcut fails at cutoff two -/

/-- The explicit cube/vacuum support mismatch occurs on a positive physical
edge, so no finite pointwise half-amplitude Harnack datum exists at cutoff
two, regardless of the proposed factor. -/
theorem no_cutoffTwoPositiveEdgeHalfAmplitudeHarnackAt
    (rho : Q') :
    CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt 2 rho → False := by
  intro harnack
  apply cutoffTwoVacuumHub_elim
  intro hubIndex hhubIndex hhubState hvacuumHub
  have hrootVertex :
      0 ∈ centralPhysicalFiniteIndexCarrier
        cutoffTwoHalfCoupling (by decide) 2 0 :=
    zero_mem_centralPhysicalFiniteIndexCarrier
      cutoffTwoHalfCoupling (by decide) 2 0
  have hvacuumSector :
      0 ∈ centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0 :=
    zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0
  have hhubVertex :
      hubIndex ∈ centralPhysicalFiniteIndexCarrier
        cutoffTwoHalfCoupling (by decide) 2 0 := by
    unfold centralPhysicalFiniteIndexCarrier
    exact List.mem_range.mpr hhubIndex
  have hhubSector :
      hubIndex ∈ centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0 :=
    rootComponent_closed_under_edge
      (centralPhysicalFiniteSupportAdjacentB
        cutoffTwoHalfCoupling (by decide) 2 0)
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        cutoffTwoHalfCoupling (by decide) 2 0)
      hrootVertex hvacuumSector hhubVertex hvacuumHub
  have hhubVacuum :
      centralPhysicalFiniteSupportAdjacentB
        cutoffTwoHalfCoupling (by decide) 2 0 hubIndex 0 = true := by
    rw [centralPhysicalFiniteSupportAdjacentB_symmetric
      cutoffTwoHalfCoupling (by decide) 2 0 hubIndex 0]
    exact hvacuumHub
  have hpositive :
      (0 : Q') < cutoffTwoEdgeLoadKernel 2 hubIndex 0 := by
    unfold cutoffTwoEdgeLoadKernel
    exact centralPhysicalFiniteKernel_pos_of_supportAdjacent
      hhubSector hvacuumSector hhubVacuum
  have hle := harnack.amplitude_le
    hubIndex (by
      simpa only [cutoffTwoEdgeLoadFullStates] using hhubSector)
    0 (by
      simpa only [cutoffTwoEdgeLoadFullStates] using hvacuumSector)
    hpositive cutoffTwoCubeSingleFaceBoundary
    cutoffTwoCubeSingleFaceBoundary_mem_channels
  rw [hhubState, cutoffTwoSectorStateAt_zero_eq_cube,
    centralPhysicalFiniteStateAt_zero_eq_vacuum] at hle
  have hrightZero :
      rho *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            zeroEdgeLabelling cutoffTwoCubeSingleFaceBoundary ≈
        0 := by
    refine Q'.eqv_trans _ (rho * 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left rho _ _
        centralHalfAmplitude_cutoffTwo_vacuum_singleFaceBoundary_eqv_zero
    · exact Q'.mul_zero_eqv rho
  have hnonpositive :
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          centralLowerCubeState cutoffTwoCubeSingleFaceBoundary ≤ 0 :=
    Q'.le_trans' _ _ _ hle (Q'.le_of_eqv hrightZero)
  exact (Int.not_lt_of_ge hnonpositive)
    centralHalfAmplitude_cutoffTwo_cube_singleFaceBoundary_pos

/-! ## 2. A zero-tolerant weighted boundary defect -/

def cutoffTwoHalfAmplitudeRelativeDefect
    (rho : Q') (later left right : Nat)
    (boundary : EdgeLabelling) : Q' :=
  Q'.abs
    (centralHalfAmplitude cutoffTwoHalfCoupling later 0
        (centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) later 0 left)
        boundary +
      -(rho *
        centralHalfAmplitude cutoffTwoHalfCoupling later 0
          (centralPhysicalFiniteStateAt
            cutoffTwoHalfCoupling (by decide) later 0 right)
          boundary))

theorem cutoffTwoHalfAmplitudeRelativeDefect_nonnegative
    (rho : Q') (later left right : Nat)
    (boundary : EdgeLabelling) :
    (0 : Q') ≤
      cutoffTwoHalfAmplitudeRelativeDefect
        rho later left right boundary := by
  unfold cutoffTwoHalfAmplitudeRelativeDefect
  exact Q'.abs_nonneg _

def cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
    (rho : Q') (later left right : Nat)
    (boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary *
    (cutoffTwoHalfAmplitudeRelativeDefect
        rho later left right boundary *
      centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling (by decide) later 0 boundary)

def cutoffTwoHalfAmplitudeRelativeDefectMoment
    (rho : Q') (later left right : Nat) : Q' :=
  listQSum
    (cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
      rho later left right)
    (centralBoundaryChannels later 0)

theorem cutoffTwoHalfAmplitudeRelativeDefectMoment_nonnegative
    (rho : Q') (later left right : Nat) :
    (0 : Q') ≤
      cutoffTwoHalfAmplitudeRelativeDefectMoment
        rho later left right := by
  unfold cutoffTwoHalfAmplitudeRelativeDefectMoment
  apply listQSum_nonnegative_on
  intro boundary hboundary
  unfold cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
  exact Q'.mul_nonneg _ _
    (centralBoundaryWeight_nonnegative_on
      (by decide) boundary hboundary)
    (Q'.mul_nonneg _ _
      (cutoffTwoHalfAmplitudeRelativeDefect_nonnegative
        rho later left right boundary)
      (cutoffTwoPositiveBoundaryTotalHalfAmplitude_nonnegative
        later boundary))

theorem cutoffTwoHalfAmplitude_le_scaled_add_relativeDefect
    (rho : Q') (later left right : Nat)
    (boundary : EdgeLabelling) :
    centralHalfAmplitude cutoffTwoHalfCoupling later 0
        (centralPhysicalFiniteStateAt
          cutoffTwoHalfCoupling (by decide) later 0 left)
        boundary ≤
      rho *
          centralHalfAmplitude cutoffTwoHalfCoupling later 0
            (centralPhysicalFiniteStateAt
              cutoffTwoHalfCoupling (by decide) later 0 right)
            boundary +
        cutoffTwoHalfAmplitudeRelativeDefect
          rho later left right boundary := by
  unfold cutoffTwoHalfAmplitudeRelativeDefect
  exact ExpNeg.le_add_of_abs_sub_le (Q'.le_refl' _)

private theorem q_boundary_moment_scale_reorder_local
    (weight rho amplitude total : Q') :
    weight * ((rho * amplitude) * total) ≈
      rho * (weight * (amplitude * total)) := by
  refine Q'.eqv_trans _
    (weight * (rho * (amplitude * total))) _
    (Q'.mul_eqv_congr_left weight _ _
      (Q'.mul_assoc_eqv rho amplitude total)) ?_
  refine Q'.eqv_trans _
    ((weight * rho) * (amplitude * total)) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv weight rho (amplitude * total))) ?_
  refine Q'.eqv_trans _
    ((rho * weight) * (amplitude * total)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv weight rho)) ?_
  exact Q'.mul_assoc_eqv rho weight (amplitude * total)

private theorem q_weighted_scaled_add_defect_reorder
    (weight rho amplitude defect total : Q') :
    weight * (((rho * amplitude) + defect) * total) ≈
      rho * (weight * (amplitude * total)) +
        weight * (defect * total) := by
  refine Q'.eqv_trans _
    (weight *
      (((rho * amplitude) * total) + (defect * total))) _
    (Q'.mul_eqv_congr_left weight _ _
      (Q'.add_mul_eqv (rho * amplitude) defect total)) ?_
  refine Q'.eqv_trans _
    (weight * ((rho * amplitude) * total) +
      weight * (defect * total)) _
    (Q'.mul_add_eqv weight
      ((rho * amplitude) * total) (defect * total)) ?_
  exact Q'.add_eqv_congr'
    (q_boundary_moment_scale_reorder_local
      weight rho amplitude total)
    (Q'.eqv_refl _)

theorem cutoffTwoRawBoundaryMomentTerm_le_scaled_add_defectTerm
    {rho : Q'}
    (later left right : Nat) {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels later 0) :
    cutoffTwoRawBoundaryMomentTerm later left boundary ≤
      rho * cutoffTwoRawBoundaryMomentTerm later right boundary +
        cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
          rho later left right boundary := by
  have htotal : (0 : Q') ≤
      centralPositiveBoundaryTotalHalfAmplitude
        cutoffTwoHalfCoupling (by decide) later 0 boundary :=
    cutoffTwoPositiveBoundaryTotalHalfAmplitude_nonnegative later boundary
  have hweight : (0 : Q') ≤
      centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary :=
    centralBoundaryWeight_nonnegative_on
      (by decide) boundary hboundary
  unfold cutoffTwoRawBoundaryMomentTerm
    cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
  refine Q'.le_trans' _
    (centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary *
      (((rho *
          centralHalfAmplitude cutoffTwoHalfCoupling later 0
            (centralPhysicalFiniteStateAt
              cutoffTwoHalfCoupling (by decide) later 0 right)
            boundary) +
          cutoffTwoHalfAmplitudeRelativeDefect
            rho later left right boundary) *
        centralPositiveBoundaryTotalHalfAmplitude
          cutoffTwoHalfCoupling (by decide) later 0 boundary)) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (cutoffTwoHalfAmplitude_le_scaled_add_relativeDefect
          rho later left right boundary)
        htotal)
      hweight
  · exact Q'.le_of_eqv
      (q_weighted_scaled_add_defect_reorder
        (centralBoundaryWeight cutoffTwoHalfCoupling later 0 boundary)
        rho
        (centralHalfAmplitude cutoffTwoHalfCoupling later 0
          (centralPhysicalFiniteStateAt
            cutoffTwoHalfCoupling (by decide) later 0 right)
          boundary)
        (cutoffTwoHalfAmplitudeRelativeDefect
          rho later left right boundary)
        (centralPositiveBoundaryTotalHalfAmplitude
          cutoffTwoHalfCoupling (by decide) later 0 boundary))

theorem cutoffTwoRawBoundaryMoment_le_scaled_add_defectMoment
    (rho : Q') (later left right : Nat) :
    cutoffTwoRawBoundaryMoment later left ≤
      rho * cutoffTwoRawBoundaryMoment later right +
        cutoffTwoHalfAmplitudeRelativeDefectMoment
          rho later left right := by
  unfold cutoffTwoRawBoundaryMoment
    cutoffTwoHalfAmplitudeRelativeDefectMoment
  refine Q'.le_trans' _
    (listQSum
      (fun boundary =>
        rho * cutoffTwoRawBoundaryMomentTerm later right boundary +
          cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
            rho later left right boundary)
      (centralBoundaryChannels later 0)) _ ?_ ?_
  · apply listQSum_mono
    intro boundary hboundary
    exact cutoffTwoRawBoundaryMomentTerm_le_scaled_add_defectTerm
      later left right hboundary
  · refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (listQSum_add
        (fun boundary =>
          rho * cutoffTwoRawBoundaryMomentTerm later right boundary)
        (cutoffTwoHalfAmplitudeRelativeDefectMomentTerm
          rho later left right)
        (centralBoundaryChannels later 0)) ?_)
    exact Q'.add_eqv_congr'
      (listQSum_mul_left rho
        (cutoffTwoRawBoundaryMomentTerm later right)
        (centralBoundaryChannels later 0))
      (Q'.eqv_refl _)

/-! ## 3. The defect fraction bounds the raw and conditional ratios -/

theorem cutoffTwoRawStationaryRowMass_le_scaled_add_defectMoment
    {rho : Q'}
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoRawStationaryRowMass later left ≤
      rho * cutoffTwoRawStationaryRowMass later right +
        cutoffTwoHalfAmplitudeRelativeDefectMoment
          rho later left right := by
  refine Q'.le_trans' _
    (cutoffTwoRawBoundaryMoment later left) _
    (Q'.le_of_eqv
      (cutoffTwoRawStationaryRowMass_eqv_boundaryMoment hleft)) ?_
  refine Q'.le_trans' _
    (rho * cutoffTwoRawBoundaryMoment later right +
      cutoffTwoHalfAmplitudeRelativeDefectMoment
        rho later left right) _
    (cutoffTwoRawBoundaryMoment_le_scaled_add_defectMoment
      rho later left right) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left rho _ _
        (Q'.eqv_symm
          (cutoffTwoRawStationaryRowMass_eqv_boundaryMoment hright)))
      (Q'.eqv_refl _))

theorem cutoffTwoRawStationaryRowMassRatio_le_rho_add_defectFraction
    {rho : Q'}
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    Q'.divPos
        (cutoffTwoRawStationaryRowMass later left)
        (cutoffTwoRawStationaryRowMass later right)
        (cutoffTwoRawStationaryRowMass_pos hright) ≤
      rho +
        Q'.divPos
          (cutoffTwoHalfAmplitudeRelativeDefectMoment
            rho later left right)
          (cutoffTwoRawStationaryRowMass later right)
          (cutoffTwoRawStationaryRowMass_pos hright) := by
  let rightMass := cutoffTwoRawStationaryRowMass later right
  let defect := cutoffTwoHalfAmplitudeRelativeDefectMoment
    rho later left right
  let defectFraction := Q'.divPos defect rightMass
    (cutoffTwoRawStationaryRowMass_pos hright)
  apply Q'.divPos_le_of_le_mul
  have hrow := cutoffTwoRawStationaryRowMass_le_scaled_add_defectMoment
    (rho := rho) hleft hright
  refine Q'.le_trans' _ (rho * rightMass + defect) _ hrow ?_
  have hcollapse :
      (rho + defectFraction) * rightMass ≈
        rho * rightMass + defect := by
    refine Q'.eqv_trans _
      (rho * rightMass + defectFraction * rightMass) _
      (Q'.add_mul_eqv rho defectFraction rightMass) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.divPos_mul_eqv defect rightMass
        (cutoffTwoRawStationaryRowMass_pos hright))
  exact Q'.le_of_eqv (Q'.eqv_symm hcollapse)

def cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction
    (rho : Q') (later left right : Nat) : Q' :=
  if _hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      if _hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right then
        Q'.divPos
          (cutoffTwoHalfAmplitudeRelativeDefectMoment
            rho later left right)
          (cutoffTwoRawStationaryRowMass later right)
          (cutoffTwoRawStationaryRowMass_pos hright)
      else 0
    else 0
  else 0

theorem cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction_nonnegative
    (rho : Q') (later left right : Nat) :
    (0 : Q') ≤
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction
        rho later left right := by
  unfold cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction
  split
  · split
    · split
      · unfold Q'.divPos
        exact Q'.mul_nonneg _ _
          (cutoffTwoHalfAmplitudeRelativeDefectMoment_nonnegative
            rho later left right)
          (Q'.le_of_lt (Q'.recipPos_pos _ _))
      · exact Q'.le_refl' 0
    · exact Q'.le_refl' 0
  · exact Q'.le_refl' 0

def cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
    (rho : Q') (later : Nat) : Q' :=
  listQMaxZero
    (fun pair : Nat × Nat =>
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction
        rho later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later))

theorem cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum_nonnegative
    (rho : Q') (later : Nat) :
    (0 : Q') ≤
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
        rho later := by
  unfold cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
  apply listQMaxZero_nonnegative
  intro pair
  exact cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction_nonnegative
    rho later pair.1 pair.2

theorem cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction_le_finiteMaximum
    {rho : Q'} {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    Q'.divPos
        (cutoffTwoHalfAmplitudeRelativeDefectMoment
          rho later left right)
        (cutoffTwoRawStationaryRowMass later right)
        (cutoffTwoRawStationaryRowMass_pos hright) ≤
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
        rho later := by
  have hpair : (left, right) ∈
      cartesian
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later) :=
    (mem_cartesian_iff _ _ (left, right)).2 ⟨hleft, hright⟩
  have hmax := le_listQMaxZero_of_mem
    (fun pair : Nat × Nat =>
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction
        rho later pair.1 pair.2)
    (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later)) hpair
  change cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction
      rho later left right ≤
    cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
      rho later at hmax
  unfold cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction at hmax
  rw [dif_pos hleft, dif_pos hright, dif_pos hforward] at hmax
  exact hmax

theorem cutoffTwoConditionalReverseForwardRatio_le_supportAwareDefectCeiling
    {rho : Q'}
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    Q'.divPos
        (cutoffTwoEdgeLoadConditionalKernel later right left)
        (cutoffTwoEdgeLoadConditionalKernel later left right)
        (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
          hleft hforward) ≤
      rho +
        cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
          rho later := by
  refine Q'.le_trans' _
    (Q'.divPos
      (cutoffTwoRawStationaryRowMass later left)
      (cutoffTwoRawStationaryRowMass later right)
      (cutoffTwoRawStationaryRowMass_pos hright)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward
            hleft hright hforward))
        (cutoffTwoStationaryWeightRatio_eqv_rawRowMassRatio hleft hright))
  · refine Q'.le_trans' _
      (rho +
        Q'.divPos
          (cutoffTwoHalfAmplitudeRelativeDefectMoment
            rho later left right)
          (cutoffTwoRawStationaryRowMass later right)
          (cutoffTwoRawStationaryRowMass_pos hright)) _
      (cutoffTwoRawStationaryRowMassRatio_le_rho_add_defectFraction
        hleft hright) ?_
    exact Q'.add_le_add_left rho _ _
      (cutoffTwoPositiveEdgeHalfAmplitudeDefectFraction_le_finiteMaximum
        hleft hright hforward)

/-! ## 4. Support-aware ceiling and cofinal payment compiler -/

def cutoffTwoSupportAwareDefectCeilingData
    (rho : Q') (hrho : (0 : Q') ≤ rho) (later : Nat) :
    CutoffTwoConditionalReverseForwardCeilingAt later
      (rho +
        cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
          rho later) where
  rho_nonnegative :=
    Q'.zero_le_add _ _ hrho
      (cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum_nonnegative
        rho later)
  ratio_le := fun _left hleft _right hright hforward =>
    cutoffTwoConditionalReverseForwardRatio_le_supportAwareDefectCeiling
      hleft hright hforward

def cutoffTwoNovelConditionalSupportAwareDefectLoad
    (rho : Q') (later source target : Nat) : Q' :=
  cutoffTwoNovelConditionalRatioCeilingLoad
    (rho +
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
        rho later)
    later source target

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_supportAwareDefect
    (rho : Q') (hrho : (0 : Q') ≤ rho) (later : Nat)
    (hdefect : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadFullStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalSupportAwareDefectLoad
              rho later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling
    (cutoffTwoSupportAwareDefectCeilingData rho hrho later)
  exact hdefect

structure CutoffTwoCofinalNovelSupportAwareDefectPayment : Type 1 where
  rho : Q'
  rho_nonnegative : (0 : Q') ≤ rho
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  defect_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalSupportAwareDefectLoad
            rho (anchor request) source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          (anchor request) source target

namespace CutoffTwoCofinalNovelSupportAwareDefectPayment

def toCofinalNovelConditionalRatioCeilingBound
    (bound : CutoffTwoCofinalNovelSupportAwareDefectPayment) :
    CutoffTwoCofinalNovelConditionalRatioCeilingBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  rho := fun request =>
    bound.rho +
      cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum
        bound.rho (bound.anchor request)
  local_ceiling := fun request =>
    cutoffTwoSupportAwareDefectCeilingData
      bound.rho bound.rho_nonnegative (bound.anchor request)
  ceiling_capacity := fun request => bound.defect_capacity request

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelSupportAwareDefectPayment) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelSupportAwareDefectPayment

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.no_cutoffTwoPositiveEdgeHalfAmplitudeHarnackAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.cutoffTwoHalfAmplitude_le_scaled_add_relativeDefect
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.cutoffTwoRawBoundaryMomentTerm_le_scaled_add_defectTerm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.cutoffTwoRawBoundaryMoment_le_scaled_add_defectMoment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.cutoffTwoRawStationaryRowMassRatio_le_rho_add_defectFraction
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.cutoffTwoConditionalReverseForwardRatio_le_supportAwareDefectCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_supportAwareDefect
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.CutoffTwoCofinalNovelSupportAwareDefectPayment.toCompletedStrictContractionData

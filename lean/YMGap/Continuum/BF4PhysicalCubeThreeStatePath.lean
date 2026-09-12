/-
# A physical two-edge path with an exactly missing direct edge

The single-face twice-spin-two probe moves to the fundamental cube and then
to the root. The existing difference-boundary summands give positive raw
edge floors at every cutoff K >= 2. In contrast the direct probe/root entry
vanishes: its face-(0,1) triangle would require the same boundary label to
equal both two and zero. At the fixed anchor the actual partition floor
gives positive normalized joint floors, without any cutoff counting.

This is a three-state support/weight certificate, not an all-vector gap.
-/

import YMGap.Continuum.BF4PhysicalCubeSeparatedChannel
import YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit

namespace YMGap.Continuum.BF4PhysicalCubeThreeStatePath

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeSeparatedChannel
open YMGap.Continuum.BF4PhysicalCubeBoundaryMask
open YMGap.Continuum.BF4PhysicalCubeKernelFactorization
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

theorem middle_zero_off (face : Nat) (hf : face ∉ centralLowerCubeFaceIds) :
    centralLowerCubeState face = 0 := by
  simp only [centralLowerCubeState, componentLabel, if_neg hf]

theorem probe_mate : centralLowerCubeEvenInwardMatePhysical probeState.val = centralLowerCubeState := by
  funext face
  by_cases hf : face ∈ centralLowerCubeFaceIds
  · simp only [centralLowerCubeEvenInwardMatePhysical, hf, ↓reduceIte,
      centralLowerCubeState, componentLabel, probeState, cutoffTwoSingleFaceTwoState]
    by_cases hone : face = 1 <;> simp [hone, evenInwardMateLabel]
  · rw [centralLowerCubeEvenInwardMatePhysical, if_neg hf]
    exact Eq.trans (probe_zero_off_cube face hf) (middle_zero_off face hf).symm

theorem middle_mate : centralLowerCubeEvenInwardMatePhysical centralLowerCubeState = zeroEdgeLabelling := by
  funext face
  by_cases hf : face ∈ centralLowerCubeFaceIds
  · simp [centralLowerCubeEvenInwardMatePhysical, centralLowerCubeState, componentLabel,
      hf, evenInwardMateLabel, zeroEdgeLabelling]
  · rw [centralLowerCubeEvenInwardMatePhysical, if_neg hf, middle_zero_off face hf]
    rfl

def probeRawFloor (w : Q') : Q' := differencePhysicalWeight w probeState.val
def rootRawFloor (w : Q') : Q' := differencePhysicalWeight w centralLowerCubeState

theorem probeRawFloor_pos {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < probeRawFloor w :=
  differencePhysicalWeight_pos hw _

theorem rootRawFloor_pos {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < rootRawFloor w :=
  differencePhysicalWeight_pos hw _

theorem probe_middle_floor {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 2 ≤ K) :
    probeRawFloor w ≤ centralPhysicalReflectedKernel w K 0 probeState.val centralLowerCubeState := by
  have h := differencePhysicalWeight_le_kernel hw K (by omega) probeState.val
    (fun face _ => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK) probe_zero_off_cube
  rw [probe_mate] at h
  exact h

theorem middle_root_floor {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) :
    rootRawFloor w ≤ centralPhysicalReflectedKernel w K 0 centralLowerCubeState zeroEdgeLabelling := by
  have h := differencePhysicalWeight_le_kernel hw K hK centralLowerCubeState
    (fun face _ => Nat.le_trans (centralLowerCubeState_le_one face) hK) middle_zero_off
  rw [middle_mate] at h
  exact h

/-- The contradiction uses one literal SU(2) fusion triangle on both halves. -/
theorem probe_root_mask_zero (boundary : EdgeLabelling) :
    cubeKernelAllowedB probeState.val zeroEdgeLabelling boundary = false := by
  cases h : cubeKernelAllowedB probeState.val zeroEdgeLabelling boundary with
  | false => rfl
  | true =>
      have hp : cubeBoundaryZeroB boundary = true ∧ cubeCornerAdmissibleB boundary = true ∧
          cubeEdgeAdmissibleB probeState.val boundary = true ∧
          cubeEdgeAdmissibleB zeroEdgeLabelling boundary = true := by
        simpa only [cubeKernelAllowedB, Bool.and_eq_true] using h
      have ha := List.all_eq_true.mp hp.2.2.1 (0, 1, 2) (by decide : (0, 1, 2) ∈ cubeDifferenceEdges)
      have hb := List.all_eq_true.mp hp.2.2.2 (0, 1, 2) (by decide : (0, 1, 2) ∈ cubeDifferenceEdges)
      change fusionOK 0 2 (boundary 2) = true at ha
      change fusionOK 0 0 (boundary 2) = true at hb
      rw [fusionOK_eq_true_iff] at ha hb
      have hlow : 2 ≤ boundary 2 := ha.1
      have hupp : boundary 2 ≤ 0 := hb.2.1
      omega

theorem probe_root_raw_zero (w : Q') (K : Nat) (hK : 2 ≤ K) :
    centralPhysicalReflectedKernel w K 0 probeState.val zeroEdgeLabelling ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (cubePhysicalKernel_eq_heat_overlap w K _ _
    (fun face => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK)
    (fun _ => Nat.zero_le K) probe_zero_off_cube (fun _ _ => rfl)) ?_
  have hoverlap : cubeBoundaryOverlap w K probeState.val zeroEdgeLabelling ≈ 0 := by
    unfold cubeBoundaryOverlap
    refine Q'.eqv_trans _ _ _ (listQSum_congr (fun boundary => ?_) _) (listQSum_zero _)
    rw [probe_root_mask_zero]
    exact Q'.mul_zero_eqv _
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hoverlap) (Q'.mul_zero_eqv _)

def normalizationFloor : Q' := Q'.mkPos 64 65 (by decide)
theorem normalizationFloor_pos : (0 : Q') < normalizationFloor := by decide

theorem normalized_floor (K : Nat) (left right : EdgeLabelling) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr : r ≤ centralPhysicalReflectedKernel anchorCoupling K 0 left right) :
    normalizationFloor * r ≤ centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0 left right := by
  let inv := (inversePartitionLimit (w := anchorCoupling) (by decide) (by decide)).approx K
  have hf : normalizationFloor ≤ inv := inversePartitionLimit_anchor_floor K
  have h := Q'.mul_le_mul_of_nonneg_left _ _ inv hr (Q'.le_trans' _ _ _ (by decide) hf)
  have hl := Q'.mul_le_mul_of_nonneg_right _ _ r hf hr0
  refine Q'.le_trans' _ _ _ hl (Q'.le_trans' _ _ _ h ?_)
  apply Q'.le_of_eqv
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_eqv_congr_left _ _ _ (inversePartitionLimit_approx (by decide) (by decide) K))

def probeJointFloor : Q' := normalizationFloor * probeRawFloor anchorCoupling
def rootJointFloor : Q' := normalizationFloor * rootRawFloor anchorCoupling

theorem probeJointFloor_pos : (0 : Q') < probeJointFloor :=
  Q'.mul_pos normalizationFloor_pos (probeRawFloor_pos (by decide))

theorem rootJointFloor_pos : (0 : Q') < rootJointFloor :=
  Q'.mul_pos normalizationFloor_pos (rootRawFloor_pos (by decide))

theorem probe_middle_joint_floor (K : Nat) (hK : 2 ≤ K) :
    probeJointFloor ≤ centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0
      probeState.val centralLowerCubeState :=
  normalized_floor K _ _ _ (Q'.le_of_lt (probeRawFloor_pos (by decide)))
    (probe_middle_floor (by decide) K hK)

theorem middle_root_joint_floor (K : Nat) (hK : 1 ≤ K) :
    rootJointFloor ≤ centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0
      centralLowerCubeState zeroEdgeLabelling :=
  normalized_floor K _ _ _ (Q'.le_of_lt (rootRawFloor_pos (by decide)))
    (middle_root_floor (by decide) K hK)

end YMGap.Continuum.BF4PhysicalCubeThreeStatePath

#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.middle_zero_off
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probe_mate
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.middle_mate
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probeRawFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.rootRawFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probeRawFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.rootRawFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probe_middle_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.middle_root_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probe_root_mask_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probe_root_raw_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.normalizationFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.normalizationFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.normalized_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probeJointFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.rootJointFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probeJointFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.rootJointFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.probe_middle_joint_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeThreeStatePath.middle_root_joint_floor

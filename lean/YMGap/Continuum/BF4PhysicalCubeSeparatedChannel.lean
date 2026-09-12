/-
# A reflected Gram channel that survives every vacuum-root correction

Use the existing single-face spin-two state and its explicit difference
boundary. Its half-amplitude is the positive heat product, while the vacuum
root's half-amplitude is exactly zero on this nonzero boundary. Therefore
one term of the actual Gram sum-of-squares gives a positive rational floor
for delta(probe) + c delta(root), for EVERY rational c.

The floor depends explicitly on w. This is nontrivial reflected norm, not
a transfer spectral gap, geometric time, or continuum construction.
-/

import YMGap.Continuum.BF4PhysicalCubeGNSData
import YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
import YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow
import YMGap.Continuum.FinitePositiveMaximumEntry

namespace YMGap.Continuum.BF4PhysicalCubeSeparatedChannel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FinitePositiveMaximumEntry
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem probe_zero_off_cube (face : Nat) (hf : face ∉ centralLowerCubeFaceIds) :
    cutoffTwoSingleFaceTwoState face = 0 := by
  unfold cutoffTwoSingleFaceTwoState
  rw [if_neg]
  intro heq
  exact hf (heq ▸ (by decide : 1 ∈ centralLowerCubeFaceIds))

/-- The previously named physical state, now on the all-spin cube carrier. -/
def probeState : CubeSectorState :=
  ⟨cutoffTwoSingleFaceTwoState, probe_zero_off_cube, by
    intro face _
    change (if face = 1 then 2 else 0) % 2 = 0
    split <;> decide⟩

def probeBoundary := cubeDifferenceBoundary probeState.val

def rootCorrectedSpan (c : Q') : CubeSpan := [(probeState, 1), (rootState, c)]

def channelFloor (w : Q') : Q' :=
  boundaryHeat w probeBoundary * (halfHeat w probeState.val * halfHeat w probeState.val)

private theorem product_pos (value : Nat → Q') (hv : ∀ n, (0 : Q') < value n) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by change (0 : Q') < 1; decide
  | id :: ids => Q'.mul_pos (hv id) (product_pos value hv ids)

theorem channelFloor_pos {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < channelFloor w :=
  Q'.mul_pos (product_pos _ (fun _ => coeffW_pos hw _) _)
    (Q'.mul_pos (product_pos _ (fun _ => coeffW_pos hw _) _)
      (product_pos _ (fun _ => coeffW_pos hw _) _))

theorem probeBoundary_mem (K : Nat) (hK : 2 ≤ K) : probeBoundary ∈ centralBoundaryChannels K 0 :=
  cubeDifferenceBoundary_mem K probeState.val
    (fun face _ => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK)

theorem probe_halfAmplitude (w : Q') (K : Nat) (hK : 2 ≤ K) :
    centralHalfAmplitude w K 0 probeState.val probeBoundary ≈ halfHeat w probeState.val :=
  halfAmplitude_eq_heat_of_multiplicity_one w K _ _
    (fun face => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK)
    (difference_source_multiplicity_one K probeState.val
      (fun face _ => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK) probe_zero_off_cube)

theorem probe_boundaryWeight (w : Q') (K : Nat) (hK : 2 ≤ K) :
    centralBoundaryWeight w K 0 probeBoundary ≈ boundaryHeat w probeBoundary :=
  boundaryWeight_eq_heat_of_multiplicity_one w K _
    (cubeDifferenceBoundary_bounded K probeState.val
      (fun face _ => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK))
    (difference_fixed_multiplicity_one K probeState.val
      (fun face _ => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK))

theorem root_halfAmplitude_zero (w : Q') (K : Nat) (hK : 2 ≤ K) :
    centralHalfAmplitude w K 0 rootState.val probeBoundary ≈ 0 :=
  centralHalfAmplitude_vacuum_eqv_zero_of_fixed_nonzero w K probeBoundary 2
    (by decide) (by decide) hK

theorem corrected_channel (w : Q') (c : Q') (K : Nat) (hK : 2 ≤ K) :
    channelLinear (rootCorrectedSpan c)
      (fun term channel => centralHalfAmplitude w K 0 term.1.val channel)
      (fun term => term.2) probeBoundary ≈ halfHeat w probeState.val := by
  change 1 * centralHalfAmplitude w K 0 probeState.val probeBoundary +
    (c * centralHalfAmplitude w K 0 rootState.val probeBoundary + 0) ≈ _
  have hz := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (root_halfAmplitude_zero w K hK))
    (Q'.mul_zero_eqv c)
  have hz' := Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) hz
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz')
    (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (probe_halfAmplitude w K hK)))

/-- A single nonnegative physical boundary term controls every rational
root correction. Nothing is estimated in the marginal norm here. -/
theorem rootCorrectedSpan_floor {w : Q'} (hw : (0 : Q') ≤ w) (c : Q') :
    channelFloor w ≤ form (kernel w) (rootCorrectedSpan c) (rootCorrectedSpan c) := by
  let K := termGramCutoff (rootCorrectedSpan c)
  have hK : 2 ≤ K := by change 2 ≤ 8; decide
  let a := fun channel => channelLinear (rootCorrectedSpan c)
    (fun term channel => centralHalfAmplitude w K 0 term.1.val channel) (fun term => term.2) channel
  have heq := Q'.eqv_trans _ _ _ (form_eq_physicalGram w (rootCorrectedSpan c))
    (weightedGramQuadratic_eq_sos (rootCorrectedSpan c) (centralBoundaryChannels K 0)
      (centralBoundaryWeight w K 0)
      (fun term channel => centralHalfAmplitude w K 0 term.1.val channel) (fun term => term.2))
  have hterm := le_listQSum_of_mem_nonnegative
    (fun channel => centralBoundaryWeight w K 0 channel * (a channel * a channel))
    (centralBoundaryChannels K 0) probeBoundary (probeBoundary_mem K hK)
    (fun channel hc => Q'.mul_nonneg _ _ (centralBoundaryWeight_nonnegative_on hw channel hc)
      (SumOfSquares.q_mul_self_nonneg (a channel)))
  have ha : a probeBoundary ≈ halfHeat w probeState.val := corrected_channel w c K hK
  have hselected : centralBoundaryWeight w K 0 probeBoundary *
      (a probeBoundary * a probeBoundary) ≈ channelFloor w :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (probe_boundaryWeight w K hK))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ ha)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hselected)
    (Q'.le_trans' _ _ _ hterm (Q'.ge_of_eqv heq))

end YMGap.Continuum.BF4PhysicalCubeSeparatedChannel

#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.probe_zero_off_cube
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.probeState
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.probeBoundary
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.rootCorrectedSpan
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.channelFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.channelFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.probeBoundary_mem
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.probe_halfAmplitude
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.probe_boundaryWeight
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.root_halfAmplitude_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.corrected_channel
#print axioms YMGap.Continuum.BF4PhysicalCubeSeparatedChannel.rootCorrectedSpan_floor

/-
# Bind exact decimation to the actual physical observable-transport budget

The scalar heat-semigroup theorem gives an explicit positive coupling

  w_eff = mkDecimate (decimationCorridorDepth w) w

inside the coefficient corridor for every `0 < w < 1`.  The physical
transport theorem, independently, scores the actual globally link-glued
cutoff-one block kernel at any positive candidate coarse coupling.

This module joins those interfaces.  It constructs the singleton physical
coupling atlas containing exactly `w_eff`, proves that transport matching
selects that coupling, and instantiates the literal fine-face covariance bound
with the actual physical kernel at `w_eff`.

The retained transport budget is not asserted to be small.  It is precisely
the finite rational quantity that must now be bounded to identify exact scalar
decimation with a controlled interacting four-dimensional observable step.

Constructive contract: exact rational powers, finite singleton selection, and
the existing physical kernel only; no choice, `Classical`, `native_decide`,
`sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor
import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion
import YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep

namespace YMGap.Continuum.CompactDualSlabObservableDecimationPhysicalTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The canonical singleton corridor atlas -/

/-- The explicit effective coupling supplied by the decimation corridor
theorem. -/
def observableDecimationCoupling (w : Q') : Q' :=
  mkDecimate (decimationCorridorDepth w) w

private theorem qpow_pos_local {w : Q'} (hw : (0 : Q') < w) :
    ∀ exponent : Nat, (0 : Q') < qpow w exponent
  | 0 => by
      show (0 : Q') < (1 : Q')
      decide
  | exponent + 1 => Q'.mul_pos (qpow_pos_local hw exponent) hw

theorem observableDecimationCoupling_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < observableDecimationCoupling w := by
  unfold observableDecimationCoupling mkDecimate
  exact qpow_pos_local hw (decimationCorridorDepth w)

theorem observableDecimationCoupling_lt_one
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    observableDecimationCoupling w < (1 : Q') := by
  have hanchor : observableDecimationCoupling w ≤ anchorCoupling := by
    unfold observableDecimationCoupling
    exact mkDecimate_decimationCorridorDepth_le_anchorCoupling hw0 hw1
  exact Q'.lt_of_le_of_lt hanchor (by
    unfold anchorCoupling
    decide)

theorem observableDecimationCoupling_coefficient
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    exteriorFaceCoefficient (observableDecimationCoupling w) 0 ≤
      anchorFaceCoefficient := by
  unfold observableDecimationCoupling
  exact mkDecimate_decimationCorridorDepth_zeroCoefficient_le hw0 hw1

/-- The one-candidate atlas dictated by the exact decimation theorem. -/
def observableDecimationAtlas
    (w : Q') (hw : (0 : Q') < w) : PositiveCouplingAtlas where
  head := observableDecimationCoupling w
  tail := []
  head_pos := observableDecimationCoupling_pos hw
  tail_pos := by
    intro candidate hcandidate
    exact absurd hcandidate List.not_mem_nil

@[simp] theorem observableDecimationAtlas_candidates
    (w : Q') (hw : (0 : Q') < w) :
    (observableDecimationAtlas w hw).candidates =
      [observableDecimationCoupling w] :=
  rfl

/-- On the singleton corridor atlas, the exact physical-transport argmin is
definitionally the decimated coupling. -/
theorem observableDecimationAtlas_selected
    (G : CutoffOneFaceGeometry)
    (w : Q') (hw : (0 : Q') < w) :
    physicalTransportMatchedCoupling
        G w (Q'.le_of_lt hw) (observableDecimationAtlas w hw) =
      observableDecimationCoupling w :=
  rfl

/-! ## 2. The actual physical kernel at the decimated coupling -/

/-- The literal fine covariance is controlled by the already-proved coarse
rate plus the exact actual-kernel budget at the canonical decimated coupling.

This is the first theorem in which the constructive decimation depth, the
actual globally link-glued physical kernel, and the literal face covariance
occur in one statement. -/
theorem observableDecimationPhysicalTransport_covariance_le
    (G : CutoffOneFaceGeometry)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
    let effective := observableDecimationCoupling w
    let heffective : (0 : Q') < effective :=
      observableDecimationCoupling_pos hw0
    let S := G.block.candidateScalePair w hg effective heffective
    let M := G.faceMap w hg effective heffective
    let K := physicalKernel S rfl heffective
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        (observablePullbackDefect K M + threePhysicalRemainderCost K) := by
  let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
  let effective := observableDecimationCoupling w
  let heffective : (0 : Q') < effective :=
    observableDecimationCoupling_pos hw0
  let S := G.block.candidateScalePair w hg effective heffective
  let M := G.faceMap w hg effective heffective
  exact
    cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_transportBudget
      S rfl heffective M
      (observableDecimationCoupling_lt_one (Q'.le_of_lt hw0) hw1)
      (observableDecimationCoupling_coefficient (Q'.le_of_lt hw0) hw1)

/-- Sharper centered form of the same canonical physical-decimation join.
The active error is now a covariance-to-covariance comparison on both sides
of the pushed-law replacement, rather than three separately paid moments. -/
theorem observableDecimationPhysicalCenteredTransport_covariance_le
    (G : CutoffOneFaceGeometry)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
    let effective := observableDecimationCoupling w
    let heffective : (0 : Q') < effective :=
      observableDecimationCoupling_pos hw0
    let S := G.block.candidateScalePair w hg effective heffective
    let M := G.faceMap w hg effective heffective
    let K := physicalKernel S rfl heffective
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        centeredPhysicalTransportBudget K M := by
  let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
  let effective := observableDecimationCoupling w
  let heffective : (0 : Q') < effective :=
    observableDecimationCoupling_pos hw0
  let S := G.block.candidateScalePair w hg effective heffective
  let M := G.faceMap w hg effective heffective
  exact
    cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_centeredBudget
      S rfl heffective M
      (observableDecimationCoupling_lt_one (Q'.le_of_lt hw0) hw1)
      (observableDecimationCoupling_coefficient (Q'.le_of_lt hw0) hw1)

/-- Cancellation-aware form of the canonical physical-decimation join.  The
pushed-law replacement cost is now displayed as the absolute value of the
exact connected signed root/target/joint cylinder-remainder combination. -/
theorem observableDecimationPhysicalConnectedTransport_covariance_le
    (G : CutoffOneFaceGeometry)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
    let effective := observableDecimationCoupling w
    let heffective : (0 : Q') < effective :=
      observableDecimationCoupling_pos hw0
    let S := G.block.candidateScalePair w hg effective heffective
    let M := G.faceMap w hg effective heffective
    let K := physicalKernel S rfl heffective
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        (centeredObservablePullbackDefect K M +
          Q'.abs (centeredCylinderRemainder K M)) := by
  let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
  let effective := observableDecimationCoupling w
  let heffective : (0 : Q') < effective :=
    observableDecimationCoupling_pos hw0
  let S := G.block.candidateScalePair w hg effective heffective
  let M := G.faceMap w hg effective heffective
  let K := physicalKernel S rfl heffective
  have htransport :=
    observableDecimationPhysicalCenteredTransport_covariance_le
      G w hw0 hw1
  have hremainder :=
    centeredPhysicalRemainderDefect_eqv_abs_centeredCylinderRemainder K M
  refine Q'.le_trans' _ _ _ htransport ?_
  unfold centeredPhysicalTransportBudget
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      (slabObservablePairedSupportGlobalAnchorRate
        S.coarse M.coarseRoot M.coarseTarget) _ _
      (Q'.add_eqv_congr_left
        (centeredObservablePullbackDefect K M) _ _ hremainder))

/-- Fully cancellation-aware canonical physical-decimation bound.  Both
transport errors are absolute values of explicit signed root/target/joint
combinations, leaving no opaque centered covariance defect in the active
finite-cutoff interface. -/
theorem observableDecimationPhysicalFullyConnectedTransport_covariance_le
    (G : CutoffOneFaceGeometry)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
    let effective := observableDecimationCoupling w
    let heffective : (0 : Q') < effective :=
      observableDecimationCoupling_pos hw0
    let S := G.block.candidateScalePair w hg effective heffective
    let M := G.faceMap w hg effective heffective
    let K := physicalKernel S rfl heffective
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        (Q'.abs (centeredObservablePullbackRemainder K M) +
          Q'.abs (centeredCylinderRemainder K M)) := by
  let hg : (0 : Q') ≤ w := Q'.le_of_lt hw0
  let effective := observableDecimationCoupling w
  let heffective : (0 : Q') < effective :=
    observableDecimationCoupling_pos hw0
  let S := G.block.candidateScalePair w hg effective heffective
  let M := G.faceMap w hg effective heffective
  let K := physicalKernel S rfl heffective
  have htransport :=
    observableDecimationPhysicalConnectedTransport_covariance_le
      G w hw0 hw1
  have hpullback :=
    centeredObservablePullbackDefect_eqv_abs_centeredPullbackRemainder K M
  refine Q'.le_trans' _ _ _ htransport ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      (slabObservablePairedSupportGlobalAnchorRate
        S.coarse M.coarseRoot M.coarseTarget) _ _
      (Q'.add_eqv_congr_right
        (centeredObservablePullbackDefect K M)
        (Q'.abs (centeredObservablePullbackRemainder K M))
        (Q'.abs (centeredCylinderRemainder K M)) hpullback))

#print axioms observableDecimationCoupling
#print axioms observableDecimationCoupling_pos
#print axioms observableDecimationCoupling_lt_one
#print axioms observableDecimationCoupling_coefficient
#print axioms observableDecimationAtlas
#print axioms observableDecimationAtlas_selected
#print axioms observableDecimationPhysicalTransport_covariance_le
#print axioms observableDecimationPhysicalCenteredTransport_covariance_le
#print axioms observableDecimationPhysicalConnectedTransport_covariance_le
#print axioms observableDecimationPhysicalFullyConnectedTransport_covariance_le

end YMGap.Continuum.CompactDualSlabObservableDecimationPhysicalTransport

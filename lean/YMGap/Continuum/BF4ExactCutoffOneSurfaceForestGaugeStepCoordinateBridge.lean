/-
# From the finite BF4 step certificate to proof-carrying ledger steps

This file identifies the decoded, proof-free certificate entry with the
corresponding certified translation step used by the geometric ledgers.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCertificate

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

def selectedTranslationStepRaw
    (step : SelectedTranslationStep 31) : RawSelectedTranslationStep where
  selected := step.selected
  multiplier := step.multiplier
  side := step.side
  multiplierOrientation := step.multiplierOrientation

private theorem rawSelectedTranslationStep_ext
    {left right : RawSelectedTranslationStep}
    (hselected : left.selected = right.selected)
    (hmultiplier : left.multiplier = right.multiplier)
    (hside : left.side = right.side)
    (horientation : left.multiplierOrientation =
      right.multiplierOrientation) :
    left = right := by
  cases left with
  | mk leftSelected leftMultiplier leftSide leftOrientation =>
      cases right with
      | mk rightSelected rightMultiplier rightSide rightOrientation =>
          cases hselected
          cases hmultiplier
          cases hside
          cases horientation
          rfl

private theorem selectedTranslationStep_ext
    {left right : SelectedTranslationStep 31}
    (hselected : left.selected = right.selected)
    (hmultiplier : left.multiplier = right.multiplier)
    (hside : left.side = right.side)
    (horientation : left.multiplierOrientation =
      right.multiplierOrientation) :
    left = right := by
  cases left with
  | mk leftSelected leftMultiplier leftSelectedLt leftMultiplierLt
      leftDistinct leftSide leftOrientation =>
      cases right with
      | mk rightSelected rightMultiplier rightSelectedLt rightMultiplierLt
          rightDistinct rightSide rightOrientation =>
          cases hselected
          cases hmultiplier
          cases hside
          cases horientation
          rfl

theorem selectedTranslationStepRaw_valid
    (step : SelectedTranslationStep 31) :
    rawSelectedTranslationStepValid 31
      (selectedTranslationStepRaw step) = true := by
  apply decide_eq_true
  exact ⟨step.selected_lt, step.multiplier_lt, step.distinct⟩

theorem selectedTranslationStepRaw_certify
    (step : SelectedTranslationStep 31)
    (hvalid : rawSelectedTranslationStepValid 31
      (selectedTranslationStepRaw step) = true) :
    (selectedTranslationStepRaw step).certify hvalid = step := by
  cases step
  rfl

private theorem encodedSelectedTranslationSideBit
    (selected multiplier side orientation : Nat)
    (hlow : selected + 32 * multiplier < 1024) :
    (selected + 32 * (multiplier + 32 * (side + 2 * orientation))) /
        1024 % 2 = side % 2 := by
  have hcode :
      selected + 32 * (multiplier + 32 * (side + 2 * orientation)) =
        (selected + 32 * multiplier) +
          1024 * (side + 2 * orientation) := by
    omega
  rw [hcode]
  have hdiv :
      ((selected + 32 * multiplier) +
          1024 * (side + 2 * orientation)) / 1024 =
        side + 2 * orientation := by
    simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt hlow]
  rw [hdiv, Nat.add_mul_mod_self_left]

private theorem encodedSelectedMultiplierOrientationBit
    (selected multiplier side orientation : Nat)
    (hlow : selected + 32 * multiplier < 1024)
    (hside : side < 2) (horientation : orientation < 2) :
    (selected + 32 * (multiplier + 32 * (side + 2 * orientation))) /
        2048 % 2 = orientation := by
  have hlow' :
      selected + 32 * multiplier + 1024 * side < 2048 := by
    omega
  have hcode :
      selected + 32 * (multiplier + 32 * (side + 2 * orientation)) =
        (selected + 32 * multiplier + 1024 * side) +
          2048 * orientation := by
    omega
  rw [hcode]
  have hdiv :
      ((selected + 32 * multiplier + 1024 * side) +
          2048 * orientation) / 2048 = orientation := by
    simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt hlow']
  rw [hdiv, Nat.mod_eq_of_lt horientation]

theorem decodeRawSelectedTranslationStep_selectedTranslationStepCode
    (step : SelectedTranslationStep 31) :
    decodeRawSelectedTranslationStep (selectedTranslationStepCode step) =
      selectedTranslationStepRaw step := by
  cases step with
  | mk selected multiplier selected_lt multiplier_lt distinct side orientation =>
      have hlow : selected + 32 * multiplier < 1024 := by
        omega
      apply rawSelectedTranslationStep_ext
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt selected_lt]
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        have hdiv :
            (selected + 32 * (multiplier + 32 *
              (selectedTranslationSideCode side +
                2 * selectedMultiplierOrientationCode orientation))) / 32 =
              multiplier + 32 * (selectedTranslationSideCode side +
                2 * selectedMultiplierOrientationCode orientation) := by
          simpa [Nat.add_mul_div_left,
            Nat.div_eq_of_lt selected_lt]
        rw [hdiv, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt multiplier_lt]
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        have hbit := encodedSelectedTranslationSideBit
          selected multiplier (selectedTranslationSideCode side)
            (selectedMultiplierOrientationCode orientation) hlow
        simp only [hbit]
        cases side <;> rfl
      · simp only [decodeRawSelectedTranslationStep,
          selectedTranslationStepCode, selectedTranslationStepRaw]
        have hside : selectedTranslationSideCode side < 2 := by
          cases side <;> decide
        have horientation :
            selectedMultiplierOrientationCode orientation < 2 := by
          cases orientation <;> decide
        have hbit := encodedSelectedMultiplierOrientationBit
          selected multiplier (selectedTranslationSideCode side)
            (selectedMultiplierOrientationCode orientation)
              hlow hside horientation
        simp only [hbit]
        cases orientation <;> rfl

theorem decodeRawSelectedTranslationStep_certify_stepCode
    (step : SelectedTranslationStep 31)
    (hvalid : rawSelectedTranslationStepValid 31
      (decodeRawSelectedTranslationStep
        (selectedTranslationStepCode step)) = true) :
    (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).certify hvalid = step := by
  have hdecode :=
    decodeRawSelectedTranslationStep_selectedTranslationStepCode step
  apply selectedTranslationStep_ext
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).selected = step.selected
    exact congrArg RawSelectedTranslationStep.selected hdecode
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).multiplier = step.multiplier
    exact congrArg RawSelectedTranslationStep.multiplier hdecode
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).side = step.side
    exact congrArg RawSelectedTranslationStep.side hdecode
  · change (decodeRawSelectedTranslationStep
      (selectedTranslationStepCode step)).multiplierOrientation =
        step.multiplierOrientation
    exact congrArg RawSelectedTranslationStep.multiplierOrientation hdecode

theorem decodedSelectedTranslationStepCoordinateCheck_stepCode
    (step : SelectedTranslationStep 31) :
    decodedSelectedTranslationStepCoordinateCheck
        (selectedTranslationStepCode step) =
      selectedTranslationStepCoordinateCheck
        (by decide : 0 < 31) step step.selected := by
  have hdecode :=
    decodeRawSelectedTranslationStep_selectedTranslationStepCode step
  have hvalid : rawSelectedTranslationStepValid 31
      (decodeRawSelectedTranslationStep
        (selectedTranslationStepCode step)) = true := by
    rw [hdecode]
    exact selectedTranslationStepRaw_valid step
  unfold decodedSelectedTranslationStepCoordinateCheck
  rw [dif_pos hvalid]
  have hcertify :
      (decodeRawSelectedTranslationStep
        (selectedTranslationStepCode step)).certify hvalid = step := by
    exact decodeRawSelectedTranslationStep_certify_stepCode step hvalid
  rw [hcertify]

theorem surfaceForestGaugeLedgerStepSelectedCoordinateCheck_true
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask) :
    selectedTranslationStepCoordinateCheck
      (by decide : 0 < 31) step step.selected = true := by
  have hcoverage :=
    binarySurfaceForestGaugeStepUniverseCoverageCheck_true
  unfold binarySurfaceForestGaugeStepUniverseCoverageCheck at hcoverage
  let maskEntry : { candidate // candidate ∈ binarySurfaceMasks } :=
    ⟨mask, hmask⟩
  have hmaskRow := List.all_eq_true.mp hcoverage maskEntry
    (List.mem_attach _ maskEntry)
  have hcodeDecision := List.all_eq_true.mp hmaskRow step hstep
  have hcode : selectedTranslationStepCode step ∈
      surfaceForestGaugeStepUniverseCodes :=
    of_decide_eq_true hcodeDecision
  have huniverse := surfaceForestGaugeStepUniverseCoordinateCheck_true
  unfold surfaceForestGaugeStepUniverseCoordinateCheck at huniverse
  have hdecoded := List.all_eq_true.mp huniverse
    (selectedTranslationStepCode step) hcode
  rw [decodedSelectedTranslationStepCoordinateCheck_stepCode] at hdecoded
  exact hdecoded

theorem surfaceForestGaugeLedgerStepSelectedCoordinate_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (step : SelectedTranslationStep 31)
    (hstep : step ∈ surfaceForestGaugeTranslationSteps mask hmask) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        [step] (orientedCoordinateQuaternion step.selected false))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          (selectedTranslationStepForwardWord step step.selected))) := by
  exact polyQuaternionCanonicalCoeffCheck_sound
    (surfaceForestGaugeLedgerStepSelectedCoordinateCheck_true
      mask hmask step hstep)

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.decodeRawSelectedTranslationStep_selectedTranslationStepCode
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.decodeRawSelectedTranslationStep_certify_stepCode
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.selectedTranslationStepRaw_valid
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.selectedTranslationStepRaw_certify
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.decodedSelectedTranslationStepCoordinateCheck_stepCode
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerStepSelectedCoordinateCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerStepSelectedCoordinate_coeffEqv

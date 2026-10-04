/-
# Projected spatial weight bound for the actual last-step conditional noise

The original one-step conditional noise is a supported nonnegative polynomial
and is independent of the spatial fringe after the transfer.  The spatial
fringe square can therefore be compared with the SAME original weighted mass
for this insertion.  Its coefficient depends on nome and width; no useful
noise-to-surviving-norm or changing-family estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
  (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass terminal_fringe_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
  (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
  (block_source_fringe_independent)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (spatialCertificate spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
  (lastStepRatioNoise lastStepRatioNoise_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyAdd
    quaternionBlockIndependent_polyMul quaternionBlockIndependent_polyNeg)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight terminalMessage weightedMass

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

/-- Compare the squared spatial fringe density against the same original
weighted mass for any certified supported insertion independent of the
fringe. This is the general-insertion form of the existing square lemma. -/
theorem spatialFringeMass_weighted_insert_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {p : RatPoly}
    (_hp : SupportedQuaternionBlocks (N width) p)
    (Pp : Certificate (N width) p)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p) :
    quaternionHaar (N width)
        (polyMul (polyMul (spatialFringeMass w K width)
          (spatialFringeMass w K width)) p) ≤
      spatialCeiling w width * weightedMass w K width p := by
  let Vbar := spatialFringeMass w K width
  let C := spatialCeiling w width
  have P := familyProject_certificate (N width) (fringeBlocks width)
    (fringeBlocks_lt width) (spatialWeight_supported w K width)
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
  have I := familyProject_interval (N width) (fringeBlocks width)
    (fringeBlocks_lt width) (spatialInterval hw0 hw1 K width (N width) (Nat.le_refl _))
  have hn := ((P.mul I.upper).mul Pp).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul Vbar Vbar) p)
        (polyMul (polyMul Vbar (polyAdd (cap C) (polyNeg Vbar))) p))
      (polySmul C (polyMul Vbar p)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
        (.mul (.mul (.var 0) (.add (.var 2) (.neg (.var 0)))) (.var 1)))
      (.mul (.var 2) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => Vbar | 1 => p | _ => cap C)).trans (cap_mul_left C _)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (N width) _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hid) (quaternionHaar_polySmul (N width) C _))
  have hpin : quaternionHaar (N width) (polyMul Vbar p) ≈
      weightedMass w K width p := by
    unfold weightedMass
    exact Q'.eqv_trans _ _ _
      (familyProject_selfAdjoint (N width) (fringeBlocks width) (fringeBlocks_lt width)
        (spatialWeight w K width) p)
      (haar_of_coeff ((familyProject_fixed (fringeBlocks width) p hfringe).mul_left _))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _ hpin)))

/-- After the actual one-step transfer, the conditional-noise insertion is
independent of every inactive fringe block. The source may use all input
coordinates; no extra locality premise is imposed on `phi`. -/
theorem lastStepRatioNoise_fringe_independent (w : Q') (K width d : Nat)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi)
    (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (lastStepRatioNoise w K width d phi) := by
  let a := terminalMessage w K width d
  have hA : QuaternionBlockIndependent i
      (originalBlockTransfer w K width 1 a) := by
    change QuaternionBlockIndependent i (transferStep w K width a)
    rw [terminalMessage_next w K width d]
    exact terminal_fringe_independent w K width (d+1) i hi
  have hb := block_source_fringe_independent w K width d 1 (by omega) hphi i hi
  have hphi2 : SupportedQuaternionBlocks (N width) (polyMul phi phi) :=
    supported_polyMul hphi hphi
  have hH := block_source_fringe_independent w K width d 1 (by omega) hphi2 i hi
  unfold lastStepRatioNoise blockNoise
  exact quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polyMul hA hH)
    (quaternionBlockIndependent_polyNeg (quaternionBlockIndependent_polyMul hb hb))

private theorem lastStepRatioNoise_supported (w : Q') (K width d : Nat)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    SupportedQuaternionBlocks (N width) (lastStepRatioNoise w K width d phi) := by
  let a := terminalMessage w K width d
  have ha := terminalMessage_supported w K width d
  have hphi2 : SupportedQuaternionBlocks (N width) (polyMul phi phi) :=
    supported_polyMul hphi hphi
  have hA := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) 1 ha
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) 1 (supported_polyMul ha hphi)
  have hH := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) 1 (supported_polyMul ha hphi2)
  unfold lastStepRatioNoise blockNoise
  exact supported_add (supported_polyMul hA hH)
    (support_neg (supported_polyMul hb hb))

/-- The literal original one-step conditional noise is controlled by the
projected spatial square against its own original weighted mass. The only
input condition is support of `phi` (besides the displayed original cutoff
guards); the coefficient depends on the fixed nome and width. -/
theorem lastStepRatioNoise_projected_weight_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) {phi : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi) :
    quaternionHaar (N width)
      (polyMul (polyMul (spatialFringeMass w K width)
        (spatialFringeMass w K width)) (lastStepRatioNoise w K width d phi)) ≤
      spatialCeiling w width *
        weightedMass w K width (lastStepRatioNoise w K width d phi) := by
  exact spatialFringeMass_weighted_insert_le hw0 hw1 K width hK
    (lastStepRatioNoise_supported w K width d hphi)
    (lastStepRatioNoise_certificate hw0 hw1 K width hK d hphi)
    (fun i hi => lastStepRatioNoise_fringe_independent w K width d hphi i hi)

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise.spatialFringeMass_weighted_insert_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise.lastStepRatioNoise_fringe_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise.lastStepRatioNoise_projected_weight_le

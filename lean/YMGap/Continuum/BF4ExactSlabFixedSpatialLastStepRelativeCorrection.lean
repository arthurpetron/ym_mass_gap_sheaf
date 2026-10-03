/-
The ORIGINAL last-step reciprocal correction is paid by the SAME surviving
spatial norm.  The projected spatial square is compared to, never identified
with, the original V-weighted square.  Degree onsets depend only on fixed
nome, width and tolerance, not heat cutoff, depth or signed source.  These
constants may deteriorate along a changing family; the leading paired score
and the signed Taylor difference remain unpaid.
-/
import YMGap.Continuum.QuaternionHaarRelativeReciprocalCorrection
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
import YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient (block_source_fringe_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection
open YMGap.Continuum.QuaternionHaarRelativeReciprocalCorrection
open YMGap.Continuum.ClusterCount (ofNat_nonneg)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight terminalMessage weightedMass

/-- A genuine comparison for the literal projected square, not Vbar²=V. -/
theorem spatialFringeMass_square_weight_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {b : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i b) :
    let Vbar := spatialFringeMass w K width
    quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul b b)) ≤
      spatialCeiling w width * weightedMass w K width (polyMul b b) := by
  dsimp only
  let Vbar := spatialFringeMass w K width
  let C := spatialCeiling w width
  let sq := polyMul b b
  have P := familyProject_certificate (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (spatialWeight_supported w K width)
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
  have I := familyProject_interval (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (spatialInterval hw0 hw1 K width (N width) (Nat.le_refl _))
  have hn := ((P.mul I.upper).mul (Certificate.square b hb)).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul Vbar Vbar) sq)
        (polyMul (polyMul Vbar (polyAdd (cap C) (polyNeg Vbar))) sq))
      (polySmul C (polyMul Vbar sq)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
        (.mul (.mul (.var 0) (.add (.var 2) (.neg (.var 0)))) (.var 1)))
      (.mul (.var 2) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => Vbar | 1 => sq | _ => cap C)).trans (cap_mul_left C _)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (N width) _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hid) (quaternionHaar_polySmul (N width) C _))
  have hpin : quaternionHaar (N width) (polyMul Vbar sq) ≈ weightedMass w K width sq := by
    unfold weightedMass
    exact Q'.eqv_trans _ _ _
      (familyProject_selfAdjoint (N width) (fringeBlocks width) (fringeBlocks_lt width)
        (spatialWeight w K width) sq)
      (haar_of_coeff ((familyProject_fixed (fringeBlocks width) sq
        (fun i hi => quaternionBlockIndependent_polyMul (hfringe i hi) (hfringe i hi))).mul_left _))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _ hpin)))

/-- Fixed-parameter coefficient; it does not contain the source norm or
terminal message mass.  No width/spacing uniformity is claimed. -/
def lastStepRelativeCorrectionCap (w : Q') (width : Nat) : Q' :=
  (relativeCap w 32 * relativeCap w 32) * spatialCeiling w width

theorem lastStepRelativeCorrectionCap_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) :
    (0 : Q') ≤ lastStepRelativeCorrectionCap w width :=
  Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _)
    (spatialInterval hw0 hw1 0 width (N width) (Nat.le_refl _)).nonnegative

/-- The actual terminal and projected weight supply every certificate.
The signed source is arbitrary, and a zero surviving norm needs no case split. -/
theorem original_block_lastStep_correction_relative_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let u := blockWindowUpper w K width n (r+1)
    let hu := blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)
    let Vbar := spatialFringeMass w K width
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu (k+1)
    quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e)) ≤
      (((Q'.ofNat (k+1)*Q'.ofNat (k+1))*
        ((mixRate hw0 hw1 width)^k*(mixRate hw0 hw1 width)^k))*
        lastStepRelativeCorrectionCap w width) * weightedMass w K width (polyMul b b) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  have hsn := activeBlocks_lt width s hs
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have win := blockWindowCertificates hw0 hw1 K width hhead n (r+1) (by omega)
  have ho : blockWindowLower w K width n (r+1) ≤ blockWindowUpper w K width n (r+1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hhead (n+(r+1)-1)))
  have R := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (remainderInterval (terminalMessage_supported w K width (n+(r+1)))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) ho win.1 win.2)
  have hrate := blockWindow_radius_pin hw0 hw1 K width hhead n (r+1)
  have R' := R.changeCap (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hrate)
    (Q'.mul_eqv_congr_left _ _ _ hrate))
  have P := terminalMessageRelativeBound hw0 hw1 K width hK (n+r) s hs hi hj
  have P' : QuaternionHaarRelativeAngularBound.RelativeBound (N width) (4*s+i) (4*s+j)
      (terminalMessage w K width (n+(r+1))) (relativeCap w 32) := by
    simpa only [Nat.add_assoc] using P
  have hstart := reciprocalScoreCorrection_relative_square_le (by omega) (by omega)
    (Certificate.square _ (spatialFringeMass_supported w K width))
    (terminalMessage_supported w K width (n+(r+1))) hb
    (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) P' win.2 R' k
  have hf : (0 : Q') ≤
      ((Q'.ofNat (k+1)*Q'.ofNat (k+1))*
        ((mixRate hw0 hw1 width)^k*(mixRate hw0 hw1 width)^k))*
        (relativeCap w 32*relativeCap w 32) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _) (SumOfSquares.q_mul_self_nonneg _))
      (SumOfSquares.q_mul_self_nonneg _)
  have hw := spatialFringeMass_square_weight_le hw0 hw1 K width hhead hb
    (block_source_fringe_independent w K width n (r+1) (by omega) hpsi)
  exact Q'.le_trans' _ _ _ hstart
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hw hf)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (by decide) (fun
          | 0 => (Q'.ofNat (k+1)*Q'.ofNat (k+1))*
              ((mixRate hw0 hw1 width)^k*(mixRate hw0 hw1 width)^k)
          | 1 => relativeCap w 32*relativeCap w 32
          | 2 => spatialCeiling w width
          | _ => weightedMass w K width (polyMul b b)))))

def lastStepRelativeCorrectionCutoff {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) (epsilon : Q') : Nat :=
  correctionSquareModulus (mixRate hw0 hw1 width) (lastStepRelativeCorrectionCap w width) epsilon

/-- One computed onset for every later degree, every late heat cutoff,
all incoming depths and every signed source, including zero-norm sources. -/
theorem original_block_lastStep_correction_relative_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (psi : RatPoly) (hpsi : SupportedQuaternionBlocks (N width) psi)
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : lastStepRelativeCorrectionCutoff hw0 hw1 width epsilon ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    let u := blockWindowUpper w K width n (r+1)
    let hu := blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)
    let Vbar := spatialFringeMass w K width
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu (k+1)
    quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul e e)) ≤
      epsilon * weightedMass w K width (polyMul b b) := by
  dsimp only
  have hb := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (r+1)
    (supported_polyMul (terminalMessage_supported w K width n) hpsi)
  have hn := weightedMass_nonnegative hw0 hw1 K width
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) (Certificate.square _ hb)
  exact Q'.le_trans' _ _ _
    (original_block_lastStep_correction_relative_square_le hw0 hw1 K width hK n r s hs hi hj psi hpsi k)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (correctionSquareModulus_bound (mixRate_nonnegative hw0 hw1 width)
        (mixRate_lt_one hw0 hw1 width) (lastStepRelativeCorrectionCap_nonnegative hw0 hw1 width)
        he k hk) hn)

#print axioms spatialFringeMass_square_weight_le
#print axioms lastStepRelativeCorrectionCap
#print axioms lastStepRelativeCorrectionCap_nonnegative
#print axioms original_block_lastStep_correction_relative_square_le
#print axioms lastStepRelativeCorrectionCutoff
#print axioms original_block_lastStep_correction_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRelativeCorrection

/-
# Actual finite-block conditional noise, without a normalized kernel

The full half-open original action supplies the positive weight for the
multi-head replica. Its three conditional moments are exactly the EXISTING
T^t g, T^t(g f), T^t(g f^2). Thus A H-b^2 has a constructed certificate on
the original surviving slice, for every finite t, including zero.

Weighted transfer symmetry also gives the exact variance-loss split
  ell(A H-b^2) = ell(g T^(2t)(g f^2)) - ell(b^2).
No comparison of this noise with the filtered norm is supplied. In particular
positivity of the noise does not bound the signed noise-minus-drift source,
produce a survival reserve, or justify a changing physical family.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
import YMGap.Continuum.SU2QuaternionHeadWindowBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds (halfOpenAction_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight spatialWeight weightedMass

/-- Literal polynomial-valued conditional variance on the actual output slice. -/
def blockNoise (w : Q') (K width t : Nat) (g f : RatPoly) : RatPoly :=
  let A := originalBlockTransfer w K width t g
  let b := originalBlockTransfer w K width t (polyMul g f)
  let H := originalBlockTransfer w K width t (polyMul g (polyMul f f))
  polyAdd (polyMul A H) (polyNeg (polyMul b b))

private def action (w : Q') (K width t : Nat) : RatPoly :=
  halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t

private theorem integral_pin (w : Q') (K width t : Nat) (g f : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)) (polyMul (polyMul g (action w K width t)) f))
      (originalBlockTransfer w K width t (polyMul g f)) :=
  (partialHaarHeads_congr (t*(N width))
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => g | 1 => action w K width t | _ => f))).trans
    (windowMessage_iterate (N width) (kineticWeight w K width)
      (spatialWeight w K width) t g f)

private theorem mass_pin (w : Q') (K width t : Nat) (g : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)) (polyMul g (action w K width t)))
      (originalBlockTransfer w K width t g) :=
  (partialHaarHeads_congr (t*(N width))
    ((RatPolyCoeffEqv.mul_one g).symm.mul_right (action w K width t))).trans
    (windowMessage_one (N width) (kineticWeight w K width)
      (spatialWeight w K width) t g)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hterm => Nat.le_trans (hp term hterm) (Nat.mul_le_mul_left 4 h)

/-- The certificate is PRODUCED from two full original finite windows and
their difference square. No sign premise on f, stationarity or inverse g. -/
def blockNoise_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g) :
    Certificate (N width) (blockNoise w K width t g f) := by
  let W := polyMul g (action w K width t)
  have hsize : (t+1)*(N width) = N width+t*(N width) := by
    rw [Nat.succ_mul]
    omega
  have hsmall : N width ≤ (t+1)*(N width) := by rw [Nat.succ_mul]; omega
  have ha := halfOpenAction_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) t
  have hW : SupportedQuaternionBlocks (N width+t*(N width)) W :=
    hsize ▸ supported_polyMul (support_mono hg hsmall) ha
  have hF : SupportedQuaternionBlocks (N width+t*(N width)) f :=
    support_mono hf (by omega)
  have GW : Certificate (N width+t*(N width)) W := by
    have GG := certificate_extend (t*(N width)) hg G
    have AA := halfOpenAction_certificate (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK) t
    exact GG.mul (hsize ▸ AA)
  have P := SU2QuaternionMultiHeadVarianceReplica.determinant_certificate
    (N width) (t*(N width)) W f hW hF GW
  have hpin : RatPolyCoeffEqv
      (SU2QuaternionMultiHeadVarianceReplica.determinant (t*(N width)) W f)
      (blockNoise w K width t g f) :=
    ((mass_pin w K width t g).mul (integral_pin w K width t g (polyMul f f))).add
      (RatPolyCoeffEqv.neg
        ((integral_pin w K width t g f).mul (integral_pin w K width t g f)))
  exact Certificate.ofCoeff hpin.symm P

/-- Full original output V is inserted once, after conditional integration. -/
theorem blockNoise_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g) :
    (0 : Q') ≤ weightedMass w K width (blockNoise w K width t g f) :=
  weightedMass_nonnegative hw0 hw1 K width hK
    (blockNoise_certificate hw0 hw1 K width hK t hg hf G)

/-- Same-source finite law of total variance. The first term is a literal
chronological endpoint square, NOT an independently supplied norm. -/
theorem blockNoise_variance_loss (w : Q') (K width t : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    weightedMass w K width (blockNoise w K width t g f) ≈
      weightedMass w K width (polyMul g
        (originalBlockTransfer w K width (2*t) (polyMul g (polyMul f f)))) -
      weightedMass w K width (polyMul
        (originalBlockTransfer w K width t (polyMul g f))
        (originalBlockTransfer w K width t (polyMul g f))) := by
  let H := originalBlockTransfer w K width t (polyMul g (polyMul f f))
  have hH : SupportedQuaternionBlocks (N width) H :=
    iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) t (supported_polyMul hg (supported_polyMul hf hf))
  have hsym := iterateStep_weighted_symmetric w K width t hg hH
  have hcomp : originalBlockTransfer w K width (2*t) (polyMul g (polyMul f f)) =
      originalBlockTransfer w K width t H := by
    unfold originalBlockTransfer H
    rw [show 2*t=t+t by omega]
    exact iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t t _
  have hfirst : weightedMass w K width (polyMul
      (originalBlockTransfer w K width t g) H) ≈
      weightedMass w K width (polyMul g
        (originalBlockTransfer w K width (2*t) (polyMul g (polyMul f f)))) :=
    Q'.eqv_trans _ _ _
      (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))
      (by rw [hcomp]; exact hsym)
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width
      ((RatPolyCoeffEqv.refl _).add (neg_smul _)))
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' hfirst
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) _)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide) (fun _ => weightedMass w K width (polyMul
              (originalBlockTransfer w K width t (polyMul g f))
              (originalBlockTransfer w K width t (polyMul g f))))))))

/-- Filtering cannot exceed the SAME longer-horizon endpoint square.
This is an upper norm comparison, not the missing survival lower bound. -/
theorem filteredSquare_le_endpointSquare {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g) :
    weightedMass w K width (polyMul
        (originalBlockTransfer w K width t (polyMul g f))
        (originalBlockTransfer w K width t (polyMul g f))) ≤
      weightedMass w K width (polyMul g
        (originalBlockTransfer w K width (2*t) (polyMul g (polyMul f f)))) :=
  Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (blockNoise_nonnegative hw0 hw1 K width hK t hg hf G)
      (Q'.le_of_eqv (blockNoise_variance_loss w K width t hg hf)))

/-- Positivity of the ACTUAL existing radius-two noise, not noise-minus-drift. -/
theorem original_noise_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ BF4ExactSlabFixedSpatialFilteredNoiseDrift.noise w K width n f := by
  have P := blockNoise_certificate hw0 hw1 K width hK 1
    (terminalMessage_supported w K width n) hf
    (terminalMessage_certificate hw0 hw1 K width hK n)
  have Q : Certificate (N width)
      (polyAdd (polyMul
        (originalBlockTransfer w K width 1 (terminalMessage w K width n))
        (originalBlockTransfer w K width 1 (polyMul (terminalMessage w K width n) (polyMul f f))))
        (polySmul (-1) (polyMul
          (originalBlockTransfer w K width 1 (polyMul (terminalMessage w K width n) f))
          (originalBlockTransfer w K width 1 (polyMul (terminalMessage w K width n) f))))) :=
    Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add (neg_smul _)).symm P
  exact weightedMass_nonnegative hw0 hw1 K width hK Q

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise.blockNoise_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise.blockNoise_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise.blockNoise_variance_loss
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise.filteredSquare_le_endpointSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise.original_noise_nonnegative

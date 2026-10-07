/-
# Uniform incoming reconstruction payment on the ORIGINAL finite carrier

The positive terminal window sharpens P(a) to 2*(1+kappa)*T1*(Ta)^2.
The ACTUAL outgoing reciprocal multiplier cancels (Ta)^2 as a cone
inequality, uniformly in its degree. Fringe projection and original
V-weighted transfer symmetry pay the remaining envelope by the SAME
incoming square. The computed coefficient depends on nome and width,
not K, terminal depth, source or outgoing degree.

This pays the differentiated incoming reconstruction error, not the
leading interacting noise. It is an ordinary finite V-weighted estimate,
not an OS-form estimate, an outgoing-relative bound, AF-uniform survival,
physical mass calibration or a continuum/QFT theorem. No source inverse,
new analytic premise, sorry or classical axiom is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonStretch comparisonStretch_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepCap stepCap_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient (block_source_fringe_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise (lastStepRatioNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepReconstructionNorm (original_step_one_upper_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise (spatialFringeMass_weighted_insert_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini (QuaternionBlockIndependent)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCap relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass

private theorem incoming_supported (w : Q') (K width n r : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width) (incomingNumerator w K width n r psi) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    r (supported_polyMul (terminalMessage_supported w K width n) hpsi)

private theorem weighted_certificate_le {blocks : Nat} {W p : RatPoly} {c : Q'}
    (MW : Certificate blocks W)
    (P : Certificate blocks (polyAdd (cap c) (polyNeg p))) :
    quaternionHaar blocks (polyMul W p) ≤ c*quaternionHaar blocks W := by
  have hn := (MW.mul P).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W p) (polyMul W (polyAdd (cap c) (polyNeg p))))
      (polySmul c W) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.var 0) (.add (.var 2) (.neg (.var 1)))))
      (.mul (.var 2) (.var 0)) (by decide)
      (fun | 0 => W | 1 => p | _ => cap c)).trans (cap_mul_left c W)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff hid) (quaternionHaar_polySmul blocks c W))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

private theorem terminal_window_stretch {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width n r : Nat) :
    comparisonStretch hw0 hw1 width * blockWindowLower w K width n r ≈
      blockWindowUpper w K width n r := by
  let f := kineticFloor w width
  let u := kineticCap w width
  let m := weightedMass w K width (terminalMessage w K width (n+r-1))
  let rf := Q'.recipPos f (kineticFloor_positive hw0 hw1 width)
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => u | 1 => rf | 2 => f | _ => m))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (u*m) _ _
        (Q'.mul_recipPos_eqv f (kineticFloor_positive hw0 hw1 width)))
      (Q'.mul_one_eqv (u*m)))

/-- Both windows and the outgoing multiplier are constructed from the actual
terminal. This ceiling holds for every outgoing degree l, without a source
inverse or dependence on the previous terminal mass. -/
def incomingEnvelope_reciprocal_cap_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (l : Nat) :
    let a := terminalMessage w K width (n+r)
    let G := blockReciprocal hw0 hw1 K width hK n (r+1) l
    Certificate (N width) (polyAdd
      (cap ((2*(1+comparisonStretch hw0 hw1 width))*stepCap w width))
      (polyNeg (polyMul (polyMul G G) (lastStepErrorBudgetMultiplier w K width a)))) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let G := blockReciprocal hw0 hw1 K width hK n (r+1) l
  have hAt : terminalMessage w K width (n+(r+1)) = A := by
    rw [show n+(r+1) = (n+r)+1 by omega, ← terminalMessage_next w K width (n+r)]
  have hG : SupportedQuaternionBlocks (N width) G :=
    reciprocal_supported (terminalMessage_supported w K width (n+(r+1))) _ _ l
  have horder : blockWindowLower w K width n (r+1) ≤ blockWindowUpper w K width n (r+1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+(r+1)-1)))
  have AG := multiplierSquareCertificate
    (terminalMessage_supported w K width (n+(r+1)))
    (blockWindowLower_positive hw0 hw1 K width hK n (r+1))
    (blockWindowUpper_positive hw0 hw1 K width hK n (r+1)) horder
    (blockWindowCertificates hw0 hw1 K width hK n (r+1) (by omega)).1
    (blockWindowCertificates hw0 hw1 K width hK n (r+1) (by omega)).2 l
  change Certificate (N width) (polyAdd polyOne (polyNeg
    (polyMul (polyMul (terminalMessage w K width (n+(r+1))) G)
      (polyMul (terminalMessage w K width (n+(r+1))) G)))) at AG
  rw [hAt] at AG
  have hkappa := Q'.le_of_lt (comparisonStretch_positive hw0 hw1 width)
  have P := lastStepErrorBudgetMultiplier_window_certificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+r))
    (terminalMessage_certificate hw0 hw1 K width hK (n+r))
    (blockWindowLower w K width n r) (blockWindowUpper w K width n r)
    (comparisonStretch hw0 hw1 width) hkappa (terminal_window_stretch hw0 hw1 K width n r)
    (blockWindowCertificates hw0 hw1 K width hK n r hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n r hdepth).2
  exact lastStepErrorBudgetMultiplier_reciprocal_cap_certificate hw0 hw1 K width hK
    (terminalMessage_supported w K width (n+r)) hG
    (comparisonStretch hw0 hw1 width) (stepCap w width) hkappa P
    (original_step_one_upper_certificate hw0 hw1 K width) AG

private theorem transferred_square_mass_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    {c : RatPoly} (hc : SupportedQuaternionBlocks (N width) c) :
    weightedMass w K width (transferStep w K width (polyMul c c)) ≤
      stepCap w width * weightedMass w K width (polyMul c c) := by
  let H := transferStep w K width (polyMul c c)
  let M := transferStep w K width polyOne
  let W := polyMul (spatialWeight w K width) (polyMul c c)
  have hsym := transferStep_weighted_symmetric w K width (supported_polyMul hc hc)
    (supported_one (N width))
  have hpin : weightedMass w K width (transferStep w K width (polyMul c c)) ≈
      weightedMass w K width (polyMul (polyMul c c) (transferStep w K width polyOne)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul H))) hsym
  have hcap : quaternionHaar (N width) (polyMul W M) ≤
      stepCap w width*quaternionHaar (N width) W :=
    weighted_certificate_le
      ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
        (Certificate.square c hc))
      (original_step_one_upper_certificate hw0 hw1 K width)
  have hleft : quaternionHaar (N width)
      (polyMul (polyMul (spatialWeight w K width) (polyMul c c))
        (transferStep w K width polyOne)) ≈
      weightedMass w K width (polyMul (polyMul c c) (transferStep w K width polyOne)) := by
    unfold weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) (polyMul c c) M)
  have hright : quaternionHaar (N width) W ≈ weightedMass w K width (polyMul c c) := by
    unfold weightedMass
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcap (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left (stepCap w width) _ _ hright))))

/-- Explicit fixed-nome/width coefficient, independent of both reciprocal
degrees, cutoff, depth and source. It is not uniform on a scaling trajectory. -/
def incomingEnvelopeCap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat) : Q' :=
  (2*(1+comparisonStretch hw0 hw1 width))*spatialCeiling w width *
    (stepCap w width*stepCap w width)

/-- The literal outgoing-weighted correction envelope is paid by the SAME
incoming V-weighted square. Null input is allowed; no transmitted norm is
used as a denominator. -/
theorem incomingErrorEnvelope_reciprocal_weight_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) (l : Nat) :
    let c := incomingNumerator w K width n r psi
    let Vbar := spatialFringeMass w K width
    let G := blockReciprocal hw0 hw1 K width hK n (r+1) l
    quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (incomingErrorEnvelope w K width n r psi)) ≤
      incomingEnvelopeCap hw0 hw1 width * weightedMass w K width (polyMul c c) := by
  dsimp only
  let c := incomingNumerator w K width n r psi
  let Vbar := spatialFringeMass w K width
  let G := blockReciprocal hw0 hw1 K width hK n (r+1) l
  let P := lastStepErrorBudgetMultiplier w K width (terminalMessage w K width (n+r))
  let H := transferStep w K width (polyMul c c)
  let d := (2*(1+comparisonStretch hw0 hw1 width))*stepCap w width
  have hc := incoming_supported w K width n r hpsi
  have hH := transferStep_supported w K width (supported_polyMul hc hc)
  have PH := transferStep_certificate hw0 hw1 K width hK (supported_polyMul hc hc)
    (Certificate.square c hc)
  have hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i H := by
    intro i hi
    have hproduct : H = SU2QuaternionProductHeatMarginals.productMap (N width) w K
        (activeBlocks width) (polyMul (spatialWeight w K width) (polyMul c c)) := by
      unfold H transferStep step SU2QuaternionProductHeatMarginals.productMap
        SU2QuaternionHaarKernelBound.kernelMap
      rw [BF4ExactSlabFixedSpatialKineticMarginals.kineticWeight_eq_indexedProduct]
      rfl
    rw [hproduct]
    have hi' := (BF4ExactSlabFixedSpatialFamilyFlow.fringeBlocks_mem_iff width i).mp hi
    exact SU2QuaternionProductHeatMarginals.productMap_independent_of_not_mem
      (N width) w K (activeBlocks width)
      (BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks_lt width) i hi'.1 hi'.2 _
      (supported_polyMul (spatialWeight_supported w K width) (supported_polyMul hc hc))
  have h1 := weighted_certificate_le ((Certificate.square Vbar
    (spatialFringeMass_supported w K width)).mul PH)
    (incomingEnvelope_reciprocal_cap_certificate hw0 hw1 K width hK n r hdepth l)
  have hpin : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G)) (incomingErrorEnvelope w K width n r psi))
      (polyMul (polyMul (polyMul Vbar Vbar) H) (polyMul (polyMul G G) P)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.var 2) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => Vbar | 1 => G | 2 => P | _ => H)
  have hd : (0 : Q') ≤ d := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt (comparisonStretch_positive hw0 hw1 width))))
    (stepCap_nonnegative hw0 hw1 width)
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ d
    (spatialFringeMass_weighted_insert_le hw0 hw1 K width hK hH PH hfringe) hd
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ (d*spatialCeiling w width)
    (transferred_square_mass_le hw0 hw1 K width hK hc)
    (Q'.mul_nonneg _ _ hd (spatialInterval hw0 hw1 K width (N width) (Nat.le_refl _)).nonnegative)
  have hright : d*(spatialCeiling w width*(stepCap w width*
      weightedMass w K width (polyMul c c))) ≈
      incomingEnvelopeCap hw0 hw1 width*weightedMass w K width (polyMul c c) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 1) (.var 3))))
      (.mul (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1))) (.var 3))
      (by decide) (fun
        | 0 => 2*(1+comparisonStretch hw0 hw1 width)
        | 1 => stepCap w width
        | 2 => spatialCeiling w width
        | _ => weightedMass w K width (polyMul c c))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff hpin))
    (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        (Q'.le_trans' _ _ _ h3
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)) (Q'.le_of_eqv hright))))))

/-- The Young factor belongs to the complete score consumer, not to the
pure correction envelope. This is a per-active-plane coefficient. -/
def incomingScoreRelativeCap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (eta : Q') (heta : (0 : Q') < eta) : Q' :=
  (1+Q'.recipPos eta heta)*(relativeCap w 32*relativeCap w 32)*
    incomingEnvelopeCap hw0 hw1 width

theorem incomingScoreRelativeCap_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (width : Nat)
    (eta : Q') (heta : (0 : Q') < eta) :
    (0 : Q') ≤ incomingScoreRelativeCap hw0 hw1 width eta heta := by
  have hd : (0 : Q') ≤ 2*(1+comparisonStretch hw0 hw1 width) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt (comparisonStretch_positive hw0 hw1 width)))
  have hv : (0 : Q') ≤ spatialCeiling w width :=
    (spatialInterval hw0 hw1 0 width (N width) (Nat.le_refl _)).nonnegative
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt (Q'.recipPos_pos eta heta)))
      (SumOfSquares.q_mul_self_nonneg (relativeCap w 32)))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hd hv)
      (SumOfSquares.q_mul_self_nonneg (stepCap w width)))

/-- Actual SAME-source score consumer with the explicit incoming-relative
payment. Its leading last-step interacting noise is retained, not bounded
or replaced by free heat. Outgoing degree l is arbitrary. -/
theorem original_lastStep_incomingRatio_relative_score_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi)
    (eta : Q') (heta : (0 : Q') < eta) (k l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let c := incomingNumerator w K width n r psi
    let b := transferStep w K width c
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let Vbar := spatialFringeMass w K width
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let M := polyMul (polyMul Vbar Vbar) (polyMul G G)
    let S := conditionalScore (4*s+i) (4*s+j) A b
    quaternionHaar (N width) (polyMul M (polyMul S S)) ≤
      (1+eta)*((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul (polyMul Vbar Vbar) (lastStepRatioNoise w K width (n+r) phi))) +
      ((mixRate hw0 hw1 width)^(2*k)*incomingScoreRelativeCap hw0 hw1 width eta heta)*
        weightedMass w K width (polyMul c c) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let c := incomingNumerator w K width n r psi
  let Vbar := spatialFringeMass w K width
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
  let M := polyMul (polyMul Vbar Vbar) (polyMul G G)
  let L := (1+Q'.recipPos eta heta)*(relativeCap w 32*relativeCap w 32)
  have hL : (0 : Q') ≤ L := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt (Q'.recipPos_pos eta heta)))
    (SumOfSquares.q_mul_self_nonneg (relativeCap w 32))
  have henv := Q'.mul_le_mul_of_nonneg_left _ _ L
    (incomingErrorEnvelope_reciprocal_weight_le hw0 hw1 K width hhead n r hdepth hpsi l) hL
  have hcoef : incomingScoreErrorCoefficient w K width n r psi M eta heta ≤
      incomingScoreRelativeCap hw0 hw1 width eta heta*weightedMass w K width (polyMul c c) :=
    Q'.le_trans' _ _ _ henv (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.mul_assoc_eqv L (incomingEnvelopeCap hw0 hw1 width) _)))
  have hgeo := Q'.mul_le_mul_of_nonneg_left _ _ ((mixRate hw0 hw1 width)^(2*k)) hcoef
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) (2*k))
  have h := original_lastStep_incomingRatio_reciprocal_score_le hw0 hw1 K width hK
    n r hdepth s hs hi hj hpsi
    (Certificate.square Vbar (spatialFringeMass_supported w K width)) eta heta k l
  exact Q'.le_trans' _ _ _ h (Q'.add_le_add (Q'.le_of_eqv (Q'.eqv_refl _))
    (Q'.le_trans' _ _ _ hgeo (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

/-- Explicit incoming-relative tolerance onset, independent of K, terminal
depth, source and outgoing degree. No source or transmitted norm is divided. -/
def incomingScoreRelativeCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (eta : Q') (heta : (0 : Q') < eta) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
    (incomingScoreRelativeCap hw0 hw1 width eta heta) epsilon

/-- The differentiated correction costs at most epsilon times the actual
incoming square, for every outgoing degree and supported source. This does
not pay the leading interacting noise or assert outgoing-relative survival. -/
theorem original_lastStep_incomingRatio_relative_score_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi)
    (eta : Q') (heta : (0 : Q') < eta) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (k l : Nat) (hk : incomingScoreRelativeCutoff hw0 hw1 width eta heta epsilon ≤ k) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let c := incomingNumerator w K width n r psi
    let b := transferStep w K width c
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let Vbar := spatialFringeMass w K width
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let M := polyMul (polyMul Vbar Vbar) (polyMul G G)
    let S := conditionalScore (4*s+i) (4*s+j) A b
    quaternionHaar (N width) (polyMul M (polyMul S S)) ≤
      (1+eta)*((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul (polyMul Vbar Vbar) (lastStepRatioNoise w K width (n+r) phi))) +
      epsilon*weightedMass w K width (polyMul c c) := by
  dsimp only
  let c := incomingNumerator w K width n r psi
  have hgeo := PositiveContractionResidual.geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    (incomingScoreRelativeCap_nonnegative hw0 hw1 width eta heta) hepsilon (2*k)
    (show PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
      (incomingScoreRelativeCap hw0 hw1 width eta heta) epsilon ≤ 2*k from by
      change PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
        (incomingScoreRelativeCap hw0 hw1 width eta heta) epsilon ≤ k at hk
      omega)
  have hpay := Q'.mul_le_mul_of_nonneg_right _ _ (weightedMass w K width (polyMul c c)) hgeo
    (weightedMass_nonnegative hw0 hw1 K width
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK)
      (Certificate.square c (incoming_supported w K width n r hpsi)))
  exact Q'.le_trans' _ _ _
    (original_lastStep_incomingRatio_relative_score_le hw0 hw1 K width hK
      n r hdepth s hs hi hj hpsi eta heta k l)
    (Q'.add_le_add (Q'.le_of_eqv (Q'.eqv_refl _)) hpay)

end YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.incomingEnvelope_reciprocal_cap_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.incomingEnvelopeCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.incomingErrorEnvelope_reciprocal_weight_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.incomingScoreRelativeCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.original_lastStep_incomingRatio_relative_score_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.incomingScoreRelativeCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.original_lastStep_incomingRatio_relative_score_tolerance

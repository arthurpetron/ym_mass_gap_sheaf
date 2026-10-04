/-
# Last-innovation dissipation in the ORIGINAL terminal law

For a=g_d, A=T a and bphi=T(a*phi), the positive last-step noise has
ell(N)+ell(bphi^2)=ell(a*g_(d+2)*phi^2). The constructed gap-two terminal
bracket gives a LINEAR (1+comparisonEta(d-1)) cleared dissipation bound.
For the actual incoming polynomial reciprocal phi_k=G_k*c, the certificate
(a*G_k)^2<=1 replaces ell((a*phi_k)^2) by ell(c^2), without an additive
error or an excitation inverse. All original spatial/kinetic factors and
the supplied source (hence its supplied OWN center) remain unchanged.

This is a local variance-loss upper comparison. It does not bound noise
relative to the surviving variance, identify Vbar^2 with V, or produce
changing-family survival, physical scaling or continuum/QFT closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison (filteredTerminalBracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (multiplierSquareCertificate)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage weightedMass kineticWeight spatialWeight

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -weightedMass w K width p :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem mass_difference (w : Q') (K width : Nat) (p q : RatPoly) :
    weightedMass w K width (polyAdd p (polyNeg q)) ≈
      weightedMass w K width p + -weightedMass w K width q :=
  Q'.eqv_trans _ _ _ (weightedMass_add w K width p (polyNeg q))
    (Q'.add_eqv_congr_left _ _ _ (mass_neg w K width q))

private theorem mass_order {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {p q : RatPoly}
    (P : Certificate (N width) (polyAdd q (polyNeg p))) :
    weightedMass w K width p ≤ weightedMass w K width q :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _
    (weightedMass_nonnegative hw0 hw1 K width hK P)
    (Q'.le_of_eqv (mass_difference w K width q p)))

private theorem negative_scale (l : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-l) p) (polyNeg (polySmul l p)) :=
  ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) l p).trans
    (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 l)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv l))) p))).symm

/-- Exact original noise endpoint; one spatial weight, unchanged source. -/
theorem lastStepNoise_endpoint_pin (w : Q') (K width d : Nat)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let bphi := transferStep w K width (polyMul a phi)
    weightedMass w K width (lastStepRatioNoise w K width d phi) +
      weightedMass w K width (polyMul bphi bphi) ≈
    weightedMass w K width (polyMul (polyMul a
      (terminalMessage w K width (d+2))) (polyMul phi phi)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := terminalMessage w K width (d+1)
  let p := polyMul a (polyMul phi phi)
  let bphi := transferStep w K width (polyMul a phi)
  have hA : transferStep w K width a = A := terminalMessage_next w K width d
  have hAA : transferStep w K width A = terminalMessage w K width (d+2) := by
    exact (terminalMessage_next w K width (d+1)).trans
      (congrArg (terminalMessage w K width) (by omega : d+1+1=d+2))
  have hsym := transferStep_weighted_symmetric w K width
    (supported_polyMul (terminalMessage_supported w K width d)
      (supported_polyMul hphi hphi)) (terminalMessage_supported w K width (d+1))
  change weightedMass w K width (polyMul A (transferStep w K width p)) ≈
    weightedMass w K width (polyMul p (transferStep w K width A)) at hsym
  rw [hAA] at hsym
  have he := weightedMass_congr w K width (lastStepRatioNoise_pin w K width d phi)
  rw [hA] at he
  have hm := Q'.eqv_trans _ _ _ he
    (mass_difference w K width (polyMul A (transferStep w K width p)) (polyMul bphi bphi))
  have hcancel : (weightedMass w K width (polyMul A (transferStep w K width p)) +
      -weightedMass w K width (polyMul bphi bphi)) +
      weightedMass w K width (polyMul bphi bphi) ≈
      weightedMass w K width (polyMul A (transferStep w K width p)) :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun
        | 0 => weightedMass w K width (polyMul A (transferStep w K width p))
        | _ => weightedMass w K width (polyMul bphi bphi))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hm)
    (Q'.eqv_trans _ _ _ hcancel (Q'.eqv_trans _ _ _ hsym
      (weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => a | 1 => phi | _ => terminalMessage w K width (d+2))))))

private theorem bracket_endpoint_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let U := (filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth).upper
    weightedMass w K width (polyMul (polyMul a (terminalMessage w K width (d+2)))
      (polyMul phi phi)) ≤ U*weightedMass w K width (polyMul (polyMul a phi) (polyMul a phi)) := by
  dsimp only
  let a := terminalMessage w K width d
  let g2 := terminalMessage w K width (d+2)
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth
  have P := J.upperCertificate.mul
    ((terminalMessage_certificate hw0 hw1 K width hK d).mul (Certificate.square phi hphi))
  have he : RatPolyCoeffEqv
      (polyMul (polyAdd (polySmul J.upper a) (polySmul (-1) g2))
        (polyMul a (polyMul phi phi)))
      (polyAdd (polySmul J.upper (polyMul (polyMul a phi) (polyMul a phi)))
        (polyNeg (polyMul (polyMul a g2) (polyMul phi phi)))) :=
    ((((cap_mul_left J.upper a).symm).add (neg_smul g2).symm).mul (.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 3) (.var 0)) (.neg (.var 1)))
          (.mul (.var 0) (.mul (.var 2) (.var 2))))
        (.add (.mul (.var 3) (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2))))
          (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))))
        (by decide) (fun | 0 => a | 1 => g2 | 2 => phi | _ => cap J.upper)).trans
        ((cap_mul_left J.upper _).add (.refl _)))
  exact Q'.le_trans' _ _ _ (mass_order hw0 hw1 K width hK (Certificate.ofCoeff he.symm P))
    (Q'.le_of_eqv (weightedMass_smul w K width J.upper _))

private theorem bracket_partition_lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d) :
    let a := terminalMessage w K width d
    let l := (filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth).lower
    l*weightedMass w K width (polyMul a a) ≤
      weightedMass w K width (polyMul a (terminalMessage w K width (d+2))) := by
  dsimp only
  let a := terminalMessage w K width d
  let g2 := terminalMessage w K width (d+2)
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth
  have he : RatPolyCoeffEqv (polyMul a (polyAdd g2 (polySmul (-J.lower) a)))
      (polyAdd (polyMul a g2) (polyNeg (polySmul J.lower (polyMul a a)))) :=
    ((RatPolyCoeffEqv.refl a).mul ((RatPolyCoeffEqv.refl g2).add
      ((negative_scale J.lower a).trans
        (RatPolyCoeffEqv.neg (cap_mul_left J.lower a).symm)))).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 2) (.var 0)))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.mul (.var 0) (.var 0)))))
        (by decide) (fun | 0 => a | 1 => g2 | _ => cap J.lower)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left J.lower _))))
  have h := mass_order hw0 hw1 K width hK (Certificate.ofCoeff he.symm
    ((terminalMessage_certificate hw0 hw1 K width hK d).mul J.lowerCertificate))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (weightedMass_smul w K width J.lower _)) h

private theorem bracket_upper_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d) :
    let J := filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth
    J.upper ≤ (1+comparisonEta hw0 hw1 width (d-1))*J.lower := by
  dsimp only
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth
  let eta := comparisonEta hw0 hw1 width (d-1)
  have h := Q'.add_le_add_right _ _ J.lower
    (terminalComparison_relative_width hw0 hw1 K width hK (d-1) 2 0)
  have heL : J.upper + -J.lower + J.lower ≈ J.upper :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun | 0 => J.upper | _ => J.lower)
  have heR : eta*J.lower+J.lower ≈ (1+eta)*J.lower :=
    poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
      (.mul (.add (.const 1) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => eta | _ => J.lower)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heL)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv heR))

/-- Arbitrary signed incoming ratio, with its noise retained. The two actual
partitions are cleared, and the factor is linear, not squared. -/
theorem lastStepNoise_dissipation_cleared {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let bphi := transferStep w K width (polyMul a phi)
    weightedMass w K width (polyMul a a)*
      (weightedMass w K width (lastStepRatioNoise w K width d phi)+
        weightedMass w K width (polyMul bphi bphi)) ≤
      (1+comparisonEta hw0 hw1 width (d-1))*
        (weightedMass w K width (polyMul A A)*
          weightedMass w K width (polyMul (polyMul a phi) (polyMul a phi))) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let g2 := terminalMessage w K width (d+2)
  let Zi := weightedMass w K width (polyMul a a)
  let Zo := weightedMass w K width (polyMul a g2)
  let B := weightedMass w K width (polyMul (polyMul a phi) (polyMul a phi))
  let E := weightedMass w K width (polyMul (polyMul a g2) (polyMul phi phi))
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth
  let F := 1+comparisonEta hw0 hw1 width (d-1)
  have hZi : (0 : Q') ≤ Zi := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square a (terminalMessage_supported w K width d))
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square (polyMul a phi) (supported_polyMul
      (terminalMessage_supported w K width d) hphi))
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one
    (comparisonEta_nonnegative hw0 hw1 width (d-1))
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ Zi
    (bracket_endpoint_le hw0 hw1 K width hK d hdepth hphi) hZi
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _ (Zi*B)
    (bracket_upper_le hw0 hw1 K width hK d hdepth) (Q'.mul_nonneg _ _ hZi hB)
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ F
    (Q'.mul_le_mul_of_nonneg_right _ _ B
      (bracket_partition_lower hw0 hw1 K width hK d hdepth) hB) hF
  have he1 : Zi*(J.upper*B) ≈ J.upper*(Zi*B) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => Zi | 1 => J.upper | _ => B)
  have he2 : (F*J.lower)*(Zi*B) ≈ F*((J.lower*Zi)*B) :=
    poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (by decide)
      (fun | 0 => F | 1 => J.lower | 2 => Zi | _ => B)
  have heZo : weightedMass w K width (polyMul A A) ≈ Zo := by
    have h := transferStep_weighted_symmetric w K width
      (terminalMessage_supported w K width d)
      (BF4ExactSlabFixedSpatialTransferStep.transferStep_supported w K width
        (terminalMessage_supported w K width d))
    change weightedMass w K width (polyMul A A) ≈
      weightedMass w K width (polyMul a (transferStep w K width A)) at h
    have hAA : transferStep w K width A = g2 :=
      (congrArg (transferStep w K width) (terminalMessage_next w K width d)).trans
        ((terminalMessage_next w K width (d+1)).trans
          (congrArg (terminalMessage w K width) (by omega : d+1+1=d+2)))
    rw [hAA] at h
    exact h
  have hfinal : Zi*E ≤ F*(Zo*B) := Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he1)
      (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he2) h3)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left Zi _ _ (lastStepNoise_endpoint_pin w K width d hphi)))
    (Q'.le_trans' _ _ _ hfinal (Q'.ge_of_eqv
      (Q'.mul_eqv_congr_left F _ _ (Q'.mul_eqv_congr_right _ _ B heZo))))

private theorem incoming_reconstruction_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let a := terminalMessage w K width (n+r)
    let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    weightedMass w K width (polyMul (polyMul a phi) (polyMul a phi)) ≤
      weightedMass w K width (polyMul c c) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hK n r k
  have hc : SupportedQuaternionBlocks (N width) c :=
    iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      r (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hwindow : blockWindowLower w K width n r ≤ blockWindowUpper w K width n r :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (BF4ExactSlabFixedSpatialTransferMixingRate.kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+r-1)))
  have P := (multiplierSquareCertificate (terminalMessage_supported w K width (n+r))
    (blockWindowLower_positive hw0 hw1 K width hK n r)
    (blockWindowUpper_positive hw0 hw1 K width hK n r) hwindow
    (blockWindowCertificates hw0 hw1 K width hK n r hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n r hdepth).2 k).mul (Certificate.square c hc)
  have he : RatPolyCoeffEqv
      (polyMul (polyAdd polyOne (polyNeg (polyMul (polyMul a G) (polyMul a G))))
        (polyMul c c))
      (polyAdd (polyMul c c)
        (polyNeg (polyMul (polyMul a (polyMul G c)) (polyMul a (polyMul G c))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
        (.mul (.var 2) (.var 2)))
      (.add (.mul (.var 2) (.var 2))
        (.neg (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 0) (.mul (.var 1) (.var 2))))))
      (by decide) (fun | 0 => a | 1 => G | _ => c)
  exact mass_order hw0 hw1 K width hK (Certificate.ofCoeff he.symm P)

private theorem bracket_upper_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (d : Nat) (hdepth : 1 ≤ d) :
    (0 : Q') ≤ (filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth).upper := by
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 2 hdepth
  let a := terminalMessage w K width d
  let g2 := terminalMessage w K width (d+2)
  have ha := terminalMessage_mass_positive hw0 hw1 K width hK d
  have hg := Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (d+2))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK J.upperCertificate
  have he : weightedMass w K width (polyAdd (polySmul J.upper a) (polySmul (-1) g2)) ≈
      J.upper*weightedMass w K width a + -weightedMass w K width g2 :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width J.upper a)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) g2)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))
  have hu := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))
  exact Q'.nonneg_of_mul_pos ha (Q'.le_trans' _ _ _ hg
    (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-- The actual incoming reciprocal supplies the endpoint ceiling directly.
The terminal upper scalar is constructed; no additive error is paid. -/
theorem lastStepRatioNoise_endpoint_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let a := terminalMessage w K width (n+r)
    let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    let bphi := transferStep w K width (polyMul a phi)
    weightedMass w K width (lastStepRatioNoise w K width (n+r) phi)+
      weightedMass w K width (polyMul bphi bphi) ≤
      (filteredTerminalBracket hw0 hw1 K width hK (n+r) 0 2 hdepth).upper*
        weightedMass w K width (polyMul c c) := by
  dsimp only
  have hphi := blockConditionalRatio_supported hw0 hw1 K width hK n r hp k
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (lastStepNoise_endpoint_pin w K width (n+r) hphi))
    (Q'.le_trans' _ _ _ (bracket_endpoint_le hw0 hw1 K width hK (n+r) hdepth hphi)
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (incoming_reconstruction_square_le hw0 hw1 K width hK n r hdepth hp k)
        (bracket_upper_nonnegative hw0 hw1 K width hK (n+r) hdepth)))

/-- Actual incoming reciprocal: no source-cap premise, and no additive
reconstruction error enters the retained noise+outgoing-norm budget. -/
theorem lastStepRatioNoise_dissipation_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let c := originalBlockTransfer w K width r (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n r psi k
    let bphi := transferStep w K width (polyMul a phi)
    weightedMass w K width (polyMul a a)*
      (weightedMass w K width (lastStepRatioNoise w K width (n+r) phi)+
        weightedMass w K width (polyMul bphi bphi)) ≤
      (1+comparisonEta hw0 hw1 width (n+r-1))*
        (weightedMass w K width (polyMul A A)*weightedMass w K width (polyMul c c)) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let F := 1+comparisonEta hw0 hw1 width (n+r-1)
  have hA := BF4ExactSlabFixedSpatialTransferStep.transferStep_supported w K width
    (terminalMessage_supported w K width (n+r))
  have hZo : (0 : Q') ≤ weightedMass w K width (polyMul A A) :=
    weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square A hA)
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one
    (comparisonEta_nonnegative hw0 hw1 width (n+r-1))
  exact Q'.le_trans' _ _ _
    (lastStepNoise_dissipation_cleared hw0 hw1 K width hK (n+r) hdepth
      (blockConditionalRatio_supported hw0 hw1 K width hK n r hp k))
    (Q'.mul_le_mul_of_nonneg_left _ _ F
      (Q'.mul_le_mul_of_nonneg_left _ _ (weightedMass w K width (polyMul A A))
        (incoming_reconstruction_square_le hw0 hw1 K width hK n r hdepth hp k) hZo) hF)

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lastStepNoise_endpoint_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lastStepNoise_dissipation_cleared
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lastStepRatioNoise_endpoint_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lastStepRatioNoise_dissipation_cleared

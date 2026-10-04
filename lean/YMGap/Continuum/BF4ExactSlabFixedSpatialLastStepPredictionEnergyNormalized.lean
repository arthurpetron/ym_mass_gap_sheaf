/-
# Actual last-step noise paid by the ORIGINAL incoming Dirichlet energy

The prediction-square identity is cleared against the actual odd incoming
partition ell(a*Ta) and outgoing square partition ell((Ta)^2). The terminal
bracket cancels its absolute scale, leaving the LINEAR cutoff-independent
factor 2*(1+comparisonEta(w,width,d-1)). The literal projected noise is paid
through spatialCeiling, not an identification of Vbar^2 with V.

No excitation norm is inverted. Signed and zero sources are allowed. This
does NOT make the incoming energy small, identify the outgoing square
partition with its Rayleigh denominator, control both signed Taylor terms,
or provide changing-family survival or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison (filteredTerminalBracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection (spatialFringeMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioNoise (lastStepRatioNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedNoise
  (lastStepRatioNoise_projected_weight_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass spatialWeight

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -weightedMass w K width p :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem negative_scale (l : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-l) p) (polyNeg (polySmul l p)) :=
  ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) l p).trans
    (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 l)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv l))) p))).symm

private theorem prediction_partition_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let l := (filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth).lower
    l*weightedMass w K width (polyMul a A) ≤
      weightedMass w K width (polyMul A A) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth
  have hA : transferStep w K width a = terminalMessage w K width (d+1) :=
    terminalMessage_next w K width d
  have P : Certificate (N width) (polyAdd A (polySmul (-J.lower) a)) := by
    simpa only [A, hA, Nat.add_zero] using J.lowerCertificate
  have PA : Certificate (N width) A := by
    change Certificate (N width) (transferStep w K width a)
    rw [hA]
    exact terminalMessage_certificate hw0 hw1 K width hK (d+1)
  have he : RatPolyCoeffEqv (polyMul A (polyAdd A (polySmul (-J.lower) a)))
      (polyAdd (polyMul A A) (polyNeg (polySmul J.lower (polyMul a A)))) :=
    ((RatPolyCoeffEqv.refl A).mul ((RatPolyCoeffEqv.refl A).add
      ((negative_scale J.lower a).trans
        (RatPolyCoeffEqv.neg (cap_mul_left J.lower a).symm)))).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 0) (.neg (.mul (.var 2) (.var 1)))))
        (.add (.mul (.var 0) (.var 0))
          (.neg (.mul (.var 2) (.mul (.var 1) (.var 0)))))
        (by decide) (fun | 0 => A | 1 => a | _ => cap J.lower)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left J.lower _))))
  have hn := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.ofCoeff he.symm (PA.mul P))
  have hm := Q'.eqv_trans _ _ _ (weightedMass_add w K width
      (polyMul A A) (polyNeg (polySmul J.lower (polyMul a A))))
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
      (mass_neg w K width (polySmul J.lower (polyMul a A)))
      (Q'.neg_eqv_congr _ _ (weightedMass_smul w K width J.lower (polyMul a A)))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv hm))

private theorem prediction_upper_relative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d) :
    let J := filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth
    J.upper ≤ (1+comparisonEta hw0 hw1 width (d-1))*J.lower := by
  dsimp only
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth
  have h := Q'.add_le_add_right _ _ J.lower
    (terminalComparison_relative_width hw0 hw1 K width hK (d-1) 1 0)
  have hl : J.upper + -J.lower + J.lower ≈ J.upper :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.var 0) (by decide) (fun | 0 => J.upper | _ => J.lower)
  have hr : comparisonEta hw0 hw1 width (d-1)*J.lower+J.lower ≈
      (1+comparisonEta hw0 hw1 width (d-1))*J.lower :=
    poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.var 1))
      (.mul (.add (.const 1) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => comparisonEta hw0 hw1 width (d-1) | _ => J.lower)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- The actual prediction square is retained. The absolute terminal-bracket
scale cancels against the two literal, distinct partitions. -/
theorem lastStepNoise_prediction_energy_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let q := lastStepPredictionError w K width d phi
    weightedMass w K width (polyMul a A)*
      (weightedMass w K width (lastStepRatioNoise w K width d phi)+
        weightedMass w K width (polyMul q q)) ≤
      (2*(1+comparisonEta hw0 hw1 width (d-1)))*
        (weightedMass w K width (polyMul A A)*energy w K width a phi) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let Z := weightedMass w K width (polyMul a A)
  let Zo := weightedMass w K width (polyMul A A)
  let E := energy w K width a phi
  let J := filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth
  let F := 1+comparisonEta hw0 hw1 width (d-1)
  have hZ : (0 : Q') ≤ Z := by
    have h := terminalPair_positive hw0 hw1 K width hK d (d+1)
    simpa only [Z, a, A, terminalMessage_next] using Q'.le_of_lt h
  have hE : (0 : Q') ≤ E := energy_nonnegative hw0 hw1 K width hK
    (terminalMessage_supported w K width d) hphi
    (terminalMessage_certificate hw0 hw1 K width hK d)
  have htwo : (0 : Q') ≤ (2 : Q') := by decide
  have hF : (0 : Q') ≤ F := Q'.zero_le_add _ _ Q'.zero_le_one
    (comparisonEta_nonnegative hw0 hw1 width (d-1))
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ Z
    (lastStepNoise_prediction_energy_le hw0 hw1 K width hK d hdepth hphi) hZ
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (2*(Z*E))
    (prediction_upper_relative hw0 hw1 K width hK d hdepth)
    (Q'.mul_nonneg _ _ htwo (Q'.mul_nonneg _ _ hZ hE))
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ (2*F)
    (Q'.mul_le_mul_of_nonneg_right _ _ E
      (prediction_partition_lower hw0 hw1 K width hK d hdepth) hE)
    (Q'.mul_nonneg _ _ htwo hF)
  have he1 : Z*((2*J.upper)*E) ≈ (2*(Z*E))*J.upper :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
      (.mul (.mul (.const 2) (.mul (.var 0) (.var 2))) (.var 1))
      (by decide) (fun | 0 => Z | 1 => J.upper | _ => E)
  have he2 : (2*(Z*E))*(F*J.lower) ≈ (2*F)*((J.lower*Z)*E) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.const 2) (.var 2)) (.mul (.mul (.var 3) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => Z | 1 => E | 2 => F | _ => J.lower)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he1)
    (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he2) h3)))

/-- The literal projected insertion required by the original angular
gradient consumer is paid by the SAME incoming energy. -/
theorem lastStepNoise_projected_prediction_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let U := (filteredTerminalBracket hw0 hw1 K width hK d 0 1 hdepth).upper
    let Vbar := spatialFringeMass w K width
    quaternionHaar (N width) (polyMul (polyMul Vbar Vbar)
      (lastStepRatioNoise w K width d phi)) ≤
      spatialCeiling w width*((2*U)*energy w K width a phi) := by
  dsimp only
  let q := lastStepPredictionError w K width d phi
  have hq := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square q (lastStepPredictionError_supported w K width d hphi))
  have hC : (0 : Q') ≤ spatialCeiling w width :=
    (spatialInterval hw0 hw1 0 width (N width) (Nat.le_refl _)).nonnegative
  have hn := Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hq)
    (lastStepNoise_prediction_energy_le hw0 hw1 K width hK d hdepth hphi)
  exact Q'.le_trans' _ _ _ (lastStepRatioNoise_projected_weight_le hw0 hw1 K width hK d hphi)
    (Q'.mul_le_mul_of_nonneg_left _ _ (spatialCeiling w width) hn hC)

/-- Cleared actual projected noise. The cutoff-independent comparison factor
still depends on nome/width/depth, and spatialCeiling depends on nome/width. -/
theorem lastStepNoise_projected_prediction_energy_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) (hdepth : 1 ≤ d)
    {phi : RatPoly} (hphi : SupportedQuaternionBlocks (N width) phi) :
    let a := terminalMessage w K width d
    let A := transferStep w K width a
    let Vbar := spatialFringeMass w K width
    weightedMass w K width (polyMul a A)*quaternionHaar (N width)
      (polyMul (polyMul Vbar Vbar) (lastStepRatioNoise w K width d phi)) ≤
      spatialCeiling w width*((2*(1+comparisonEta hw0 hw1 width (d-1)))*
        (weightedMass w K width (polyMul A A)*energy w K width a phi)) := by
  dsimp only
  let a := terminalMessage w K width d
  let A := transferStep w K width a
  let Z := weightedMass w K width (polyMul a A)
  let No := weightedMass w K width (lastStepRatioNoise w K width d phi)
  let q := lastStepPredictionError w K width d phi
  let C := spatialCeiling w width
  have hZ : (0 : Q') ≤ Z := by
    have h := terminalPair_positive hw0 hw1 K width hK d (d+1)
    simpa only [Z, a, A, terminalMessage_next] using Q'.le_of_lt h
  have hq := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square q (lastStepPredictionError_supported w K width d hphi))
  have hC : (0 : Q') ≤ C :=
    (spatialInterval hw0 hw1 0 width (N width) (Nat.le_refl _)).nonnegative
  have hn := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ Z (Q'.add_le_self_of_nonneg _ _ hq) hZ)
    (lastStepNoise_prediction_energy_cleared hw0 hw1 K width hK d hdepth hphi)
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ Z
    (lastStepRatioNoise_projected_weight_le hw0 hw1 K width hK d hphi) hZ
  have he : Z*(C*No) ≈ C*(Z*No) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => Z | 1 => C | _ => No)
  exact Q'.le_trans' _ _ _ hp (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ C hn hC))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized.lastStepNoise_prediction_energy_cleared
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized.lastStepNoise_projected_prediction_energy_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized.lastStepNoise_projected_prediction_energy_cleared

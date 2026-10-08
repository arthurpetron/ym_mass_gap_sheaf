/-
# Signed local Gram for the FULL original transfer score

Use the actual zero-mean two-source residual under the original one-step
action. Every other kinetic factor, spatial interaction and padded unit is
retained in a PRODUCED certified density independent of this output block.
The local heat prefix supplies its curvature/windows at the original onset.
No source quotient, extra marginal multiplier or Hessian sign is assumed.

The signed Fisher moment belongs to the original T1 law, NOT to Ta. This
finite estimate does not supply its useful scaling control, a completed OS
contraction, nontrivial continuum survival or a physical Hamiltonian gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin
import YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature
import YMGap.Continuum.SU2QuaternionConditionalZeroMeanSignedGram

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSignedGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepPairedResidual lastStepPairedResidual_mean_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin
  (lastStepAction action_integral_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (heatAt_symm)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (heatAt_floorCertificate)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (heatInterval)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare pairedScorePlus)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature (prefixFrozenCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica
open YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder (conditionalFisher)
open YMGap.Continuum.SU2QuaternionConditionalZeroMeanSignedGram

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Orient the SAME local factor with its surviving endpoint first. -/
def localPrefix (w : Q') (K width s : Nat) : RatPoly := heatAt (N width+s) s w K

/-- Output coefficients are lifted only AFTER the actual local first jets. -/
def localFrozenFirst (w : Q') (K width s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  firstJet (fun i => liftBoundary (N width) (u i))
    (fun i => pairedDerivativeAt (N width+s) i (localPrefix w K width s))

/-- Retain every ordered local second jet and the homogeneous cost inside I. -/
def localFrozenAugmentedSecond (w : Q') (K width s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  polyAdd
    (quadraticForm (fun i => liftBoundary (N width) (u i))
      (fun i j => pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))
    (polyMul (polyMul (cap (prefixCurvatureCost w))
      (threeSquare (fun i => liftBoundary (N width) (u i)))) (localPrefix w K width s))

/-- The negative score-mean square remains, for the original T1 source law. -/
def localSignedFisher (w : Q') (K width s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  conditionalFisher (N width) (localOutputDensity w K width s) (localPrefix w K width s)
    (localFrozenFirst w K width s u) (localFrozenAugmentedSecond w K width s u)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p := by
  intro t ht
  have := hp t ht
  omega

private theorem three_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

/-- Actual original score bound, for arbitrary incoming sources and frozen
output coefficients, under every certified tail insertion. All curvature,
kernel-window and spectator-density certificates are PRODUCED here. -/
theorem lastStep_local_signed_gram {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width s : Nat)
    (hs : s ∈ activeBlocks width) (hK : prefixFrozenCurvatureCutoff w ≤ K)
    {a c R : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    (PR : Certificate (N width) R) :
    let score := firstJet u (pairedScorePlus s (transferStep w K width a) (transferStep w K width c))
    let X := lastStepPairedResidual w K width a c
    quaternionHaar (N width) (polyMul R
      (polyMul (transferStep w K width polyOne) (polyMul score score))) ≤
    quaternionHaar (N width) (polyMul R
      (polyMul (partialHaarHeads (N width)
        (polyMul (lastStepAction w K width) (polyMul X X)))
        (localSignedFisher w K width s u))) := by
  dsimp only
  let q := localOutputDensity w K width s
  let P := localPrefix w K width s
  let d := localFrozenFirst w K width s u
  let dd := localFrozenAugmentedSecond w K width s u
  let X := lastStepPairedResidual w K width a c
  let score := firstJet u (pairedScorePlus s (transferStep w K width a) (transferStep w K width c))
  let v := fun i => liftBoundary (N width) (u i)
  have hslot : s < N width := activeBlocks_lt width s hs
  have hb : 1 < N width+N width := by omega
  have hout : N width+s < N width+N width := by omega
  have hhead : headCutoff w ≤ K := by unfold prefixFrozenCurvatureCutoff at hK; omega
  have hv : ∀ i, SupportedQuaternionBlocks (N width+N width) (v i) :=
    fun i => lift_supported (hu i) (N width)
  have hp := (heatInterval hout (by omega : s < N width+N width) hw0 hw1 K)
  have hd : SupportedQuaternionBlocks (N width+N width) d :=
    three_supported (fun i => supported_polyMul (hv i) (pairedDerivativeAt_supported hout i hp.support))
  have hsecond : SupportedQuaternionBlocks (N width+N width)
      (quadraticForm v (fun i j => pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j P))) :=
    three_supported (fun i => three_supported (fun j =>
      supported_polyMul (supported_polyMul (hv i) (hv j))
        (pairedDerivativeAt_supported hout i (pairedDerivativeAt_supported hout j hp.support))))
  have hnorm := three_supported (fun i => supported_polyMul (hv i) (hv i))
  have hdd : SupportedQuaternionBlocks (N width+N width) dd :=
    supported_add hsecond (supported_polyMul
      (supported_polyMul (polySmul_supported (supported_one _) (prefixCurvatureCost w)) hnorm) hp.support)
  have hX : SupportedQuaternionBlocks (N width+N width) X :=
    supported_add
      (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
        (support_mono hc (by omega)))
      (support_neg (supported_polyMul
        (lift_supported (transferStep_supported w K width hc) (N width))
        (support_mono ha (by omega))))
  have hW : RatPolyCoeffEqv (polyMul q P) (lastStepAction w K width) :=
    ((heatAt_symm (N width+s) s w K).mul_left q).trans
      (localOutputDensity_action_pin w K width s hs)
  have hzero : RatPolyCoeffEqv (momentB (N width) q P X) polyZero :=
    (partialHaarHeads_congr (N width) (hW.mul_right X)).trans
      (lastStepPairedResidual_mean_zero w K width a c)
  have hclear : RatPolyCoeffEqv
      (polyAdd (polyMul P dd) (polyNeg (polyMul d d)))
      (frozenCurvatureAt (N width+s) (prefixCurvatureCost w) P v) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 2) (.mul (.mul (.var 3) (.var 4)) (.var 0))))
        (.neg (.mul (.var 1) (.var 1))))
      (.add (.mul (.var 3) (.mul (.var 4) (.mul (.var 0) (.var 0))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun
        | 0 => P | 1 => d
        | 2 => quadraticForm v (fun i j => pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j P))
        | 3 => cap (prefixCurvatureCost w) | _ => threeSquare v)
  let C := Certificate.ofCoeff hclear
    (heatAt_frozen_curvature_certificate hb ⟨N width+s,hout⟩ ⟨s,by omega⟩
      (by simp only; omega) hw0 hw1 K hK v hv)
  have hm := headFloor_positive hw0 hw1
  have hle : headFloor w ≤ prefixCap w+headFloor w :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (headFloor w) _ hp.nonnegative)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hupper := Q'.pos_of_lt_of_le hm hle
  have hgram := conditional_zero_mean_signed_score_bound (N width) (N width) q P d dd X R
    (localOutputDensity_supported w K width s) hp.support hd hdd hX
    (localOutputDensity_certificate hw0 hw1 K hhead width s) C PR hm hupper hle
    (heatAt_floorCertificate hout (by omega : s < N width+N width) hw0 hw1 K hhead)
    (hp.raise (headFloor w) (Q'.le_of_lt hm)).upper hzero
  have hA : RatPolyCoeffEqv (momentA (N width) q P) (transferStep w K width polyOne) :=
    (partialHaarHeads_congr (N width) hW).trans
      ((partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_one (lastStepAction w K width)).symm).trans
        (action_integral_pin w K width polyOne))
  have hE : RatPolyCoeffEqv (momentE (N width) q d X) score :=
    local_frozen_score_integral_pin w K width s q P
      (localOutputDensity_independent w K width s hs) hW ha hc u
  have hV : RatPolyCoeffEqv (momentV (N width) q P X)
      (partialHaarHeads (N width) (polyMul (lastStepAction w K width) (polyMul X X))) :=
    partialHaarHeads_congr (N width) (hW.mul_right (polyMul X X))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((hA.mul (hE.mul hE)).mul_left R).symm))
    (Q'.le_trans' _ _ _ hgram
      (Q'.le_of_eqv (haar_of_coeff ((hV.mul_right _).mul_left R))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSignedGram

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSignedGram.lastStep_local_signed_gram

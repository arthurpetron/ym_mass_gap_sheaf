/-
# Matched terminal marginal in the original last-step signed Gram

The selected output heat sees the positive lower terminal message as part of
its independent density. Consequently its conditional moments differentiate
the SAME marginal A = T(a) used by the incoming reciprocal. The curvature
cost and all nine ordered second jets remain signed. This is a finite score
inequality, not a signed-Fisher scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionConditionalFisherOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin
  (lastStepAction action_integral_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepPairedResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalPairedScorePin
  (local_frozen_score_integral_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSignedGram
  (localPrefix localFrozenFirst localFrozenAugmentedSecond)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalMarginalJets
  (paired_congr paired_partial paired_product integrate_threeSum integrate_add
   integrate_quadratic pull_coefficient lift_threeSquare local_factor_pin)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (supported_upper_independent heatAt_symm)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (partialHaarHeads_add partialHaarHeads_neg partialHaarHeads_smul)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
  (partialHaarHeads_congr partialHaarHeads_mul_lift)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.QuaternionHaarSquareCertificate
  (Certificate haar_of_coeff supported_add supported_one)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (pairedScorePlus threeSquare)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
  (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr threeSum_mul_left)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica
  (momentA momentB momentD momentV momentE momentG)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder
  (conditionalScore conditionalNoise conditionalFisher conditional_signed_score_bound)
open YMGap.Continuum.QuaternionHaarClearedThreeGram
  (centeredScore centeredNoise centeredFisher)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
  (prefixFrozenCurvatureCutoff nearFlatPrefixFrozenCurvatureCutoff nearFlatPrefixCurvatureCost)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (heatInterval)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (heatAt_floorCertificate)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature
  (heatAt_frozen_curvature_certificate heatAt_frozen_curvature_nearFlat_certificate frozenCurvatureAt)
open YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct
  (positiveFromLowerWindow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage

/-- Insert any lower source without changing the selected output heat. -/
def sourceDensity (w : Q') (K width s : Nat) (a : RatPoly) : RatPoly :=
  polyMul (localOutputDensity w K width s) a

def sourceFrozenFirst (w : Q') (K width s : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  localFrozenFirst w K width s u

def sourceFrozenAugmentedSecond (w : Q') (K width s : Nat)
    (u : Fin 3 → RatPoly) : RatPoly :=
  localFrozenAugmentedSecond w K width s u

private def sourceFrozenAugmentedSecondAt (w C : Q') (K width s : Nat)
    (u : Fin 3 → RatPoly) : RatPoly :=
  polyAdd
    (quadraticForm (fun i => liftBoundary (N width) (u i))
      (fun i j => pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))
    (polyMul (polyMul (cap C) (threeSquare (fun i => liftBoundary (N width) (u i))))
      (localPrefix w K width s))

/-- Frozen output derivative of the matched marginal T(a). -/
def sourceMarginalFirst (w : Q') (K width s : Nat) (a : RatPoly)
    (u : Fin 3 → RatPoly) : RatPoly :=
  firstJet u (fun i => pairedDerivativeAt s i (transferStep w K width a))

/-- All nine ordered output Hessian entries of the matched marginal T(a). -/
def sourceMarginalSecond (w : Q') (K width s : Nat) (a : RatPoly)
    (u : Fin 3 → RatPoly) : RatPoly :=
  quadraticForm u (fun i j => pairedDerivativeAt s i
    (pairedDerivativeAt s j (transferStep w K width a)))

private theorem source_factor (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (a : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (sourceDensity w K width s a) (localPrefix w K width s))
      (polyMul (lastStepAction w K width) a) := by
  have hreorder : RatPolyCoeffEqv
      (polyMul (polyMul (localOutputDensity w K width s) a)
        (localPrefix w K width s))
      (polyMul (polyMul (localOutputDensity w K width s)
        (localPrefix w K width s)) a) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => localOutputDensity w K width s
        | 1 => a | _ => localPrefix w K width s)
  exact hreorder.trans ((local_factor_pin w K width s hs).mul_right a)

private theorem source_mass (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (a : RatPoly) :
    RatPolyCoeffEqv (momentA (N width) (sourceDensity w K width s a)
      (localPrefix w K width s)) (transferStep w K width a) :=
  (partialHaarHeads_congr (N width) (source_factor w K width s hs a)).trans
    (action_integral_pin w K width a)

private theorem source_independent (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) :
    QuaternionBlockIndependent (N width+s) (sourceDensity w K width s a) :=
  quaternionBlockIndependent_polyMul
    (localOutputDensity_independent w K width s hs)
    (supported_upper_independent ha s)

private theorem source_first_cell (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (i : Fin 3) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (sourceDensity w K width s a)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))
      (pairedDerivativeAt s i (transferStep w K width a)) := by
  have hq := source_independent w K width s hs ha
  have hfactor := source_factor w K width s hs a
  have h : RatPolyCoeffEqv
      (polyMul (sourceDensity w K width s a)
        (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))
      (pairedDerivativeAt (N width+s) i (polyMul (lastStepAction w K width) a)) :=
    (paired_product (N width+s) i _ _ hq).symm.trans
      (paired_congr (N width+s) i hfactor)
  exact (partialHaarHeads_congr (N width) h).trans
    ((paired_partial (N width) s i (polyMul (lastStepAction w K width) a)).symm.trans
      (paired_congr s i (action_integral_pin w K width a)))

private theorem source_second_cell (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (i j : Fin 3) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (sourceDensity w K width s a)
          (pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j (localPrefix w K width s)))))
      (pairedDerivativeAt s i
        (pairedDerivativeAt s j (transferStep w K width a))) := by
  have hq := source_independent w K width s hs ha
  have hfactor := source_factor w K width s hs a
  have hproduct : RatPolyCoeffEqv
      (pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j
          (polyMul (sourceDensity w K width s a) (localPrefix w K width s))))
      (polyMul (sourceDensity w K width s a)
        (pairedDerivativeAt (N width+s) i
          (pairedDerivativeAt (N width+s) j (localPrefix w K width s)))) :=
    (paired_congr (N width+s) i
      (paired_product (N width+s) j _ _ hq)).trans
      (paired_product (N width+s) i _ _ hq)
  have h : RatPolyCoeffEqv
      (polyMul (sourceDensity w K width s a)
        (pairedDerivativeAt (N width+s) i
          (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))
      (pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j (polyMul (lastStepAction w K width) a))) :=
    hproduct.symm.trans (paired_congr (N width+s) i
      (paired_congr (N width+s) j hfactor))
  have hpartial : RatPolyCoeffEqv
      (pairedDerivativeAt s i (pairedDerivativeAt s j
        (partialHaarHeads (N width) (polyMul (lastStepAction w K width) a))))
      (partialHaarHeads (N width)
        (pairedDerivativeAt (N width+s) i
          (pairedDerivativeAt (N width+s) j
            (polyMul (lastStepAction w K width) a)))) :=
    (paired_congr s i
      (paired_partial (N width) s j (polyMul (lastStepAction w K width) a))).trans
      (paired_partial (N width) s i
        (pairedDerivativeAt (N width+s) j (polyMul (lastStepAction w K width) a)))
  exact (partialHaarHeads_congr (N width) h).trans
    (hpartial.symm.trans (paired_congr s i
      (paired_congr s j (action_integral_pin w K width a))))

private theorem source_first_term (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (i : Fin 3) (ui : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (sourceDensity w K width s a)
          (polyMul (liftBoundary (N width) ui)
            (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))))
      (polyMul ui (pairedDerivativeAt s i (transferStep w K width a))) := by
  have hmove : RatPolyCoeffEqv
      (polyMul (sourceDensity w K width s a)
        (polyMul (liftBoundary (N width) ui)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))
      (polyMul (liftBoundary (N width) ui)
        (polyMul (sourceDensity w K width s a)
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun
        | 0 => sourceDensity w K width s a
        | 1 => liftBoundary (N width) ui
        | _ => pairedDerivativeAt (N width+s) i (localPrefix w K width s))
  exact (partialHaarHeads_congr (N width) hmove).trans
    ((pull_coefficient (N width) ui _).trans
      ((source_first_cell w K width s hs ha i).mul_left ui))

private theorem source_second_term (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (i j : Fin 3) (ui uj : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (sourceDensity w K width s a)
          (polyMul (polyMul (liftBoundary (N width) ui) (liftBoundary (N width) uj))
            (pairedDerivativeAt (N width+s) i
              (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))))
      (polyMul (polyMul ui uj)
        (pairedDerivativeAt s i
          (pairedDerivativeAt s j (transferStep w K width a)))) := by
  let F := pairedDerivativeAt (N width+s) i
    (pairedDerivativeAt (N width+s) j (localPrefix w K width s))
  have hmove : RatPolyCoeffEqv
      (polyMul (sourceDensity w K width s a)
        (polyMul (polyMul (liftBoundary (N width) ui) (liftBoundary (N width) uj)) F))
      (polyMul (liftBoundary (N width) (polyMul ui uj))
        (polyMul (sourceDensity w K width s a) F)) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
      (by decide) (fun
        | 0 => sourceDensity w K width s a
        | 1 => liftBoundary (N width) ui
        | 2 => liftBoundary (N width) uj | _ => F)
  exact (partialHaarHeads_congr (N width) hmove).trans
    ((pull_coefficient (N width) (polyMul ui uj) _).trans
      ((source_second_cell w K width s hs ha i j).mul_left (polyMul ui uj)))

/-- First frozen moment for any supported lower source; terminal positivity is
not needed for this algebraic transport. -/
theorem source_momentD_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentD (N width) (sourceDensity w K width s a)
        (localFrozenFirst w K width s u))
      (sourceMarginalFirst w K width s a u) := by
  change RatPolyCoeffEqv
    (partialHaarHeads (N width) (polyMul (sourceDensity w K width s a)
      (threeSum (fun i => polyMul (liftBoundary (N width) (u i))
        (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))))
    (threeSum (fun i => polyMul (u i)
      (pairedDerivativeAt s i (transferStep w K width a))))
  have hdistrib : RatPolyCoeffEqv
      (polyMul (sourceDensity w K width s a)
        (threeSum (fun i => polyMul (liftBoundary (N width) (u i))
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s)))))
      (threeSum (fun i => polyMul (sourceDensity w K width s a)
        (polyMul (liftBoundary (N width) (u i))
          (pairedDerivativeAt (N width+s) i (localPrefix w K width s))))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.mul_add_right _ _ _))
  exact (partialHaarHeads_congr (N width) hdistrib).trans
    ((integrate_threeSum (N width) _).trans
      ((source_first_term w K width s hs ha 0 (u 0)).add
        ((source_first_term w K width s hs ha 1 (u 1)).add
          (source_first_term w K width s hs ha 2 (u 2)))))

private theorem source_second_sum (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (sourceDensity w K width s a)
          (quadraticForm (fun i => liftBoundary (N width) (u i))
            (fun i j => pairedDerivativeAt (N width+s) i
              (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))))
      (sourceMarginalSecond w K width s a u) := by
  let q := sourceDensity w K width s a
  let v := fun i => liftBoundary (N width) (u i)
  let M := fun i j => pairedDerivativeAt (N width+s) i
    (pairedDerivativeAt (N width+s) j (localPrefix w K width s))
  have hdistrib : RatPolyCoeffEqv
      (polyMul q (quadraticForm v M))
      (threeSum (fun i => threeSum (fun j =>
        polyMul q (polyMul (polyMul (v i) (v j)) (M i j))))) := by
    unfold quadraticForm
    exact (threeSum_mul_left q _).symm.trans
      (threeSum_congr (fun i => (threeSum_mul_left q _).symm))
  change RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul q (quadraticForm v M)))
    (sourceMarginalSecond w K width s a u)
  exact (partialHaarHeads_congr (N width) hdistrib).trans
    ((integrate_quadratic (N width) _).trans
      (((source_second_term w K width s hs ha 0 0 (u 0) (u 0)).add
        ((source_second_term w K width s hs ha 0 1 (u 0) (u 1)).add
          (source_second_term w K width s hs ha 0 2 (u 0) (u 2)))).add
        (((source_second_term w K width s hs ha 1 0 (u 1) (u 0)).add
          ((source_second_term w K width s hs ha 1 1 (u 1) (u 1)).add
            (source_second_term w K width s hs ha 1 2 (u 1) (u 2)))).add
          ((source_second_term w K width s hs ha 2 0 (u 2) (u 0)).add
            ((source_second_term w K width s hs ha 2 1 (u 2) (u 1)).add
              (source_second_term w K width s hs ha 2 2 (u 2) (u 2)))))))

private theorem source_cost (w C : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (a : RatPoly) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (sourceDensity w K width s a)
          (polyMul (polyMul (cap C)
            (threeSquare (fun i => liftBoundary (N width) (u i))))
            (localPrefix w K width s))))
      (polyMul (polyMul (cap C) (threeSquare u))
        (transferStep w K width a)) := by
  let q := sourceDensity w K width s a
  let P := localPrefix w K width s
  have hmove : RatPolyCoeffEqv
      (polyMul q (polyMul (polyMul (cap C)
        (threeSquare (fun i => liftBoundary (N width) (u i)))) P))
      (polyMul (cap C)
        (polyMul (liftBoundary (N width) (threeSquare u)) (polyMul q P))) := by
    rw [lift_threeSquare]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 1) (.mul (.var 2) (.mul (.var 0) (.var 3))))
      (by decide) (fun
        | 0 => q | 1 => cap C
        | 2 => threeSquare (fun i => liftBoundary (N width) (u i)) | _ => P)
  have hsmul : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (cap C)
        (polyMul (liftBoundary (N width) (threeSquare u)) (polyMul q P))))
      (polySmul C (partialHaarHeads (N width)
        (polyMul (liftBoundary (N width) (threeSquare u)) (polyMul q P)))) :=
    (partialHaarHeads_congr (N width) (cap_mul_left C _)).trans
      (partialHaarHeads_smul (N width) C _)
  have hmass := source_mass w K width s hs a
  have hfinal : RatPolyCoeffEqv
      (polySmul C (polyMul (threeSquare u) (transferStep w K width a)))
      (polyMul (polyMul (cap C) (threeSquare u))
        (transferStep w K width a)) :=
    (RatPolyCoeffEqv.polyMul_smul_left C (threeSquare u)
      (transferStep w K width a)).symm.trans
        ((cap_mul_left C (threeSquare u)).symm.mul_right _)
  exact (partialHaarHeads_congr (N width) hmove).trans
    (hsmul.trans ((RatPolyCoeffEqv.smul C
      ((pull_coefficient (N width) (threeSquare u) _).trans
        (hmass.mul_left (threeSquare u)))).trans hfinal))

private theorem source_momentG_at_pin (w C : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentG (N width) (sourceDensity w K width s a)
        (sourceFrozenAugmentedSecondAt w C K width s u))
      (polyAdd (sourceMarginalSecond w K width s a u)
        (polyMul (polyMul (cap C) (threeSquare u))
          (transferStep w K width a))) := by
  change RatPolyCoeffEqv
    (partialHaarHeads (N width)
      (polyMul (sourceDensity w K width s a)
        (polyAdd (quadraticForm (fun i => liftBoundary (N width) (u i))
          (fun i j => pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j (localPrefix w K width s))))
          (polyMul (polyMul (cap C)
            (threeSquare (fun i => liftBoundary (N width) (u i))))
            (localPrefix w K width s))))) _
  exact (partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_add_right _ _ _)).trans
      ((integrate_add (N width) _ _).trans
        ((source_second_sum w K width s hs ha u).add
          (source_cost w C K width s hs a u)))

/-- The matched augmented second moment retains the full signed Hessian. -/
theorem source_momentG_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentG (N width) (sourceDensity w K width s a)
        (localFrozenAugmentedSecond w K width s u))
      (polyAdd (sourceMarginalSecond w K width s a u)
        (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u))
          (transferStep w K width a))) :=
  source_momentG_at_pin w (prefixCurvatureCost w) K width s hs ha u

private theorem support_extend {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p := by
  intro t ht
  have := hp t ht
  omega

private theorem three_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

/-- The terminal factor retains the complete certified spectator density. -/
def terminalDensity (w : Q') (K width s n r : Nat) : RatPoly :=
  sourceDensity w K width s (terminalMessage w K width (n+r))

theorem terminalDensity_supported (w : Q') (K width s n r : Nat) :
    SupportedQuaternionBlocks (N width+N width) (terminalDensity w K width s n r) :=
  supported_polyMul (localOutputDensity_supported w K width s)
    (support_extend (terminalMessage_supported w K width (n+r)) (by omega))

def terminalDensity_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s n r : Nat) (hK : headCutoff w ≤ K) :
    Certificate (N width+N width) (terminalDensity w K width s n r) := by
  let a := terminalMessage w K width (n+r)
  let Q : Certificate (N width+N width) (localOutputDensity w K width s) :=
    localOutputDensity_certificate hw0 hw1 K hK width s
  let A : Certificate (N width) a :=
    terminalMessage_certificate hw0 hw1 K width hK (n+r)
  let AE : Certificate (N width+N width) a :=
    certificate_extend (blocks := N width) (p := a) (N width)
      (terminalMessage_supported w K width (n+r)) A
  change Certificate (N width+N width)
    (polyMul (localOutputDensity w K width s) a)
  exact Certificate.mul (blocks := N width+N width)
    (p := localOutputDensity w K width s) (q := a) Q AE

theorem terminalDensity_independent (w : Q') (K width s n r : Nat)
    (hs : s ∈ activeBlocks width) :
    QuaternionBlockIndependent (N width+s) (terminalDensity w K width s n r) :=
  source_independent w K width s hs
    (terminalMessage_supported w K width (n+r))

/-- Exact coefficient factorization with the literal original action. -/
theorem terminalDensity_action_pin (w : Q') (K width s n r : Nat)
    (hs : s ∈ activeBlocks width) :
    RatPolyCoeffEqv
      (polyMul (terminalDensity w K width s n r) (localPrefix w K width s))
      (polyMul (lastStepAction w K width) (terminalMessage w K width (n+r))) :=
  source_factor w K width s hs (terminalMessage w K width (n+r))

/-- D is the actual frozen first jet of the terminal marginal A=T(a). -/
theorem terminal_momentD_pin (w : Q') (K width s n r : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentD (N width) (terminalDensity w K width s n r)
        (localFrozenFirst w K width s u))
      (sourceMarginalFirst w K width s (terminalMessage w K width (n+r)) u) :=
  source_momentD_pin w K width s hs
    (terminalMessage_supported w K width (n+r)) u

/-- G is the actual frozen all-nine-jet terminal Hessian plus local cost. -/
theorem terminal_momentG_pin (w : Q') (K width s n r : Nat)
    (hs : s ∈ activeBlocks width) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentG (N width) (terminalDensity w K width s n r)
        (localFrozenAugmentedSecond w K width s u))
      (polyAdd
        (sourceMarginalSecond w K width s (terminalMessage w K width (n+r)) u)
        (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u))
          (transferStep w K width (terminalMessage w K width (n+r))))) :=
  source_momentG_pin w K width s hs
    (terminalMessage_supported w K width (n+r)) u

private theorem source_fisher_pin (w C : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (conditionalFisher (N width) (sourceDensity w K width s a)
        (localPrefix w K width s) (localFrozenFirst w K width s u)
        (sourceFrozenAugmentedSecondAt w C K width s u))
      (polyAdd
        (polyMul (transferStep w K width a)
          (polyAdd (sourceMarginalSecond w K width s a u)
            (polyMul (polyMul (cap C) (threeSquare u))
              (transferStep w K width a))))
        (polyNeg (polyMul (sourceMarginalFirst w K width s a u)
          (sourceMarginalFirst w K width s a u)))) :=
  ((source_mass w K width s hs a).mul
    (source_momentG_at_pin w C K width s hs ha u)).add
      (RatPolyCoeffEqv.neg
        ((source_momentD_pin w K width s hs ha u).mul
          (source_momentD_pin w K width s hs ha u)))

private theorem source_B_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (a phi : RatPoly) :
    RatPolyCoeffEqv
      (momentB (N width) (sourceDensity w K width s a)
        (localPrefix w K width s) phi)
      (transferStep w K width (polyMul a phi)) := by
  have hreorder : RatPolyCoeffEqv
      (polyMul (polyMul (sourceDensity w K width s a)
        (localPrefix w K width s)) phi)
      (polyMul (sourceDensity w K width s (polyMul a phi))
        (localPrefix w K width s)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.var 2))
      (by decide) (fun
        | 0 => localOutputDensity w K width s | 1 => a
        | 2 => localPrefix w K width s | _ => phi)
  exact (partialHaarHeads_congr (N width) hreorder).trans
    (source_mass w K width s hs (polyMul a phi))

private theorem source_V_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (a phi : RatPoly) :
    RatPolyCoeffEqv
      (momentV (N width) (sourceDensity w K width s a)
        (localPrefix w K width s) phi)
      (transferStep w K width (polyMul a (polyMul phi phi))) := by
  have hreorder : RatPolyCoeffEqv
      (polyMul (polyMul (sourceDensity w K width s a)
        (localPrefix w K width s)) (polyMul phi phi))
      (polyMul (sourceDensity w K width s (polyMul a (polyMul phi phi)))
        (localPrefix w K width s)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 3) (.var 3)))
      (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3))))
        (.var 2))
      (by decide) (fun
        | 0 => localOutputDensity w K width s | 1 => a
        | 2 => localPrefix w K width s | _ => phi)
  exact (partialHaarHeads_congr (N width) hreorder).trans
    (source_mass w K width s hs (polyMul a (polyMul phi phi)))

private theorem source_E_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a phi : RatPoly}
    (happ : SupportedQuaternionBlocks (N width) (polyMul a phi))
    (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (momentE (N width) (sourceDensity w K width s a)
        (localFrozenFirst w K width s u) phi)
      (sourceMarginalFirst w K width s (polyMul a phi) u) := by
  have hreorder : RatPolyCoeffEqv
      (polyMul (polyMul (sourceDensity w K width s a)
        (localFrozenFirst w K width s u)) phi)
      (polyMul (sourceDensity w K width s (polyMul a phi))
        (localFrozenFirst w K width s u)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 3))) (.var 2))
      (by decide) (fun
        | 0 => localOutputDensity w K width s | 1 => a
        | 2 => localFrozenFirst w K width s u | _ => phi)
  exact (partialHaarHeads_congr (N width) hreorder).trans
    (source_momentD_pin w K width s hs happ u)

private theorem source_noise_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) (a phi : RatPoly) :
    RatPolyCoeffEqv
      (conditionalNoise (N width) (sourceDensity w K width s a)
        (localPrefix w K width s) phi)
      (polyAdd
        (polyMul (transferStep w K width a)
          (transferStep w K width (polyMul a (polyMul phi phi))))
        (polyNeg (polyMul (transferStep w K width (polyMul a phi))
          (transferStep w K width (polyMul a phi))))) :=
  ((source_mass w K width s hs a).mul
    (source_V_pin w K width s hs a phi)).add
      (RatPolyCoeffEqv.neg
        ((source_B_pin w K width s hs a phi).mul
          (source_B_pin w K width s hs a phi)))

/-- The conditional score of the matched density is the SAME original
two-source paired score with c=a*phi. No quotient c/a is introduced. -/
theorem source_score_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) {a phi : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (conditionalScore (N width) (sourceDensity w K width s a)
        (localPrefix w K width s) (localFrozenFirst w K width s u) phi)
      (firstJet u (pairedScorePlus s (transferStep w K width a)
        (transferStep w K width (polyMul a phi)))) := by
  let q := localOutputDensity w K width s
  let P := localPrefix w K width s
  let d := localFrozenFirst w K width s u
  let c := polyMul a phi
  let A := transferStep w K width a
  let B := transferStep w K width c
  let X := lastStepPairedResidual w K width a c
  let Y := polyMul q d
  have hc : SupportedQuaternionBlocks (N width) c := supported_polyMul ha hphi
  have hA := source_mass w K width s hs a
  have hB := source_B_pin w K width s hs a phi
  have hraw : RatPolyCoeffEqv
      (conditionalScore (N width) (sourceDensity w K width s a) P d phi)
      (polyAdd (polyMul A (momentE (N width) (sourceDensity w K width s a) d phi))
        (polyNeg (polyMul B (momentD (N width) (sourceDensity w K width s a) d)))) :=
    ((hA.mul (RatPolyCoeffEqv.refl _)).add
      (RatPolyCoeffEqv.neg (hB.mul (RatPolyCoeffEqv.refl _))))
  have hsplit : RatPolyCoeffEqv
      (polyMul Y X)
      (polyAdd
        (polyMul (polyMul (polyMul (sourceDensity w K width s a) d) phi)
          (liftBoundary (N width) A))
        (polyNeg (polyMul (polyMul (sourceDensity w K width s a) d)
          (liftBoundary (N width) B)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1))
        (.add (.mul (.var 2) (.mul (.var 3) (.var 4)))
          (.neg (.mul (.var 5) (.var 3)))))
      (.add
        (.mul (.mul (.mul (.mul (.var 0) (.var 3)) (.var 1)) (.var 4)) (.var 2))
        (.neg (.mul (.mul (.mul (.var 0) (.var 3)) (.var 1)) (.var 5))))
      (by decide) (fun
        | 0 => q | 1 => d | 2 => liftBoundary (N width) A
        | 3 => a | 4 => phi | _ => liftBoundary (N width) B)
  have hI : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul Y X))
      (polyAdd
        (polyMul (momentE (N width) (sourceDensity w K width s a) d phi) A)
        (polyNeg (polyMul (momentD (N width) (sourceDensity w K width s a) d) B))) :=
    (partialHaarHeads_congr (N width) hsplit).trans
      ((integrate_add (N width) _ _).trans
        ((partialHaarHeads_mul_lift (N width) _ A).add
          ((partialHaarHeads_neg (N width) _).trans
            (RatPolyCoeffEqv.neg (partialHaarHeads_mul_lift (N width) _ B)))))
  have hcomm : RatPolyCoeffEqv
      (polyAdd (polyMul A (momentE (N width) (sourceDensity w K width s a) d phi))
        (polyNeg (polyMul B (momentD (N width) (sourceDensity w K width s a) d))))
      (polyAdd
        (polyMul (momentE (N width) (sourceDensity w K width s a) d phi) A)
        (polyNeg (polyMul (momentD (N width) (sourceDensity w K width s a) d) B))) :=
    (RatPolyCoeffEqv.mul_comm _ _).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_comm _ _))
  exact (hraw.trans hcomm).trans (hI.symm.trans
    (local_frozen_score_integral_pin w K width s q P
      (localOutputDensity_independent w K width s hs)
      (local_factor_pin w K width s hs) ha hc u))

private theorem terminal_local_signed_score_bound_at {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s n r : Nat) (hs : s ∈ activeBlocks width)
    (hhead : headCutoff w ≤ K) (cost : Q')
    {phi R : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    (PR : Certificate (N width) R)
    (curvature : Certificate (N width+N width)
      (frozenCurvatureAt (N width+s) cost (localPrefix w K width s)
        (fun i => liftBoundary (N width) (u i)))) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let B := transferStep w K width (polyMul a phi)
    let DA := sourceMarginalFirst w K width s a u
    let DDA := sourceMarginalSecond w K width s a u
    quaternionHaar (N width) (polyMul R
      (polyMul (firstJet u (pairedScorePlus s A B))
        (firstJet u (pairedScorePlus s A B)))) ≤
    quaternionHaar (N width) (polyMul R
      (polyMul
        (polyAdd (polyMul A (transferStep w K width
          (polyMul a (polyMul phi phi)))) (polyNeg (polyMul B B)))
        (polyAdd
          (polyMul A (polyAdd DDA
            (polyMul (polyMul (cap cost) (threeSquare u)) A)))
          (polyNeg (polyMul DA DA))))) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let q := terminalDensity w K width s n r
  let P := localPrefix w K width s
  let d := localFrozenFirst w K width s u
  let dd := sourceFrozenAugmentedSecondAt w cost K width s u
  let v := fun i => liftBoundary (N width) (u i)
  have ha : SupportedQuaternionBlocks (N width) a :=
    terminalMessage_supported w K width (n+r)
  have hslot : s < N width := activeBlocks_lt width s hs
  have hout : N width+s < N width+N width := by omega
  have hv : ∀ i, SupportedQuaternionBlocks (N width+N width) (v i) :=
    fun i => lift_supported (hu i) (N width)
  have hp := heatInterval hout (by omega : s < N width+N width) hw0 hw1 K
  have hd : SupportedQuaternionBlocks (N width+N width) d :=
    three_supported (fun i =>
      supported_polyMul (hv i) (pairedDerivativeAt_supported hout i hp.support))
  have hsecond : SupportedQuaternionBlocks (N width+N width)
      (quadraticForm v (fun i j => pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j P))) :=
    three_supported (fun i => three_supported (fun j =>
      supported_polyMul (supported_polyMul (hv i) (hv j))
        (pairedDerivativeAt_supported hout i
          (pairedDerivativeAt_supported hout j hp.support))))
  have hnorm := three_supported (fun i => supported_polyMul (hv i) (hv i))
  have hdd : SupportedQuaternionBlocks (N width+N width) dd :=
    supported_add hsecond (supported_polyMul
      (supported_polyMul
        (polySmul_supported (supported_one _) cost) hnorm)
      hp.support)
  have hphiFull : SupportedQuaternionBlocks (N width+N width) phi :=
    support_extend hphi (by omega)
  have hclear : RatPolyCoeffEqv
      (polyAdd (polyMul P dd) (polyNeg (polyMul d d)))
      (frozenCurvatureAt (N width+s) cost P v) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 2) (.mul (.mul (.var 3) (.var 4)) (.var 0))))
        (.neg (.mul (.var 1) (.var 1))))
      (.add (.mul (.var 3) (.mul (.var 4) (.mul (.var 0) (.var 0))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun
        | 0 => P | 1 => d
        | 2 => quadraticForm v (fun i j => pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j P))
        | 3 => cap cost | _ => threeSquare v)
  let C := Certificate.ofCoeff hclear curvature
  have hm := headFloor_positive hw0 hw1
  have hle : headFloor w ≤ prefixCap w+headFloor w :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (headFloor w) _ hp.nonnegative)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hupper := Q'.pos_of_lt_of_le hm hle
  have hgram := conditional_signed_score_bound (N width) (N width)
    q P d dd phi R
    (terminalDensity_supported w K width s n r) hp.support hd hdd hphiFull
    (terminalDensity_certificate hw0 hw1 K width s n r hhead) C PR
    hm hupper hle
    (heatAt_floorCertificate hout (by omega : s < N width+N width)
      hw0 hw1 K hhead)
    (hp.raise (headFloor w) (Q'.le_of_lt hm)).upper
  have hscore := source_score_pin w K width s hs ha hphi u
  have hnoise := source_noise_pin w K width s hs a phi
  have hfisher := source_fisher_pin w cost K width s hs ha u
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((hscore.mul hscore).mul_left R).symm))
    (Q'.le_trans' _ _ _ hgram
      (Q'.le_of_eqv (haar_of_coeff ((hnoise.mul hfisher).mul_left R))))

/-- Exact original-action conditional signed Gram with the positive terminal
source inserted into q. Both derivatives and the reciprocal-facing marginal
are A=T(a); the RHS is NOT asserted nonnegative term by term or bounded above. -/
theorem terminal_local_signed_score_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s n r : Nat) (hs : s ∈ activeBlocks width)
    (hK : prefixFrozenCurvatureCutoff w ≤ K)
    {phi R : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    (PR : Certificate (N width) R) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let B := transferStep w K width (polyMul a phi)
    let DA := sourceMarginalFirst w K width s a u
    let DDA := sourceMarginalSecond w K width s a u
    quaternionHaar (N width) (polyMul R
      (polyMul (firstJet u (pairedScorePlus s A B))
        (firstJet u (pairedScorePlus s A B)))) ≤
    quaternionHaar (N width) (polyMul R
      (polyMul
        (polyAdd (polyMul A (transferStep w K width
          (polyMul a (polyMul phi phi)))) (polyNeg (polyMul B B)))
        (polyAdd
          (polyMul A (polyAdd DDA
            (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u)) A)))
          (polyNeg (polyMul DA DA))))) := by
  have hslot := activeBlocks_lt width s hs
  have hout : N width+s < N width+N width := by omega
  have hhead : headCutoff w ≤ K := by unfold prefixFrozenCurvatureCutoff at hK; omega
  exact terminal_local_signed_score_bound_at hw0 hw1 K width s n r hs hhead
    (prefixCurvatureCost w) hphi u hu PR
    (heatAt_frozen_curvature_certificate (by omega) ⟨N width+s,hout⟩ ⟨s,by omega⟩
      (by simp only; omega) hw0 hw1 K hK _ (fun i => lift_supported (hu i) (N width)))

/-- The sharper PRODUCED original heat certificate in the SAME terminal signed
Gram. Full spectator action, all nine marginal jets, noise and negative DA square
are unchanged. This is not an upper innovation bound or completed-norm estimate. -/
theorem terminal_local_signed_score_bound_nearFlat {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s n r : Nat) (hs : s ∈ activeBlocks width)
    (hK : nearFlatPrefixFrozenCurvatureCutoff w ≤ K)
    {phi R : RatPoly}
    (hphi : SupportedQuaternionBlocks (N width) phi)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    (PR : Certificate (N width) R) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let B := transferStep w K width (polyMul a phi)
    let DA := sourceMarginalFirst w K width s a u
    let DDA := sourceMarginalSecond w K width s a u
    quaternionHaar (N width) (polyMul R
      (polyMul (firstJet u (pairedScorePlus s A B))
        (firstJet u (pairedScorePlus s A B)))) ≤
    quaternionHaar (N width) (polyMul R
      (polyMul
        (polyAdd (polyMul A (transferStep w K width
          (polyMul a (polyMul phi phi)))) (polyNeg (polyMul B B)))
        (polyAdd
          (polyMul A (polyAdd DDA
            (polyMul (polyMul (cap (nearFlatPrefixCurvatureCost w)) (threeSquare u)) A)))
          (polyNeg (polyMul DA DA))))) := by
  have hslot := activeBlocks_lt width s hs
  have hout : N width+s < N width+N width := by omega
  have hhead : headCutoff w ≤ K := by
    unfold nearFlatPrefixFrozenCurvatureCutoff at hK
    omega
  exact terminal_local_signed_score_bound_at hw0 hw1 K width s n r hs hhead
    (nearFlatPrefixCurvatureCost w) hphi u hu PR
    (heatAt_frozen_curvature_nearFlat_certificate (by omega) ⟨N width+s,hout⟩ ⟨s,by omega⟩
      (by simp only; omega) hw0 hw1 K hK _ (fun i => lift_supported (hu i) (N width)))

/-- Integration preserves the produced lower frozen log-Hessian of the SAME
original terminal marginal, under every certified outgoing insertion. The
negative marginal-gradient square is retained without an observable-noise
multiplier. This is integrated order, not a polynomial certificate, an upper
innovation estimate, a variance floor or a scaling/physical gap assertion. -/
theorem terminal_marginal_curvature_nonnegative_nearFlat {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s n r : Nat) (hs : s ∈ activeBlocks width)
    (hK : nearFlatPrefixFrozenCurvatureCutoff w ≤ K)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    {R : RatPoly} (PR : Certificate (N width) R) :
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let DA := sourceMarginalFirst w K width s a u
    let DDA := sourceMarginalSecond w K width s a u
    (0 : Q') ≤ quaternionHaar (N width) (polyMul R
      (polyAdd
        (polyMul A (polyAdd DDA
          (polyMul (polyMul (cap (nearFlatPrefixCurvatureCost w)) (threeSquare u)) A)))
        (polyNeg (polyMul DA DA)))) := by
  dsimp only
  let a := terminalMessage w K width (n+r)
  let q := terminalDensity w K width s n r
  let P := localPrefix w K width s
  let d := localFrozenFirst w K width s u
  let cost := nearFlatPrefixCurvatureCost w
  let dd := sourceFrozenAugmentedSecondAt w cost K width s u
  let v := fun i => liftBoundary (N width) (u i)
  have ha := terminalMessage_supported w K width (n+r)
  have hslot := activeBlocks_lt width s hs
  have hout : N width+s < N width+N width := by omega
  have hhead : headCutoff w ≤ K := by
    unfold nearFlatPrefixFrozenCurvatureCutoff at hK
    omega
  have hv : ∀ i, SupportedQuaternionBlocks (N width+N width) (v i) :=
    fun i => lift_supported (hu i) (N width)
  have hp := heatInterval hout (by omega : s < N width+N width) hw0 hw1 K
  have hd : SupportedQuaternionBlocks (N width+N width) d :=
    three_supported (fun i =>
      supported_polyMul (hv i) (pairedDerivativeAt_supported hout i hp.support))
  have hsecond : SupportedQuaternionBlocks (N width+N width)
      (quadraticForm v (fun i j => pairedDerivativeAt (N width+s) i
        (pairedDerivativeAt (N width+s) j P))) :=
    three_supported (fun i => three_supported (fun j =>
      supported_polyMul (supported_polyMul (hv i) (hv j))
        (pairedDerivativeAt_supported hout i
          (pairedDerivativeAt_supported hout j hp.support))))
  have hnorm := three_supported (fun i => supported_polyMul (hv i) (hv i))
  have hdd : SupportedQuaternionBlocks (N width+N width) dd :=
    supported_add hsecond (supported_polyMul
      (supported_polyMul (polySmul_supported (supported_one _) cost) hnorm) hp.support)
  have hclear : RatPolyCoeffEqv
      (polyAdd (polyMul P dd) (polyNeg (polyMul d d)))
      (frozenCurvatureAt (N width+s) cost P v) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 2) (.mul (.mul (.var 3) (.var 4)) (.var 0))))
        (.neg (.mul (.var 1) (.var 1))))
      (.add (.mul (.var 3) (.mul (.var 4) (.mul (.var 0) (.var 0))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun
        | 0 => P | 1 => d
        | 2 => quadraticForm v (fun i j => pairedDerivativeAt (N width+s) i
            (pairedDerivativeAt (N width+s) j P))
        | 3 => cap cost | _ => threeSquare v)
  let C := Certificate.ofCoeff hclear
    (heatAt_frozen_curvature_nearFlat_certificate (by omega)
      ⟨N width+s,hout⟩ ⟨s,by omega⟩ (by simp only; omega) hw0 hw1 K hK v
      (fun i => lift_supported (hu i) (N width)))
  have hm := headFloor_positive hw0 hw1
  have hle : headFloor w ≤ prefixCap w+headFloor w :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (headFloor w) _ hp.nonnegative)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hupper := Q'.pos_of_lt_of_le hm hle
  have h := SU2QuaternionConditionalFisherOrder.conditional_fisher_nonnegative
    (N width) (N width) q P d dd R
    (terminalDensity_supported w K width s n r) hp.support hd hdd
    (terminalDensity_certificate hw0 hw1 K width s n r hhead) C PR
    hm hupper hle
    (heatAt_floorCertificate hout (by omega : s < N width+N width) hw0 hw1 K hhead)
    (hp.raise (headFloor w) (Q'.le_of_lt hm)).upper
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (haar_of_coeff ((source_fisher_pin w cost K width s hs ha u).mul_left R)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminalDensity_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminalDensity_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminalDensity_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminalDensity_action_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_momentD_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_momentG_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.source_momentD_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.source_momentG_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.source_score_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_local_signed_score_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_local_signed_score_bound_nearFlat
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_marginal_curvature_nonnegative_nearFlat
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.sourceFrozenAugmentedSecondAt
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.source_momentG_at_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.source_fisher_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_local_signed_score_bound_at

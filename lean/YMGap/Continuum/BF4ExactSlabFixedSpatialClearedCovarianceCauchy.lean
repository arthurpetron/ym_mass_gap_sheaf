/-
# Same-action Cauchy reduction for the cleared signed covariance defect

The exact `clearedDefect_pairing` identity already puts the signed defect on
the original spatial weight times the actual terminal message.  The Haar
square certificate and constructive weighted Cauchy--Schwarz therefore give
an honest finite bound by two explicit norms:

  `|clearedDefect|^2 <= ||terminalResidual||^2 * ||combinedTest||^2`.

This is a reduction, not the missing uniform estimate.  Both norms retain the
same original action, carrier, cutoff, width and terminal message.  In
particular no conditional message is substituted for the original weight,
and no square root, division, spectral theorem or continuum limit is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalDirichletCoercivity
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- The combined signed test stays on the original finite polynomial carrier. -/
theorem combinedTest_supported (w delta : Q') (K width : Nat) (g s : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hs : SupportedQuaternionBlocks (N width) s) :
    SupportedQuaternionBlocks (N width) (combinedTest w delta K width g s) := by
  unfold combinedTest
  apply supported_add
  · apply supported_add
    · exact support_smul
        (supported_polyMul (transferStep_supported w K width hg) hs) _
    · exact support_smul
        (transferStep_supported w K width (supported_polyMul hg hs)) _
  · exact support_smul (transferStep_supported w K width hg) _

/-- The exact defect in the certified weighted-pair interface. -/
theorem clearedDefect_pairing_weightedPair
    (w delta : Q') (K width : Nat) (g r s : RatPoly) :
    clearedDefect w delta K width g r s ≈
      weightedPair (N width) (polyMul (spatialWeight w K width) g) r
        (combinedTest w delta K width g s) := by
  have hpin := clearedDefect_pairing w delta K width g r s
  have hcomm : RatPolyCoeffEqv
      (polyMul (polyMul (spatialWeight w K width) g)
        (polyMul r (combinedTest w delta K width g s)))
      (polyMul (polyMul r (combinedTest w delta K width g s))
        (polyMul (spatialWeight w K width) g)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.var 3)) (.mul (.var 0) (.var 1)))
      (by decide)
      (fun
        | 0 => spatialWeight w K width
        | 1 => g
        | 2 => r
        | _ => combinedTest w delta K width g s)
  unfold weightedPair
  exact Q'.eqv_trans _ _ _ hpin (haar_of_coeff hcomm)

/-! ## The finite same-action norm reduction -/

/--
For the actual terminal residual and the exact combined signed test, the
partition-cleared defect satisfies a constructive Cauchy--Schwarz bound in
the original weighted Haar form.  The certificate is built from the original
spatial weight and terminal message, so this is an actual finite SU(2)
statement rather than an abstract positive-form hypothesis.
-/
theorem terminalResidual_clearedDefect_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (delta : Q') (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) {f s : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hs : SupportedQuaternionBlocks (N width) s) :
    let g := terminalMessage w K width n
    let r := terminalResidual w K width n i f
    let F := combinedTest w delta K width g s
    clearedDefect w delta K width g r s *
        clearedDefect w delta K width g r s ≤
      weightedPair (N width) (polyMul (spatialWeight w K width) g) r r *
        weightedPair (N width) (polyMul (spatialWeight w K width) g) F F := by
  dsimp only
  let g := terminalMessage w K width n
  let r := terminalResidual w K width n i f
  let F := combinedTest w delta K width g s
  let W := polyMul (spatialWeight w K width) g
  have hg : SupportedQuaternionBlocks (N width) g :=
    terminalMessage_supported w K width n
  have hr : SupportedQuaternionBlocks (N width) r :=
    terminalResidual_supported w K width n i hf
  have hF : SupportedQuaternionBlocks (N width) F :=
    combinedTest_supported w delta K width g s hg hs
  have hW : Certificate (N width) W :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK n)
  have hcs := weighted_cauchySchwarz (N width) W r F hW hr hF
  have hpair : clearedDefect w delta K width g r s ≈
      weightedPair (N width) W r F :=
    clearedDefect_pairing_weightedPair w delta K width g r s
  have hleft : clearedDefect w delta K width g r s *
      clearedDefect w delta K width g r s ≈
      weightedPair (N width) W r F * weightedPair (N width) W r F :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpair)
      (Q'.mul_eqv_congr_left _ _ _ hpair)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hcs

end YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy.combinedTest_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy.clearedDefect_pairing_weightedPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialClearedCovarianceCauchy.terminalResidual_clearedDefect_square_le

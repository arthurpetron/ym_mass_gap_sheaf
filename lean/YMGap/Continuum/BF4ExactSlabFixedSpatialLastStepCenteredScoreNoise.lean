/-
# The corrected conditional covariance reaches the actual direct-score budget

Use the ORIGINAL full terminal-weighted window, its literal conditional noise
and the SAME output multiplier Vbar^2*G^2 as exactScoreAngularBudget.
The mean-derivative square remains subtracted in every active angular plane.
No conditional mass, source or excitation norm is inverted by this join.

This is a finite alternative ceiling, not a claim that replacing the exact
score by this ceiling improves it. A useful summed estimate in surviving-form
units, AF survival and the two-step RG action comparison remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredScoreNoise

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
  (original_block_centered_scoreVariance_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff relativeCap headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (sixValue sixValue_mono)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage

private theorem certificate_square_bound {blocks : Nat} {p S J : RatPoly}
    (P : Certificate blocks (polyAdd p (polyNeg (polyMul S S))))
    (hJ : SupportedQuaternionBlocks blocks J) :
    quaternionHaar blocks (polyMul (polyMul J J) (polyMul S S)) ≤
      quaternionHaar blocks (polyMul (polyMul J J) p) := by
  let E := polyMul (polyMul J J) (polyAdd p (polyNeg (polyMul S S)))
  have hn := (Certificate.multiplySquare J hJ P).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul J J) (polyMul S S)) E)
      (polyMul (polyMul J J) p) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 0))
          (.add (.var 2) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.mul (.var 0) (.var 0)) (.var 2))
      (by decide) (fun | 0 => J | 1 => S | _ => p)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
    (haar_of_coeff hid)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- The original full-window noise times the corrected coefficient, with
the literal reciprocal/spatial multiplier from the direct-score consumer. -/
def centeredScoreNoiseAngularBudget (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  let noise := blockNoise w K width (r+1) (terminalMessage w K width n) psi
  finSum (fun s => if s ∈ activeBlocks width then
    sixValue (fun i j => (1+sigma)*quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (polyMul
          (polyAdd (polyMul (cap (relativeCap w 32*relativeCap w 32)) (polyMul A A))
            (polyNeg (polyMul (angularDerivative (4*s+i) (4*s+j) A)
              (angularDerivative (4*s+i) (4*s+j) A)))) noise)))
    else 0) (N width)

private theorem finite_sum_mono (f g : Nat → Q') : ∀ m,
    (∀ s, s < m → f s ≤ g s) → finSum f m ≤ finSum g m
  | 0, _ => Q'.le_refl' _
  | m+1, h => Q'.add_le_add
      (finite_sum_mono f g m (fun s hs => h s (by omega))) (h m (by omega))

/-- The SAME exact score budget is bounded using the original conditional
noise and its mean-derivative correction. No new analytic premise occurs. -/
theorem exactScoreAngularBudget_le_centeredNoise (sigma : Q')
    (hsigma : (0 : Q') ≤ sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (f : RatPoly) (c : Q')
    (hf : SupportedQuaternionBlocks (N width) f) (k : Nat) :
    exactScoreAngularBudget sigma hw0 hw1 K width hK n r (shifted f c) k ≤
      centeredScoreNoiseAngularBudget sigma hw0 hw1 K width hK n r (shifted f c) k := by
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1)
    (polyMul (terminalMessage w K width n) (shifted f c))
  let G := blockReciprocal hw0 hw1 K width
    (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) n (r+1) k
  let Vbar := spatialFringeMass w K width
  let J := polyMul Vbar G
  have hJ : SupportedQuaternionBlocks (N width) J :=
    supported_polyMul (spatialFringeMass_supported w K width)
      (reciprocal_supported (terminalMessage_supported w K width (n+(r+1))) _ _ k)
  have hJJ : RatPolyCoeffEqv (polyMul J J)
      (polyMul (polyMul Vbar Vbar) (polyMul G G)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => Vbar | _ => G)
  unfold exactScoreAngularBudget centeredScoreNoiseAngularBudget
  apply finite_sum_mono
  intro s hs
  split
  · rename_i hactive
    apply sixValue_mono
    intro i j hi hj
    have h := certificate_square_bound
      (original_block_centered_scoreVariance_certificate hw0 hw1 K width hK
        n r s hactive hi hj f c hf) hJ
    have h' := Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (hJJ.mul_right _)))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff (hJJ.mul_right _))))
    exact Q'.mul_le_mul_of_nonneg_left _ _ (1+sigma) h'
      (Q'.zero_le_add _ _ Q'.zero_le_one hsigma)
  · exact Q'.le_refl' _

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredScoreNoise

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredScoreNoise.centeredScoreNoiseAngularBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredScoreNoise.exactScoreAngularBudget_le_centeredNoise

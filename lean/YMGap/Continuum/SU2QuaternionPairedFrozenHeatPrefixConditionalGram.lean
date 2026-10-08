/-
# Signed conditional jet moments of the SAME original heat prefix

The actual prefix supplies its own augmented frozen curvature and strict
kernel windows. Three replicas keep one shared tail; integrated order
reflection removes the kernel multiplier and retains the negative score-mean
square. The incoming density and surrounding tail insertion are certified
data, not silently replaced by free Haar or by an independent law.

These are moments of PRECOMPUTED paired jets. No identity with derivatives
of the marginal is asserted, especially for coefficients or densities that
depend on integrated heads. No arbitrary source is factored as q*phi. The
full interacting product/domain recoding and source-error joins remain open,
as do scaling, OS reconstruction and a physical Hamiltonian gap.
-/

import YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixSignedGram
import YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

namespace YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixConditionalGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit (prefix_mixed_interval)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixSignedGram
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeWord_supported relativeWord_unit)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

/-- The actual full prefix curvature, with the zero-lambda term cleared.
The caller supplies no curvature, Hessian sign or determinant bound. -/
def prefix_cleared_curvature_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixFrozenCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks
      (polyAdd (polyMul (pairedPrefix w K) (prefixAugmentedSecondJet w K u))
        (polyNeg (polyMul (prefixFirstJet w K u) (prefixFirstJet w K u)))) := by
  have hclear : RatPolyCoeffEqv
      (polyAdd (polyMul (pairedPrefix w K) (prefixAugmentedSecondJet w K u))
        (polyNeg (polyMul (prefixFirstJet w K u) (prefixFirstJet w K u))))
      (polyAdd (polyMul (cap 0) (polyMul (pairedPrefix w K) (pairedPrefix w K)))
        (polyAdd (polyMul (pairedPrefix w K) (prefixAugmentedSecondJet w K u))
          (polyNeg (polyMul (prefixFirstJet w K u) (prefixFirstJet w K u))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
      (.add (.mul (.const 0) (.mul (.var 0) (.var 0)))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun
        | 0 => pairedPrefix w K
        | 1 => prefixFirstJet w K u
        | _ => prefixAugmentedSecondJet w K u)
  exact Certificate.ofCoeff (hclear.trans (prefix_augmented_curvature_pin w K u))
    (prefix_frozen_curvature_certificate hb hw0 hw1 K hK u hu)

private theorem threeSum_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

/-- The signed conditional Gram of actual augmented prefix jets under any
certified incoming density and tail insertion. All surviving variables and
the signed second-jet correction remain; no marginal inverse is used. -/
theorem prefix_conditional_signed_score_bound {tail heads : Nat} {w : Q'}
    {q phi R : RatPoly} (hb : 1 < tail+heads)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixFrozenCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (tail+heads) (u i))
    (hq : SupportedQuaternionBlocks (tail+heads) q)
    (hphi : SupportedQuaternionBlocks (tail+heads) phi)
    (Q : Certificate (tail+heads) q) (PR : Certificate tail R) :
    let P := pairedPrefix w K
    let d := prefixFirstJet w K u
    let dd := prefixAugmentedSecondJet w K u
    quaternionHaar tail (polyMul R
      (polyMul (conditionalScore heads q P d phi) (conditionalScore heads q P d phi))) ≤
      quaternionHaar tail (polyMul R
        (polyMul (conditionalNoise heads q P phi) (conditionalFisher heads q P d dd))) := by
  let P := prefix_value_interval hb hw0 hw1 K
  have hm : (0 : Q') < headFloor w := headFloor_positive hw0 hw1
  have hle : headFloor w ≤ prefixValueCap w+headFloor w :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (headFloor w) (prefixValueCap w) P.nonnegative)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hupper : (0 : Q') < prefixValueCap w+headFloor w :=
    Q'.pos_of_lt_of_le hm hle
  have hhead : headCutoff w ≤ K := by
    unfold prefixFrozenCurvatureCutoff at hK
    omega
  let L := QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (relativeWord_supported hb) (relativeWord_unit hb) K hhead
  have hd : SupportedQuaternionBlocks (tail+heads) (prefixFirstJet w K u) :=
    threeSum_supported (fun i => supported_polyMul (hu i)
      (prefix_first_interval hb hw0 hw1 K i).support)
  have hdd : SupportedQuaternionBlocks (tail+heads) (prefixSecondJet w K u) :=
    threeSum_supported (fun i => threeSum_supported (fun j =>
      supported_polyMul (supported_polyMul (hu i) (hu j))
        (prefix_mixed_interval hb hw0 hw1 K i j).support))
  have hR : SupportedQuaternionBlocks (tail+heads) (threeSquare u) :=
    supported_add (supported_polyMul (hu 0) (hu 0))
      (supported_add (supported_polyMul (hu 1) (hu 1)) (supported_polyMul (hu 2) (hu 2)))
  have haug : SupportedQuaternionBlocks (tail+heads) (prefixAugmentedSecondJet w K u) :=
    supported_add hdd
      (supported_polyMul
        (supported_polyMul (polySmul_supported (supported_one (tail+heads))
          (prefixCurvatureCost w)) hR) P.support)
  exact conditional_signed_score_bound tail heads q (pairedPrefix w K)
    (prefixFirstJet w K u) (prefixAugmentedSecondJet w K u) phi R
    hq P.support hd haug hphi Q
    (prefix_cleared_curvature_certificate hb hw0 hw1 K hK u hu) PR
    hm hupper hle L (P.raise (headFloor w) (Q'.le_of_lt hm)).upper

end YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixConditionalGram

#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixConditionalGram.prefix_cleared_curvature_certificate
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixConditionalGram.prefix_conditional_signed_score_bound

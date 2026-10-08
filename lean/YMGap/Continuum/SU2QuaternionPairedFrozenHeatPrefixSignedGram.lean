/-
# Signed integrated Gram bound for the SAME full ORIGINAL-prefix matrix

The produced full frozen curvature certificate enters the signed dual
bound with lambda zero. Its homogeneous polynomial cost augments the
actual second jet BEFORE Haar integration. Arbitrary supported polynomial
directions therefore remain inside the integral, and no sign of the
unaugmented Hessian is assumed. Original positive windows are constructed
from the actual prefix interval and floor; their inverses do not enter
the resulting estimate.

This is a finite signed integrated Gram precursor on blocks zero/one,
not a normalized conditional estimate, completed OS or physical gap.
-/

import YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
import YMGap.Continuum.QuaternionHaarCurvatureDualBound

namespace YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixSignedGram

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
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative threeSum)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet jetCurvature)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit (prefix_mixed_interval)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeWord_supported relativeWord_unit)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)

/-- Actual first paired jets, multiplied by the frozen coefficients. -/
def prefixFirstJet (w : Q') (K : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  firstJet u (fun i => pairedDerivative i (pairedPrefix w K))

/-- All NINE ordered actual mixed jets precede coefficient multiplication. -/
def prefixSecondJet (w : Q') (K : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  quadraticForm u (fun i j => pairedDerivative i (pairedDerivative j (pairedPrefix w K)))

/-- The polynomial homogeneous cost stays INSIDE subsequent integration. -/
def prefixAugmentedSecondJet (w : Q') (K : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  polyAdd (prefixSecondJet w K u)
    (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u)) (pairedPrefix w K))

/-- Exact zero-lambda curvature reassembly on the SAME original prefix. -/
theorem prefix_augmented_curvature_pin (w : Q') (K : Nat) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (cap 0) (polyMul (pairedPrefix w K) (pairedPrefix w K)))
        (polyAdd (polyMul (pairedPrefix w K) (prefixAugmentedSecondJet w K u))
          (polyNeg (polyMul (prefixFirstJet w K u) (prefixFirstJet w K u)))))
      (prefixFrozenCurvature w (prefixCurvatureCost w) K u) := by
  have hz : RatPolyCoeffEqv
      (polyMul (cap 0) (polyMul (pairedPrefix w K) (pairedPrefix w K))) polyZero :=
    (cap_mul_left 0 _).trans (RatPolyCoeffEqv.zero_smul _)
  refine (hz.add (RatPolyCoeffEqv.refl _)).trans ((RatPolyCoeffEqv.zero_add _).trans ?_)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.var 2) (.mul (.mul (.var 3) (.var 4)) (.var 0))))
      (.neg (.mul (.var 1) (.var 1))))
    (.add (.mul (.var 3) (.mul (.var 4) (.mul (.var 0) (.var 0))))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
    (by decide) (fun
      | 0 => pairedPrefix w K
      | 1 => prefixFirstJet w K u
      | 2 => prefixSecondJet w K u
      | 3 => cap (prefixCurvatureCost w)
      | _ => threeSquare u)

private theorem threeSum_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

/-- Signed Gram estimate from the PRODUCED full original-prefix curvature.
No nonpositive-Hessian premise and no coefficient cap are supplied. -/
theorem prefix_signed_gram_bound {blocks : Nat} {w : Q'}
    {background f : RatPoly} (hb : 1 < blocks)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixFrozenCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (hf : SupportedQuaternionBlocks blocks f) (B : Certificate blocks background) :
    quaternionHaar blocks (polyMul background (polyMul (prefixFirstJet w K u) f)) *
        quaternionHaar blocks (polyMul background (polyMul (prefixFirstJet w K u) f)) ≤
      quaternionHaar blocks (polyMul background (polyMul (pairedPrefix w K) (polyMul f f))) *
        quaternionHaar blocks (polyMul background (prefixAugmentedSecondJet w K u)) := by
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
  have hd : SupportedQuaternionBlocks blocks (prefixFirstJet w K u) :=
    threeSum_supported (fun i => supported_polyMul (hu i)
      (prefix_first_interval hb hw0 hw1 K i).support)
  have hdd : SupportedQuaternionBlocks blocks (prefixSecondJet w K u) :=
    threeSum_supported (fun i => threeSum_supported (fun j =>
      supported_polyMul (supported_polyMul (hu i) (hu j))
        (prefix_mixed_interval hb hw0 hw1 K i j).support))
  have hR : SupportedQuaternionBlocks blocks (threeSquare u) :=
    supported_add (supported_polyMul (hu 0) (hu 0))
      (supported_add (supported_polyMul (hu 1) (hu 1)) (supported_polyMul (hu 2) (hu 2)))
  have haug : SupportedQuaternionBlocks blocks (prefixAugmentedSecondJet w K u) :=
    supported_add hdd
      (supported_polyMul
        (supported_polyMul (polySmul_supported (supported_one blocks) (prefixCurvatureCost w)) hR)
        P.support)
  let C := Certificate.ofCoeff (prefix_augmented_curvature_pin w K u)
    (prefix_frozen_curvature_certificate hb hw0 hw1 K hK u hu)
  have h := QuaternionHaarCurvatureDualBound.curvature_signed_dual_bound
    P.support hd haug hf hm hupper hle L
    (P.raise (headFloor w) (Q'.le_of_lt hm)).upper B C
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.var 1) (.mul (.const 0) (.var 2))))
    (.mul (.var 0) (.var 1)) (by decide) (fun
      | 0 => quaternionHaar blocks (polyMul background (polyMul (pairedPrefix w K) (polyMul f f)))
      | 1 => quaternionHaar blocks (polyMul background (prefixAugmentedSecondJet w K u))
      | _ => quaternionHaar blocks (polyMul background (pairedPrefix w K)))

end YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixSignedGram

#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixSignedGram.prefix_augmented_curvature_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixSignedGram.prefix_signed_gram_bound

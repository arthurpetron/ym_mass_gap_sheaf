/-
# A certified original block Schur bound on multiplied tests

For S=T^d, a positive supported A and the actual upper certificate
U*A-S*A, conditional Gram positivity and weighted transfer symmetry give
ell[(S(A*f))^2] <= U^2*ell[(A*f)^2].  The input f may be signed and d=0
is included.  Every iterate and pairing retains the original spatial
action.  There is no inverse polynomial, stationary eigenpin, source-norm
floor, or supplied operator-norm estimate.  Extension to an arbitrary
filtered message, and changing-family signed-cost control, are not claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (iterateStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (iterateStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise blockNoise_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass

private theorem mass_neg (w : Q') (K width : Nat) (p : RatPoly) :
    weightedMass w K width (polyNeg p) ≈ -(weightedMass w K width p) :=
  Q'.eqv_trans _ _ _ (weightedMass_congr w K width (neg_smul p))
    (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

private theorem mass_difference (w : Q') (K width : Nat) (p q : RatPoly) :
    weightedMass w K width (polyAdd p (polyNeg q)) ≈
      weightedMass w K width p + -(weightedMass w K width q) :=
  Q'.eqv_trans _ _ _ (weightedMass_add w K width p (polyNeg q))
    (Q'.add_eqv_congr_left _ _ _ (mass_neg w K width q))

private theorem upper_insertion {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (A B p : RatPoly) (U : Q')
    (PU : Certificate (N width) (polyAdd (polySmul U A) (polyNeg B)))
    (P : Certificate (N width) p) :
    weightedMass w K width (polyMul B p) ≤
      U*weightedMass w K width (polyMul A p) := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK (PU.mul P)
  have halg : RatPolyCoeffEqv
      (polyMul (polyAdd (polySmul U A) (polyNeg B)) p)
      (polyAdd (polySmul U (polyMul A p)) (polyNeg (polyMul B p))) :=
    (((cap_mul_left U A).symm.add (RatPolyCoeffEqv.refl _)).mul_right p).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))) (.var 3))
        (.add (.mul (.var 0) (.mul (.var 1) (.var 3)))
          (.neg (.mul (.var 2) (.var 3))))
        (by decide) (fun | 0 => cap U | 1 => A | 2 => B | _ => p)).trans
        ((cap_mul_left U (polyMul A p)).add (RatPolyCoeffEqv.refl _)))
  have he := Q'.eqv_trans _ _ _ (weightedMass_congr w K width halg)
    (Q'.eqv_trans _ _ _ (mass_difference w K width (polySmul U (polyMul A p)) (polyMul B p))
      (Q'.add_eqv_congr_right _ _ _ (weightedMass_smul w K width U (polyMul A p))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- A genuine Schur square estimate for the ORIGINAL finite transfer,
proved from the positive input and its upper transfer certificate.  No
positivity of f, lower bound for A, or nonzero-norm guard is needed. -/
theorem original_block_terminal_schur_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) {A f : RatPoly}
    (hA : SupportedQuaternionBlocks (N width) A)
    (hf : SupportedQuaternionBlocks (N width) f)
    (PA : Certificate (N width) A) (U : Q') (hU : (0 : Q') ≤ U)
    (PU : Certificate (N width)
      (polyAdd (polySmul U A) (polyNeg (originalBlockTransfer w K width d A)))) :
    weightedMass w K width
        (polyMul (originalBlockTransfer w K width d (polyMul A f))
          (originalBlockTransfer w K width d (polyMul A f))) ≤
      (U*U)*weightedMass w K width (polyMul (polyMul A f) (polyMul A f)) := by
  let SA := originalBlockTransfer w K width d A
  let Sf := originalBlockTransfer w K width d (polyMul A f)
  let p := polyMul A (polyMul f f)
  let H := originalBlockTransfer w K width d p
  have hp : SupportedQuaternionBlocks (N width) p :=
    supported_polyMul hA (supported_polyMul hf hf)
  have Pp : Certificate (N width) p := PA.mul (Certificate.square f hf)
  have PH : Certificate (N width) H :=
    iterateStep_certificate hw0 hw1 K width hK d p hp Pp
  have hn := blockNoise_nonnegative hw0 hw1 K width hK d hA hf PA
  have he : weightedMass w K width (blockNoise w K width d A f) ≈
      weightedMass w K width (polyMul SA H) +
        -(weightedMass w K width (polyMul Sf Sf)) :=
    mass_difference w K width (polyMul SA H) (polyMul Sf Sf)
  have hnoise : weightedMass w K width (polyMul Sf Sf) ≤
      weightedMass w K width (polyMul SA H) :=
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))
  have hfirst := upper_insertion hw0 hw1 K width hK A SA H U PU PH
  have hsym : weightedMass w K width (polyMul A H) ≈
      weightedMass w K width (polyMul p SA) :=
    iterateStep_weighted_symmetric w K width d hp hA
  have hsecond := upper_insertion hw0 hw1 K width hK A SA p U PU Pp
  have hcomm := weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm p SA)
  have hstep : weightedMass w K width (polyMul A H) ≤
      U*weightedMass w K width (polyMul A p) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsym)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) hsecond)
  have hsquare : weightedMass w K width (polyMul A p) ≈
      weightedMass w K width (polyMul (polyMul A f) (polyMul A f)) :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => A | _ => f))
  have hlast := Q'.mul_le_mul_of_nonneg_left _ _ _ hstep hU
  have hpin : U*(U*weightedMass w K width (polyMul A p)) ≈
      (U*U)*weightedMass w K width (polyMul (polyMul A f) (polyMul A f)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv U U _))
      (Q'.mul_eqv_congr_left _ _ _ hsquare)
  exact Q'.le_trans' _ _ _ hnoise (Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hlast (Q'.le_of_eqv hpin)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest.original_block_terminal_schur_square_le

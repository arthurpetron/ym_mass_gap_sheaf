/-
# Signed vector score duality on the SAME original odd marginal

For arbitrary supported frozen directions u, put DA=D_u W and H2=D_u^2 W.
The complete original curvature order gives
H[DA*h]^2 <= H[W*h^2]*(H[H2]+C(w)*H[W*|u|^2]).
No sign or upper bound on H[H2] is assumed: that signed quantity is the
actual ordered double-IBP frontier. No log-score or inverse state is built.
Both original terminal depths and every spatial factor remain in W.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFisherVector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature
  (marginalCurvatureCost marginalCurvatureCutoff
    marginalWeight_frozen_curvature_nonnegative_nearFlat)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature (plaquetteCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (frozenFirstAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct (frozenCurvatureAt)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarCurvatureDualBound (integrated_curvature_signed_dual_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks marginalWeight marginalCurvatureCost pairedDerivativeAt

private theorem headCutoff_le {w : Q'} {K : Nat}
    (hK : marginalCurvatureCutoff w ≤ K) : headCutoff w ≤ K := by
  unfold marginalCurvatureCutoff plaquetteCurvatureCutoff at hK
  omega

private theorem three_supported {blocks : Nat} (p : Fin 3 → RatPoly)
    (hp : ∀ i, SupportedQuaternionBlocks blocks (p i)) :
    SupportedQuaternionBlocks blocks (threeSum p) :=
  supported_add (hp 0) (supported_add (hp 1) (hp 2))

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_one_mul (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (polyMul polyOne p) ≈ quaternionHaar blocks p :=
  haar_of_coeff (RatPolyCoeffEqv.one_mul p)

/-- The full vector estimate is produced from the literal original action,
not a supplied score bound. The ordered Hessian expectation stays signed. -/
theorem marginal_frozen_score_signed_dual_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    {h : RatPoly} (hh : SupportedQuaternionBlocks (N width) h) :
    let W := marginalWeight w K width n
    let s := (baseLinks width).idxOf selected
    quaternionHaar (N width) (polyMul (frozenFirstAt s u W) h) *
      quaternionHaar (N width) (polyMul (frozenFirstAt s u W) h) ≤
    quaternionHaar (N width) (polyMul W (polyMul h h)) *
      (quaternionHaar (N width) (frozenSecondAt s u W) +
        marginalCurvatureCost w*quaternionHaar (N width) (polyMul W (threeSquare u))) := by
  let s := (baseLinks width).idxOf selected
  let W := marginalWeight w K width n
  let C := marginalCurvatureCost w
  let DA := frozenFirstAt s u W
  let H2 := frozenSecondAt s u W
  let G := threeSquare u
  let dd := polyAdd H2 (polyMul (cap C) (polyMul W G))
  have hb := activeBlocks_lt width s hs
  have hW := marginalWeight_supported w K width n
  have hDA : SupportedQuaternionBlocks (N width) DA :=
    three_supported _ (fun i => supported_polyMul (hu i)
      (pairedDerivativeAt_supported hb i hW))
  have hH2 : SupportedQuaternionBlocks (N width) H2 :=
    three_supported _ (fun i => three_supported _ (fun j =>
      supported_polyMul (supported_polyMul (hu i) (hu j))
        (pairedDerivativeAt_supported hb i (pairedDerivativeAt_supported hb j hW))))
  have hG : SupportedQuaternionBlocks (N width) G :=
    three_supported _ (fun i => supported_polyMul (hu i) (hu i))
  have hdd : SupportedQuaternionBlocks (N width) dd :=
    supported_add hH2 (supported_polyMul
      (polySmul_supported (supported_one (N width)) C) (supported_polyMul hW hG))
  have hFC : RatPolyCoeffEqv (frozenCurvatureAt s C W u)
      (polyAdd (polyMul (cap 0) (polyMul W W))
        (polyAdd (polyMul W dd) (polyNeg (polyMul DA DA)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))
        (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 4) (.var 4)))))
      (.add (.mul (.const 0) (.mul (.var 2) (.var 2)))
        (.add (.mul (.var 2) (.add (.var 3) (.mul (.var 0) (.mul (.var 2) (.var 1)))))
          (.neg (.mul (.var 4) (.var 4)))))
      (by decide) (fun | 0 => cap C | 1 => G | 2 => W | 3 => H2 | _ => DA)
  have P : ∀ {R : RatPoly}, Certificate (N width) R →
      (0 : Q') ≤ quaternionHaar (N width) (polyMul R
        (polyAdd (polyMul (cap 0) (polyMul W W))
          (polyAdd (polyMul W dd) (polyNeg (polyMul DA DA))))) := by
    intro R PR
    exact Q'.le_trans' _ _ _
      (marginalWeight_frozen_curvature_nonnegative_nearFlat
        hw0 hw1 K width n hK selected hl hs u hu PR)
      (Q'.le_of_eqv (haar_of_coeff (hFC.mul_left R)))
  have hhead := headCutoff_le hK
  have hdual := integrated_curvature_signed_dual_bound hW hDA hdd hh
    (BF4ExactSlabFixedSpatialActualMarginalWindow.lower_positive hw0 hw1 K width hhead n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.upper_positive hw0 hw1 K width hhead n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.lower_le_upper w K width n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.lowerCertificate hw0 hw1 K width hhead n)
    (BF4ExactSlabFixedSpatialActualMarginalWindow.upperCertificate hw0 hw1 K width hhead n)
    (Certificate.one (N width)) P
  have hddpin : quaternionHaar (N width) dd ≈
      quaternionHaar (N width) H2+C*quaternionHaar (N width) (polyMul W G) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left C (polyMul W G)))
          (quaternionHaar_polySmul (N width) C (polyMul W G))))
  have hright : quaternionHaar (N width) (polyMul polyOne dd) +
      0*quaternionHaar (N width) (polyMul polyOne W) ≈
      quaternionHaar (N width) H2+C*quaternionHaar (N width) (polyMul W G) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_one_mul (N width) dd) (Q'.zero_mul_eqv _))
      (Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) hddpin)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (mul_congr (haar_one_mul (N width) (polyMul DA h)) (haar_one_mul (N width) (polyMul DA h))))
    (Q'.le_trans' _ _ _ hdual (Q'.le_of_eqv
      (mul_congr (haar_one_mul (N width) (polyMul W (polyMul h h))) hright)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFisherVector

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherVector.marginal_frozen_score_signed_dual_bound

/-
# OWN mean versus selected energy in the ORIGINAL odd marginal

The actual paired Fisher dual and degree-one block Casimir give
mu_W(f)^2 <= (marginalCurvatureCost(w)/3)*mu_W(Gamma_s(f)).
W is literally V*g_n*g_(n+1), the partition is its OWN positive odd mass,
and the selected physical link must be active. The source may have arbitrary
spectator coefficients. No zero-mean or weighted-Poincare input is assumed.
This is a fixed-strict-nome estimate, not continuum survival or a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual
import YMGap.Continuum.SU2QuaternionBlockLinearCasimir
import YMGap.Continuum.QuaternionHaarPairedHessianTrace
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
import YMGap.Continuum.RationalListCauchy
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress (Z4Link Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature
  (marginalCurvatureCost marginalCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature (plaquetteCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFisherDual (marginal_paired_score_dual_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
  (incident_mem_baseLinks plaquette_character_degree)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality (blockAngularLaplacian_eq_six)
open YMGap.Continuum.SU2QuaternionBlockLinearCasimir (blockCasimir_linear)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarPairedHessianTrace (paired_second_trace_carrier)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (pairedAt_mul)
open YMGap.Continuum.QPolyHaarPairedAtFrozenBasis (paired_haar_zero)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RationalListCauchy (qsum qsumSquares qsum_sq_le_length_mul_qsumSquares)
open YMGap.Continuum.RationalQuadraticDiscriminant (normalize_squared_bound)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks marginalWeight marginalCurvatureCost pairedDerivativeAt

/-- Literal rational factor; not an opaque estimate. -/
def third : Q' := Q'.mkPos 1 3 (by decide)

private theorem headCutoff_le {w : Q'} {K : Nat}
    (hK : marginalCurvatureCutoff w ≤ K) : headCutoff w ≤ K := by
  unfold marginalCurvatureCutoff plaquetteCurvatureCutoff at hK
  omega

private def threeValue (a : Fin 3 → Q') : Q' := a 0+(a 1+a 2)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_add (blocks : Nat) (r p q : RatPoly) :
    quaternionHaar blocks (polyMul r (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul r p)+quaternionHaar blocks (polyMul r q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right r p q))
    (quaternionHaar_append blocks _ _)

private theorem haar_three (blocks : Nat) (r : RatPoly) (p : Fin 3 → RatPoly) :
    quaternionHaar blocks (polyMul r (threeSum p)) ≈
      threeValue (fun i => quaternionHaar blocks (polyMul r (p i))) :=
  Q'.eqv_trans _ _ _ (haar_add blocks r _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_add blocks r _ _))

private theorem threeValue_mul (c : Q') (a : Fin 3 → Q') :
    threeValue (fun i => c*a i) ≈ c*threeValue a :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.eqv_symm (Q'.mul_add_eqv c (a 1) (a 2))))
    (Q'.eqv_symm (Q'.mul_add_eqv c (a 0) (a 1+a 2)))

private theorem three_cauchy (a : Fin 3 → Q') :
    threeValue a*threeValue a ≤ 3*threeValue (fun i => a i*a i) := by
  have h := qsum_sq_le_length_mul_qsumSquares [a 0,a 1,a 2]
  have ha : qsum [a 0,a 1,a 2] ≈ threeValue a :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (QPoly.q_add_zero_eqv (a 2)))
  have hb : qsumSquares [a 0,a 1,a 2] ≈ threeValue (fun i => a i*a i) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (QPoly.q_add_zero_eqv (a 2*a 2)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mul_congr ha ha))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left 3 _ _ hb)))

/-- The actual paired eigenaction is derived from the original block Casimir,
not supplied as an analytic premise. -/
theorem paired_linear_mean_ward {blocks s : Nat} (hs : s < blocks)
    (W f : RatPoly) (hf : SupportedQuaternionBlocks blocks f)
    (hdegree : HasQuaternionBlockDegree s 1 f) :
    threeValue (fun i => quaternionHaar blocks
      (polyMul (pairedDerivativeAt s i W) (pairedDerivativeAt s i f))) ≈
      3*quaternionHaar blocks (polyMul W f) := by
  let a : Fin 3 → Q' := fun i => quaternionHaar blocks
    (polyMul (pairedDerivativeAt s i W) (pairedDerivativeAt s i f))
  let b : Fin 3 → Q' := fun i => quaternionHaar blocks
    (polyMul W (pairedDerivativeAt s i (pairedDerivativeAt s i f)))
  have hzero (i : Fin 3) : a i+b i ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (haar_of_coeff (pairedAt_mul s i W (pairedDerivativeAt s i f)))
        (quaternionHaar_append blocks _ _)))
      (paired_haar_zero hs i (polyMul W (pairedDerivativeAt s i f)))
  have hsum : threeValue a+threeValue b ≈ 0 :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 3) (.add (.var 4) (.var 5))))
      (.add (.add (.var 0) (.var 3))
        (.add (.add (.var 1) (.var 4)) (.add (.var 2) (.var 5))))
      (by decide) (fun | 0 => a 0 | 1 => a 1 | 2 => a 2 | 3 => b 0 | 4 => b 1 | _ => b 2))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hzero 0)
        (Q'.add_eqv_congr' (hzero 1) (hzero 2))) (by decide))
  have htrace := (paired_second_trace_carrier hs f).trans
    ((RatPolyCoeffEqv.haarCarrier (blockAngularLaplacian_eq_six s f)).symm.trans
      (blockCasimir_linear hs f hf hdegree))
  have hb : threeValue b ≈ (-3)*quaternionHaar blocks (polyMul W f) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_three blocks W _))
      (Q'.eqv_trans _ _ _ (htrace W) (quaternionHaar_polyMul_smul_right blocks (-3) W f))
  have hdiff : threeValue a ≈ -(threeValue b) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.var 0) (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (by decide) (fun | 0 => threeValue a | _ => threeValue b))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hsum (Q'.eqv_refl _)) (QPoly.q_zero_add_eqv _))
  exact Q'.eqv_trans _ _ _ hdiff (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hb)
    (poly_identity_of_normal_eq (.neg (.mul (.const (-3)) (.var 0)))
      (.mul (.const 3) (.var 0)) (by decide)
      (fun _ => quaternionHaar blocks (polyMul W f))))

/-- Raw SAME-marginal mean-energy inequality, valid with arbitrary spectator
coefficients. The cost is one third of the produced full curvature cost. -/
theorem marginal_paired_mean_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f)
    (hdegree : HasQuaternionBlockDegree ((baseLinks width).idxOf selected) 1 f) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) *
      quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) ≤
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (threeSquare (fun i => pairedDerivativeAt ((baseLinks width).idxOf selected) i f))) *
      ((third*marginalCurvatureCost w)*quaternionHaar (N width) (marginalWeight w K width n)) := by
  let s := (baseLinks width).idxOf selected
  let W := marginalWeight w K width n
  let Z := quaternionHaar (N width) W
  let F := quaternionHaar (N width) (polyMul W f)
  let C := marginalCurvatureCost w
  let a : Fin 3 → Q' := fun i => quaternionHaar (N width)
    (polyMul (pairedDerivativeAt s i W) (pairedDerivativeAt s i f))
  let E : Fin 3 → Q' := fun i => quaternionHaar (N width)
    (polyMul W (polyMul (pairedDerivativeAt s i f) (pairedDerivativeAt s i f)))
  have hb := activeBlocks_lt width s hs
  have hi (i : Fin 3) : a i*a i ≤ (C*Z)*E i :=
    Q'.le_trans' _ _ _
      (marginal_paired_score_dual_bound hw0 hw1 K width n hK selected hl hs i
        (pairedDerivativeAt_supported hb i hf))
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  have hsum : threeValue (fun i => a i*a i) ≤ (C*Z)*threeValue E :=
    Q'.le_trans' _ _ _ (Q'.add_le_add (hi 0) (Q'.add_le_add (hi 1) (hi 2)))
      (Q'.le_of_eqv (threeValue_mul (C*Z) E))
  have hw := paired_linear_mean_ward hb W f hf hdegree
  have hraw : (3*F)*(3*F) ≤ 3*((C*Z)*threeValue E) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mul_congr hw hw))
      (Q'.le_trans' _ _ _ (three_cauchy a)
        (Q'.mul_le_mul_of_nonneg_left _ _ 3 hsum (by decide)))
  let ninth : Q' := Q'.mkPos 1 9 (by decide)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ ninth hraw (by decide)
  have hleft : ninth*((3*F)*(3*F)) ≈ F*F :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.mul (.const 3) (.var 0)) (.mul (.const 3) (.var 0))))
      (.mul (.mul (.var 1) (.const 9)) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => F | _ => ninth))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (by decide : ninth*9 ≈ 1)) (Q'.one_mul_eqv _))
  have hright : ninth*(3*((C*Z)*threeValue E)) ≈ threeValue E*((third*C)*Z) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 3) (.mul (.const 3) (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (.mul (.mul (.var 3) (.const 3)) (.mul (.var 2) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => C | 1 => Z | 2 => threeValue E | _ => ninth))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (by decide : ninth*3 ≈ third))
        (poly_identity_of_normal_eq
          (.mul (.var 3) (.mul (.var 2) (.mul (.var 0) (.var 1))))
          (.mul (.var 2) (.mul (.mul (.var 3) (.var 0)) (.var 1)))
          (by decide) (fun | 0 => C | 1 => Z | 2 => threeValue E | _ => third)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hright
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (haar_three (N width) W
        (fun i => polyMul (pairedDerivativeAt s i f) (pairedDerivativeAt s i f))))))))

/-- The OWN mean and energy use exactly the SAME positive odd partition. -/
theorem marginal_paired_own_mean_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f)
    (hdegree : HasQuaternionBlockDegree ((baseLinks width).idxOf selected) 1 f) :
    let W := marginalWeight w K width n
    let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
    let m := normalizedMoment (N width) W f hZ
    let r := Q'.recipPos (quaternionHaar (N width) W) hZ
    m*m ≤ (third*marginalCurvatureCost w)*
      (r*quaternionHaar (N width) (polyMul W
        (threeSquare (fun i => pairedDerivativeAt ((baseLinks width).idxOf selected) i f)))) := by
  let W := marginalWeight w K width n
  let F := quaternionHaar (N width) (polyMul W f)
  let r := Q'.recipPos (quaternionHaar (N width) W)
    (mass_positive hw0 hw1 K width (headCutoff_le hK) n)
  have hn := normalize_squared_bound _ _ _ _
    (mass_positive hw0 hw1 K width (headCutoff_le hK) n)
    (marginal_paired_mean_square_bound hw0 hw1 K width n hK selected hl hs f hf hdegree)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (mul_congr (Q'.mul_comm_eqv F r) (Q'.mul_comm_eqv F r))) hn

/-- Exact original character-one plaquette consumer; its degree is produced
by the actual incident physical link, not an unproved source hypothesis. -/
theorem plaquette_character_mean_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (face : Z4Plaq) (hface : face ∈ spatialFaces width)
    (selected : Z4Link) (hl : selected ∈ edgesOf face)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width) :
    let f := characterPolynomial (plaquette width face).scalar 1
    quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) *
      quaternionHaar (N width) (polyMul (marginalWeight w K width n) f) ≤
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (threeSquare (fun i => pairedDerivativeAt ((baseLinks width).idxOf selected) i f))) *
      ((third*marginalCurvatureCost w)*quaternionHaar (N width) (marginalWeight w K width n)) :=
  marginal_paired_mean_square_bound hw0 hw1 K width n hK selected
    (incident_mem_baseLinks hface hl) hs _
    (character_supported (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
    (plaquette_character_degree width hface hl)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean.third
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean.paired_linear_mean_ward
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean.marginal_paired_mean_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean.marginal_paired_own_mean_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean.plaquette_character_mean_square_bound

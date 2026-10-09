/-
# SAME original signed Fisher/Ward join for the growing Wilson square

The actual ordered Hessian expectation removes the previously unbounded
signed term in the vector dual. No weight, center, chronological mass or
source is replaced. The surviving cost remains nome-dependent; this is
not a useful relative time-loss estimate or continuum survival theorem.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian
import YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean
import YMGap.Continuum.QPolyHaarPairedAtCenteredWard

namespace YMGap.Continuum.BF4DyadicWilsonSquareFisherWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameAt
  (pairedDerivativeAt pairedDerivativeAt_supported)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (frozenFirstAt)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarCenteredLinearWard
  (normalized_centered_cross_own_mean)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature
  (marginalCurvatureCost marginalCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature (plaquetteCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFisherVector
  (marginal_frozen_score_signed_dual_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean
  (third marginal_paired_own_mean_square_bound)
open YMGap.Continuum.BF4DyadicWilsonSquare (side square paddedSquare paddedSquare_edges)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
  (observableBlocks observableBlocks_lt)
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_character_degree)
open YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian
  (paddedSquare_original_frozen_hessian_haar)
open YMGap.Continuum.QPolyHaarPairedAtCenteredWard

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks marginalWeight marginalCurvatureCost pairedDerivativeAt

private theorem headCutoff_le {w : Q'} {K : Nat}
    (hK : marginalCurvatureCutoff w ≤ K) : headCutoff w ≤ K := by
  unfold marginalCurvatureCutoff plaquetteCurvatureCutoff at hK
  omega

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The active physical link is produced from the literal padded-square
membership, rather than added as a new analytic or geometry premise. -/
theorem paddedSquare_original_signed_vector_dual {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n scale : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth)
    {h : RatPoly} (hh : SupportedQuaternionBlocks (N width) h) :
    let W := marginalWeight w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let u := fun i => pairedDerivativeAt block i f
    let b := quaternionHaar (N width) (polyMul (frozenFirstAt block u W) h)
    b*b ≤ quaternionHaar (N width) (polyMul W (polyMul h h)) *
      (48*quaternionHaar (N width) W +
        (marginalCurvatureCost w+(-16))*
          quaternionHaar (N width) (polyMul W (threeSquare u))) := by
  let W := marginalWeight w K width n
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let u := fun i => pairedDerivativeAt block i f
  have hs := observableBlocks_lt scale width hwidth block hb
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hu (i : Fin 3) := pairedDerivativeAt_supported hs i hf
  have hmem := of_decide_eq_true (List.mem_filter.mp hb).2
  obtain ⟨edge,he,hblock⟩ := List.mem_map.mp hmem
  have hl := (paddedSquare scale width hwidth).physical edge he
  have hactive : (baseLinks width).idxOf edge.link ∈ activeBlocks width := by
    apply BF4ExactSlabFixedSpatialWilsonActivePadding.source_edges_active_after_padding
      hwidth (square scale) edge
    rw [← paddedSquare_edges scale width hwidth]
    exact he
  have hd := marginal_frozen_score_signed_dual_bound hw0 hw1 K width n hK
    edge.link hl hactive u hu hh
  dsimp only at hd
  rw [hblock] at hd
  have hH := paddedSquare_original_frozen_hessian_haar w K width n scale hwidth block hb
  have hr : quaternionHaar (N width)
      (BF4ExactSlabFixedSpatialPlaquetteFrozenHessian.frozenSecondAt block u W) +
      marginalCurvatureCost w*quaternionHaar (N width) (polyMul W (threeSquare u)) ≈
      48*quaternionHaar (N width) W +
        (marginalCurvatureCost w+(-16))*
          quaternionHaar (N width) (polyMul W (threeSquare u)) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hH (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.const 48) (.var 0)) (.mul (.const (-16)) (.var 1)))
          (.mul (.var 2) (.var 1)))
        (.add (.mul (.const 48) (.var 0))
          (.mul (.add (.var 2) (.const (-16))) (.var 1)))
        (by decide) (fun
          | 0 => quaternionHaar (N width) W
          | 1 => quaternionHaar (N width) (polyMul W (threeSquare u))
          | _ => marginalCurvatureCost w))
  exact Q'.le_trans' _ _ _ hd (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hr))

/-- Literal growing-source mean bound, using its OWN original positive mass
and selected energy. The source degree and active link are both produced. -/
theorem paddedSquare_original_own_mean_square_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n scale : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let W := marginalWeight w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
    let m := normalizedMoment (N width) W f hZ
    let r := Q'.recipPos (quaternionHaar (N width) W) hZ
    m*m ≤ (third*marginalCurvatureCost w)*
      (r*quaternionHaar (N width) (polyMul W
        (threeSquare (fun i => pairedDerivativeAt block i f)))) := by
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hmem := of_decide_eq_true (List.mem_filter.mp hb).2
  obtain ⟨edge,he,hblock⟩ := List.mem_map.mp hmem
  have hl := (paddedSquare scale width hwidth).physical edge he
  have hactive : (baseLinks width).idxOf edge.link ∈ activeBlocks width := by
    apply BF4ExactSlabFixedSpatialWilsonActivePadding.source_edges_active_after_padding
      hwidth (square scale) edge
    rw [← paddedSquare_edges scale width hwidth]
    exact he
  have hdegree := paddedSquare_character_degree scale width hwidth block hb
  have hm := marginal_paired_own_mean_square_bound hw0 hw1 K width n hK
    edge.link hl hactive _ hf (by rw [hblock]; exact hdegree)
  dsimp only at hm
  rw [hblock] at hm
  exact hm

private theorem clear_mass {blocks : Nat} (W : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks W) (a v : Q')
    (h : a*Q'.recipPos (quaternionHaar blocks W) hZ ≈ v) :
    a ≈ quaternionHaar blocks W*v := by
  let Z := quaternionHaar blocks W
  let r := Q'.recipPos Z hZ
  have hc : Z*(a*r) ≈ a :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => Z | 1 => a | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv a))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hc) (Q'.mul_eqv_congr_left Z _ _ h)

private theorem own_cross {blocks : Nat} (hblocks : 0 < blocks) (W f : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks W) :
    let m := normalizedMoment blocks W f hZ
    let h := polyAdd f (polySmul (-m) polyOne)
    quaternionHaar blocks (polyMul W (polyMul h f)) ≈
      quaternionHaar blocks W*normalizedVariance blocks W f hZ := by
  have hlen : blocks-1+1 = blocks := Nat.sub_add_cancel hblocks
  have hn := normalized_centered_cross_own_mean (blocks-1) W f
    (by rw [hlen]; exact hZ)
  simp only [hlen] at hn
  exact clear_mass W hZ _ _ hn

private theorem own_square {blocks : Nat} (W f : RatPoly)
    (P : Certificate blocks W) (hf : SupportedQuaternionBlocks blocks f)
    (hZ : (0 : Q') < quaternionHaar blocks W) :
    let m := normalizedMoment blocks W f hZ
    let h := polyAdd f (polySmul (-m) polyOne)
    quaternionHaar blocks (polyMul W (polyMul h h)) ≈
      quaternionHaar blocks W*normalizedVariance blocks W f hZ := by
  let m := normalizedMoment blocks W f hZ
  let h := polyAdd f (polySmul (-m) polyOne)
  have he : RatPolyCoeffEqv (shifted f m) h :=
    (RatPolyCoeffEqv.one_smul f).add (RatPolyCoeffEqv.refl _)
  have hn : quaternionHaar blocks (polyMul W (polyMul h h))*
      Q'.recipPos (quaternionHaar blocks W) hZ ≈ normalizedVariance blocks W f hZ :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (haar_of_coeff ((he.symm.mul he.symm).mul_left W))) (own_mean_pin P hf hZ)
  exact clear_mass W hZ _ _ hn

/-- The signed centered residual has been eliminated against the SAME
original variance and selected energy. This retains the actual negative
source correction; no variance floor or scaling estimate is asserted. -/
theorem paddedSquare_original_own_variance_fisher_ward {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n scale : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let W := marginalWeight w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
    let Z := quaternionHaar (N width) W
    let v := normalizedVariance (N width) W f hZ
    let E := quaternionHaar (N width)
      (polyMul W (threeSquare (fun i => pairedDerivativeAt block i f)))
    (3*(Z*v)+(-E))*(3*(Z*v)+(-E)) ≤
      (Z*v)*(48*Z+(marginalCurvatureCost w+(-16))*E) := by
  let W := marginalWeight w K width n
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
  let Z := quaternionHaar (N width) W
  let v := normalizedVariance (N width) W f hZ
  let m := normalizedMoment (N width) W f hZ
  let h := polyAdd f (polySmul (-m) polyOne)
  let u := fun i => pairedDerivativeAt block i f
  let E := quaternionHaar (N width) (polyMul W (threeSquare u))
  let b := quaternionHaar (N width) (polyMul (frozenFirstAt block u W) h)
  have hs := observableBlocks_lt scale width hwidth block hb
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hh := supported_add hf (polySmul_supported (supported_one (N width)) (-m))
  have hdegree := paddedSquare_character_degree scale width hwidth block hb
  have hX := own_cross (Nat.lt_of_le_of_lt (Nat.zero_le block) hs) W f hZ
  have hA := own_square W f (marginalCertificate hw0 hw1 K width (headCutoff_le hK) n) hf hZ
  have hw : E+b ≈ 3*(Z*v) :=
    Q'.eqv_trans _ _ _ (pairedAt_centered_ward hs W f m hf hdegree)
      (Q'.mul_eqv_congr_left 3 _ _ hX)
  have hbpin : b ≈ 3*(Z*v)+(-E) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.var 0) (.add (.add (.var 1) (.var 0)) (.neg (.var 1)))
      (by decide) (fun | 0 => b | _ => E))
      (Q'.add_eqv_congr' hw (Q'.eqv_refl _))
  have hd := paddedSquare_original_signed_vector_dual hw0 hw1 K width n scale hK
    hwidth block hb hh
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mul_congr hbpin hbpin))
    (Q'.le_trans' _ _ _ hd (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hA)))

end YMGap.Continuum.BF4DyadicWilsonSquareFisherWard

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_signed_vector_dual
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_own_mean_square_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_own_variance_fisher_ward

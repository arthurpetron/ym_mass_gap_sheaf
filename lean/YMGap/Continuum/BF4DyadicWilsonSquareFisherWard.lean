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
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction

namespace YMGap.Continuum.BF4DyadicWilsonSquareFisherWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
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

private theorem gap_order {a b g : Q'} (hg : (0 : Q') ≤ g)
    (he : b + -a ≈ g) : a ≤ b :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hg (Q'.ge_of_eqv he))

private theorem square_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    a*a ≤ b*b :=
  Q'.mul_le_mul_of_nonneg hab hab (Q'.le_trans' _ _ _ ha hab) ha

/-- Scalar consequence of the paid mean and signed Ward laws.  The constant
is explicit data in the statement, with no positive variance premise. -/
private theorem scalar_fisher_variance_floor (C v A : Q')
    (hC : (0 : Q') ≤ C) (hv : (0 : Q') ≤ v) (hA : (0 : Q') ≤ A)
    (hamp : (12 : Q') ≤ (C+3)*A+3*v)
    (hward : (3*v+(-A))*(3*v+(-A)) ≤ v*(48+(C+(-16))*A)) :
    (1 : Q') ≤ 4*(C+3)*(C+3)*v := by
  let L := C+3
  let X := L*A
  let b := 4*L*L*v
  have hL3 : (3 : Q') ≤ L := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg 3 C hC) (Q'.le_of_eqv (Q'.add_comm_eqv 3 C))
  have hL : (0 : Q') ≤ L := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 3) hL3
  have hLp : (0 : Q') < L := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 3) hL3
  have hX : (0 : Q') ≤ X := Q'.mul_nonneg _ _ hL hA
  by_cases hb : (1 : Q') ≤ b
  · exact hb
  · have hb1 : b ≤ (1 : Q') := by
      change ¬ ((1 : Q').num * (b.den : Int) ≤ b.num * ((1 : Q').den : Int)) at hb
      change b.num * ((1 : Q').den : Int) ≤ (1 : Q').num * (b.den : Int)
      omega
    have hLL : (9 : Q') ≤ L*L := Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (by decide : ((3 : Q')*3) ≈ 9)) (square_mono (by decide) hL3)
    have h36 : (36 : Q') ≤ 4*(L*L) := Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (by decide : ((4 : Q')*9) ≈ 36))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hLL (by decide))
    have hvb : v ≤ b := by
      have h := Q'.mul_le_mul_of_nonneg_right _ _ v
        (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 36) h36) hv
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv v))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
          (Q'.mul_eqv_congr_right _ _ v (Q'.eqv_symm (Q'.mul_assoc_eqv 4 L L)))))
    have hv1 : v ≤ (1 : Q') := Q'.le_trans' _ _ _ hvb hb1
    have h3v : 3*v ≤ (3 : Q') := Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 3 hv1 (by decide))
      (Q'.le_of_eqv (Q'.mul_one_eqv 3))
    have hX3 : (12 : Q') ≤ X+3 := Q'.le_trans' _ _ _ hamp
      (Q'.add_le_add_left X _ _ h3v)
    have hX9 : (9 : Q') ≤ X := by
      have h := Q'.add_le_add_right _ _ (-3) hX3
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : ((12 : Q')+(-3)) ≈ 9))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.const 3)) (.const (-3))) (.var 0)
          (by decide) (fun _ => X))))
    have h6L : (6 : Q') ≤ 4*L := Q'.le_trans' _ _ _ (by decide : (6 : Q') ≤ 12)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : ((4 : Q')*3) ≈ 12))
        (Q'.mul_le_mul_of_nonneg_left _ _ 4 hL3 (by decide)))
    have h6Lv : 6*(L*v) ≤ b := Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (L*v) h6L (Q'.mul_nonneg _ _ hL hv))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.var 0)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.mul (.const 4) (.var 0)) (.var 0)) (.var 1))
        (by decide) (fun | 0 => L | _ => v)))
    have h6vA : 6*v ≤ A := by
      apply Q'.le_of_mul_le_mul_left (c := L) _ hLp
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 6) (.var 1)))
        (.mul (.const 6) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => L | _ => v)))
        (Q'.le_trans' _ _ _ h6Lv (Q'.le_trans' _ _ _ hb1
          (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 9) hX9)))
    let t := A+(-(3*v))
    have ht : (0 : Q') ≤ t := Q'.sub_nonneg_of_le
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ v (by decide : (3 : Q') ≤ 6) hv) h6vA)
    have hAt : A ≤ 2*t := gap_order (Q'.sub_nonneg_of_le h6vA)
      (poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.add (.var 0) (.neg (.mul (.const 3) (.var 1)))))
          (.neg (.var 0)))
        (.add (.var 0) (.neg (.mul (.const 6) (.var 1))))
        (by decide) (fun | 0 => A | _ => v))
    have hAres : A*A ≤ 4*((3*v+(-A))*(3*v+(-A))) :=
      Q'.le_trans' _ _ _ (square_mono hA hAt)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.mul (.const 2) (.add (.var 0) (.neg (.mul (.const 3) (.var 1)))))
            (.mul (.const 2) (.add (.var 0) (.neg (.mul (.const 3) (.var 1))))))
          (.mul (.const 4) (.mul
            (.add (.mul (.const 3) (.var 1)) (.neg (.var 0)))
            (.add (.mul (.const 3) (.var 1)) (.neg (.var 0)))))
          (by decide) (fun | 0 => A | _ => v)))
    have hcost : (C+(-16))*A ≤ C*A := gap_order
      (Q'.mul_nonneg 16 A (by decide) hA)
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.add (.var 0) (.const (-16))) (.var 1))))
        (.mul (.const 16) (.var 1)) (by decide) (fun | 0 => C | _ => A))
    have hres : (3*v+(-A))*(3*v+(-A)) ≤ v*(48+C*A) :=
      Q'.le_trans' _ _ _ hward (Q'.mul_le_mul_of_nonneg_left _ _ v
        (Q'.add_le_add_left 48 _ _ hcost) hv)
    have hAA : A*A ≤ 4*(v*(48+C*A)) := Q'.le_trans' _ _ _ hAres
      (Q'.mul_le_mul_of_nonneg_left _ _ 4 hres (by decide))
    have hXX : X*X ≤ b*(48+C*A) := by
      have h := Q'.mul_le_mul_of_nonneg_left _ _ (L*L) hAA (Q'.mul_nonneg _ _ hL hL)
      have he₁ : (L*L)*(A*A) ≈ X*X := poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => L | _ => A)
      have he₂ : (L*L)*(4*(v*(48+C*A))) ≈ b*(48+C*A) :=
        poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 0)) (.mul (.const 4) (.mul (.var 1) (.var 2))))
          (.mul (.mul (.mul (.mul (.const 4) (.var 0)) (.var 0)) (.var 1)) (.var 2))
          (by decide) (fun | 0 => L | 1 => v | _ => 48+C*A)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he₁)
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he₂))
    have hCA : (0 : Q') ≤ C*A := Q'.mul_nonneg _ _ hC hA
    have h48 : (0 : Q') ≤ 48+C*A := Q'.zero_le_add _ _ (by decide) hCA
    have hupper : X*X ≤ 48+X := Q'.le_trans' _ _ _ hXX
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hb1 h48)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (48+C*A)))
          (Q'.add_le_add_left 48 _ _ (Q'.mul_le_mul_of_nonneg_right _ _ A
            (Q'.add_le_self_of_nonneg C 3 (by decide)) hA))))
    have h9X : 9*X ≤ X*X := Q'.mul_le_mul_of_nonneg_right _ _ X hX9 hX
    have h8X : 8*X ≤ (48 : Q') := by
      have h := Q'.add_le_add_right _ _ (-X) (Q'.le_trans' _ _ _ h9X hupper)
      have he₁ : 9*X+(-X) ≈ 8*X := poly_identity_of_normal_eq
        (.add (.mul (.const 9) (.var 0)) (.neg (.var 0)))
        (.mul (.const 8) (.var 0)) (by decide) (fun _ => X)
      have he₂ : (48+X)+(-X) ≈ (48 : Q') := poly_identity_of_normal_eq
        (.add (.add (.const 48) (.var 0)) (.neg (.var 0)))
        (.const 48) (by decide) (fun _ => X)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he₁)
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he₂))
    have h72 : (72 : Q') ≤ 48 := Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (by decide : ((8 : Q')*9) ≈ 72))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ 8 hX9 (by decide)) h8X)
    exact False.elim ((by decide : ¬ ((72 : Q') ≤ 48)) h72)

private theorem haar_weighted_add (blocks : Nat) (W p q : RatPoly) :
    quaternionHaar blocks (polyMul W (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul W p)+quaternionHaar blocks (polyMul W q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W p q))
    (quaternionHaar_append blocks _ _)

/-- A produced division-free floor for the OWN variance of the literal
padded Wilson square under its complete original marginal `V*g_n*g_(n+1)`.
It is uniform in the finite square size, width and depth at the existing
curvature cutoff.  This is an initial variance estimate, not late retention,
shifted H1, continuum survival or a physical excitation-gap statement. -/
theorem paddedSquare_original_own_variance_fisher_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n scale : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let W := marginalWeight w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
    (1 : Q') ≤ 4*(marginalCurvatureCost w+3)*(marginalCurvatureCost w+3)*
      normalizedVariance (N width) W f hZ := by
  let W := marginalWeight w K width n
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
  let Z := quaternionHaar (N width) W
  let r := Q'.recipPos Z hZ
  let m := normalizedMoment (N width) W f hZ
  let v := normalizedVariance (N width) W f hZ
  let u := fun i => pairedDerivativeAt block i f
  let E := quaternionHaar (N width) (polyMul W (threeSquare u))
  let A := r*E
  let C := marginalCurvatureCost w
  let Q := normalizedMoment (N width) W (polyMul f f) hZ
  have hs := observableBlocks_lt scale width hwidth block hb
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hu (i : Fin 3) := pairedDerivativeAt_supported hs i hf
  have P := marginalCertificate hw0 hw1 K width (headCutoff_le hK) n
  have hv : (0 : Q') ≤ v :=
    QuaternionHaarIntervalSecondMoment.normalizedVariance_nonnegative P hZ hf
  have hraw (i : Fin 3) :
      (0 : Q') ≤ quaternionHaar (N width) (polyMul W (polyMul (u i) (u i))) :=
    Q'.le_trans' _ _ _ (P.square_insertion_nonnegative (u i) (hu i))
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have hEsplit : E ≈
      quaternionHaar (N width) (polyMul W (polyMul (u 0) (u 0)))+
        (quaternionHaar (N width) (polyMul W (polyMul (u 1) (u 1)))+
          quaternionHaar (N width) (polyMul W (polyMul (u 2) (u 2)))) :=
    Q'.eqv_trans _ _ _ (haar_weighted_add (N width) W _ _)
      (Q'.add_eqv_congr_left _ _ _ (haar_weighted_add (N width) W _ _))
  have hE0 : (0 : Q') ≤ E := Q'.le_trans' _ _ _
    (Q'.zero_le_add _ _ (hraw 0) (Q'.zero_le_add _ _ (hraw 1) (hraw 2)))
    (Q'.ge_of_eqv hEsplit)
  have hA : (0 : Q') ≤ A := Q'.mul_nonneg _ _
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ)) hE0
  have hgamma : HaarCarrierEqv (N width) (threeSquare u)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) :=
    (RatPolyCoeffEqv.haarCarrier
      (QuaternionHaarPairedHessianTrace.paired_gradient_square_pin block f)).trans
      (BF4DyadicWilsonSquareWardMoments.paddedSquare_block_gamma scale width hwidth block hb)
  have hG : E ≈ quaternionHaar (N width)
      (polyMul W (polyAdd (cap 4) (polySmul (-1) (polyMul f f)))) :=
    Q'.eqv_trans _ _ _ (hgamma W)
      (haar_of_coeff (((RatPolyCoeffEqv.refl (cap 4)).add
        (QuaternionHaarAngularCarrier.neg_smul (polyMul f f))).mul_left W))
  have hApin : A ≈ (4 : Q')+(-Q) := by
    have hfirst : A ≈ normalizedMoment (N width) W
        (polyAdd (cap 4) (polySmul (-1) (polyMul f f))) hZ :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r E)
        (Q'.mul_eqv_congr_right _ _ r hG)
    have hconst : normalizedMoment (N width) W (cap 4) hZ ≈ (4 : Q') :=
      Q'.eqv_trans _ _ _
        (QuaternionHaarNormalizedMomentLinear.normalizedMoment_smul hZ)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _
          (QuaternionHaarNormalizedMomentLinear.normalizedMoment_one hZ))
          (Q'.mul_one_eqv 4))
    have hneg : normalizedMoment (N width) W (polySmul (-1) (polyMul f f)) hZ ≈ -Q :=
      Q'.eqv_trans _ _ _
        (QuaternionHaarNormalizedMomentLinear.normalizedMoment_smul hZ)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => Q))
    exact Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _
      (QuaternionHaarNormalizedMomentLinear.normalizedMoment_add hZ)
      (Q'.add_eqv_congr' hconst hneg))
  have hamp : m*m+v+A ≈ (4 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hApin)
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 0))
          (.add (.var 1) (.neg (.mul (.var 0) (.var 0)))))
          (.add (.const 4) (.neg (.var 1))))
        (.const 4) (by decide) (fun | 0 => m | _ => Q))
  have hm := paddedSquare_original_own_mean_square_bound hw0 hw1 K width n scale
    hK hwidth block hb
  have hm3 : 3*(m*m) ≤ C*A := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ 3 hm (by decide)
    have he : 3*((third*C)*A) ≈ C*A :=
      Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.const 3) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (.mul (.mul (.const 3) (.var 0)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => third | 1 => C | _ => A))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (C*A) (by decide : ((3 : Q')*third) ≈ 1))
          (Q'.one_mul_eqv (C*A)))
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)
  have hamp12 : (12 : Q') ≤ (C+3)*A+3*v := by
    have hleft : (3*(m*m)+3*v)+3*A ≈ (12 : Q') :=
      Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.add (.add (.mul (.const 3) (.var 0)) (.mul (.const 3) (.var 1)))
          (.mul (.const 3) (.var 2)))
        (.mul (.const 3) (.add (.add (.var 0) (.var 1)) (.var 2)))
        (by decide) (fun | 0 => m*m | 1 => v | _ => A))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 3 _ _ hamp)
          (by decide : ((3 : Q')*4) ≈ 12))
    have hright : (C*A+3*v)+3*A ≈ (C+3)*A+3*v := poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.mul (.const 3) (.var 2)))
        (.mul (.const 3) (.var 1)))
      (.add (.mul (.add (.var 0) (.const 3)) (.var 1)) (.mul (.const 3) (.var 2)))
      (by decide) (fun | 0 => C | 1 => A | _ => v)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (3*A)
        (Q'.add_le_add_right _ _ (3*v) hm3)) (Q'.le_of_eqv hright))
  have hE : E ≈ Z*A := clear_mass W hZ E A (Q'.mul_comm_eqv E r)
  have hWard := paddedSquare_original_own_variance_fisher_ward hw0 hw1
    K width n scale hK hwidth block hb
  have hres : 3*(Z*v)+(-E) ≈ Z*(3*v+(-A)) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hE))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 3) (.mul (.var 0) (.var 1)))
          (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.mul (.const 3) (.var 1)) (.neg (.var 2))))
        (by decide) (fun | 0 => Z | 1 => v | _ => A))
  have hleft : (3*(Z*v)+(-E))*(3*(Z*v)+(-E)) ≈
      (Z*Z)*((3*v+(-A))*(3*v+(-A))) :=
    Q'.eqv_trans _ _ _ (mul_congr hres hres)
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => Z | _ => 3*v+(-A)))
  have hright : (Z*v)*(48*Z+(C+(-16))*E) ≈
      (Z*Z)*(v*(48+(C+(-16))*A)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Z*v) _ _
      (Q'.add_eqv_congr_left (48*Z) _ _ (Q'.mul_eqv_congr_left (C+(-16)) _ _ hE)))
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.add (.mul (.const 48) (.var 0)) (.mul (.var 2) (.mul (.var 0) (.var 3)))))
        (.mul (.mul (.var 0) (.var 0))
          (.mul (.var 1) (.add (.const 48) (.mul (.var 2) (.var 3)))))
        (by decide) (fun | 0 => Z | 1 => v | 2 => C+(-16) | _ => A))
  have hnormalized : (3*v+(-A))*(3*v+(-A)) ≤ v*(48+(C+(-16))*A) :=
    Q'.le_of_mul_le_mul_left (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hWard (Q'.le_of_eqv hright))) (Q'.mul_pos hZ hZ)
  exact scalar_fisher_variance_floor C v A
    (BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_nonnegative hw0 hw1)
    hv hA hamp12 hnormalized

/-- Explicit nome-defect squared floor for the SAME original finite OWN
variance: equivalently `v ≥ (1-w)^2/7396`.  The division-free statement keeps
the original partition, cutoff, observable and normalization.  It concerns
initial variance only, with no late-time or physical survival conclusion. -/
theorem paddedSquare_original_own_variance_nome_defect_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n scale : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let W := marginalWeight w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
    ((1 : Q')-w)*((1 : Q')-w) ≤
      7396*normalizedVariance (N width) W f hZ := by
  let W := marginalWeight w K width n
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let hZ := mass_positive hw0 hw1 K width (headCutoff_le hK) n
  let v := normalizedVariance (N width) W f hZ
  let C := marginalCurvatureCost w
  let L := C+3
  let delta := (1 : Q')-w
  have hfloor := paddedSquare_original_own_variance_fisher_floor hw0 hw1
    K width n scale hK hwidth block hb
  have hv : (0 : Q') ≤ v := QuaternionHaarIntervalSecondMoment.normalizedVariance_nonnegative
    (marginalCertificate hw0 hw1 K width (headCutoff_le hK) n) hZ
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)
  have hC := BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_nonnegative hw0 hw1
  have hL : (0 : Q') ≤ L := Q'.zero_le_add _ _ hC (by decide)
  have hd : (0 : Q') ≤ delta := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hdL : (0 : Q') ≤ delta*L := Q'.mul_nonneg _ _ hd hL
  have hcap := BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_add_three_nome_defect_upper hw0 hw1
  have hsquare : (delta*L)*(delta*L) ≤ (1849 : Q') :=
    Q'.le_trans' _ _ _ (square_mono hdL hcap)
      (Q'.le_of_eqv (by decide : ((43 : Q')*43) ≈ 1849))
  have hfour : 4*((delta*L)*(delta*L)) ≤ (7396 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 4 hsquare (by decide))
      (Q'.le_of_eqv (by decide : ((4 : Q')*1849) ≈ 7396))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (delta*delta) hfloor
    (Q'.mul_nonneg _ _ hd hd)
  have hregroup : (delta*delta)*(4*L*L*v) ≈
      (4*((delta*L)*(delta*L)))*v := poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0))
      (.mul (.mul (.mul (.const 4) (.var 1)) (.var 1)) (.var 2)))
    (.mul (.mul (.const 4)
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))) (.var 2))
    (by decide) (fun | 0 => delta | 1 => L | _ => v)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (delta*delta)))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
      (Q'.mul_le_mul_of_nonneg_right _ _ v hfour hv)))

end YMGap.Continuum.BF4DyadicWilsonSquareFisherWard

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_signed_vector_dual
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_own_mean_square_bound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_own_variance_fisher_ward
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_own_variance_fisher_floor
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherWard.paddedSquare_original_own_variance_nome_defect_floor

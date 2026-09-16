/-
# Volume-independent comparison with the actual one-link star deleted

At every rational 0<w<1, late original heat prefixes have explicit positive
floors and finite caps. A link meets at most six physical faces, so deleting
only those factors costs constants depending on w, not the volume or cutoff.
All complementary factors and all shared links remain in the Haar integral.

The final comparison is normalized by cross multiplication with the two
actual partition functions. This is a star-deleted free-link reference, NOT
the original conditional update kernel, a spatial contraction, or a gap.
No lower bound uniform as w approaches one is asserted.
-/

import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.BF4ExactSlabLinkStarGeometry

namespace YMGap.Continuum.BF4ExactSlabLocalStarComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

def localFloor (w : Q') : Q' := Q'.min' (headFloor w) 1
def localCap (w : Q') : Q' := 1 + prefixCap w
def lowerFactor (w : Q') : Q' := (localFloor w)^6
def upperFactor (w : Q') : Q' := (localCap w)^6
def starRatio (w : Q') : Q' := HKConv.divPos (lowerFactor w) (upperFactor w)

theorem localFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < localFloor w := by
  unfold localFloor Q'.min'
  split
  · exact headFloor_positive hw0 hw1
  · decide

theorem one_le_localCap {w : Q'} (hw0 : (0 : Q') < w) : (1 : Q') ≤ localCap w :=
  Q'.add_le_self_of_nonneg 1 _ (prefixCap_nonnegative hw0)

theorem lowerFactor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < lowerFactor w := HKPos.pow_pos (localFloor_positive hw0 hw1) 6

theorem upperFactor_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < upperFactor w :=
  HKPos.pow_pos (Q'.pos_add_nonneg (by decide : (0 : Q') < 1) (prefixCap_nonnegative hw0)) 6

theorem starRatio_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < starRatio w :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (lowerFactor_positive hw0 hw1))

private theorem pow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x^n ≤ y^n
  | 0 => Q'.le_refl' 1
  | n+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hxy (Q'.pow_nonneg x hx n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono hx hxy n) (Q'.le_trans' _ _ _ hx hxy))

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {m n : Nat}
    (hmn : m ≤ n) : x^m ≤ x^n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
    exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
        (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (m+d))))

theorem starRatio_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    starRatio w ≤ (1 : Q') := by
  apply HKConv.divPos_le_of_le (CReal.num_pos_of_pos (upperFactor_positive hw0))
  exact Q'.le_trans' _ _ _
    (pow_mono (Q'.le_of_lt (localFloor_positive hw0 hw1))
      (Q'.le_trans' _ _ _ Q'.min_le_right (one_le_localCap hw0)) 6)
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))

/-- The two constants count at most six inserted factors, not all slab faces. -/
theorem atMostSix_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) {p : RatPoly} (P : Certificate (blocks extent) p)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hlen : ids.length ≤ 6) :
    lowerFactor w * quaternionHaar (blocks extent) p ≤
      quaternionHaar (blocks extent) (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids)) ∧
    quaternionHaar (blocks extent) (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids)) ≤
      upperFactor w * quaternionHaar (blocks extent) p := by
  have hlo : lowerFactor w ≤ (headFloor w)^ids.length :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_right hlen)
      (pow_mono (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_left _)
  have hhi : (prefixCap w)^ids.length ≤ upperFactor w :=
    Q'.le_trans' _ _ _ (pow_mono (prefixCap_nonnegative hw0)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))) _)
      (pow_exponent_mono (one_le_localCap hw0) hlen)
  exact ⟨Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hlo P.haar_nonnegative)
    (headProduct_weighted_floor hw0 hw1 K extent hK P ids hi),
    Q'.le_trans' _ _ _ (headProduct_weighted_upper hw0 hw1 K extent P ids hi)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hhi P.haar_nonnegative)⟩

/-- Compare the original full action with only the selected link's star deleted. -/
theorem original_star_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    {p : RatPoly} (P : Certificate (blocks extent) p) :
    let full := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
    let rest := complementHeat w K extent link
    lowerFactor w * quaternionHaar (blocks extent) (polyMul p rest) ≤
      quaternionHaar (blocks extent) (polyMul p full) ∧
    quaternionHaar (blocks extent) (polyMul p full) ≤
      upperFactor w * quaternionHaar (blocks extent) (polyMul p rest) := by
  have h := atMostSix_bounds hw0 hw1 K extent hK
    (P.mul (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ hi => complementIds_physical hi)))
    (incidentIds extent link) (fun _ hi => incidentIds_physical hi) (incidentIds_length_le_six extent link)
  have he : quaternionHaar (blocks extent)
      (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))) ≈
      quaternionHaar (blocks extent) (polyMul (polyMul p (complementHeat w K extent link))
        (incidentHeat w K extent link)) :=
    haar_of_coeff (((RatPolyCoeffEqv.refl p).mul (heatProduct_partition w K extent link)).trans
      (((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm _ _)).trans
        (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv he), Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h.2⟩

/-- Denominator-cleared normalized comparison. Both original partition factors
are retained; no inverse of a whole-volume partition lower bound occurs. -/
theorem original_star_normalized_cross {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    {p : RatPoly} (P : Certificate (blocks extent) p) :
    let full := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
    let rest := complementHeat w K extent link
    starRatio w * quaternionHaar (blocks extent) (polyMul p rest) * quaternionHaar (blocks extent) full ≤
      quaternionHaar (blocks extent) (polyMul p full) * quaternionHaar (blocks extent) rest := by
  let full := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
  let rest := complementHeat w K extent link
  let Y := quaternionHaar (blocks extent) (polyMul p rest)
  let Z := quaternionHaar (blocks extent) rest
  have R := headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
    (fun _ hi => complementIds_physical hi)
  have hY : (0 : Q') ≤ Y := (P.mul R).haar_nonnegative
  have hz := (original_star_bounds hw0 hw1 K extent hK link (.one _)).2
  have hz' : quaternionHaar (blocks extent) full ≤ upperFactor w * Z :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.one_mul full)))
      (Q'.le_trans' _ _ _ hz (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.one_mul rest)))))
  have he : starRatio w * Y * (upperFactor w * Z) ≈ (lowerFactor w * Y) * Z :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 2)) (.var 1)) (.var 3)) (by decide)
      (fun | 0 => starRatio w | 1 => Y | 2 => upperFactor w | _ => Z))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0)))))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hz'
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (starRatio_positive hw0 hw1)) hY))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (original_star_bounds hw0 hw1 K extent hK link P).1 R.haar_nonnegative))

end YMGap.Continuum.BF4ExactSlabLocalStarComparison

#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.localFloor
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.localCap
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.lowerFactor
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.upperFactor
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.starRatio
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.localFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.one_le_localCap
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.lowerFactor_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.upperFactor_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.starRatio_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.starRatio_le_one
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.atMostSix_bounds
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.original_star_bounds
#print axioms YMGap.Continuum.BF4ExactSlabLocalStarComparison.original_star_normalized_cross

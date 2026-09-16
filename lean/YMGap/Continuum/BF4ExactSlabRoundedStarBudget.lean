/-
# Rounded six-face budget in the original local Haar law

The actual heat-window spread pays the existing local star comparison:
localCap <= 4^bits localFloor, hence U <= 4^(6*bits) L. The same factor
pays the reciprocal star ratio, and is applied below to the original
normalized comparison with both partition factors retained. Its exponent
costs at most 1080 heat units under the existing named AF envelope.

The bound is independent of slab extent and of every representation cutoff
above the existing headCutoff. It is a conditioning estimate for the
ordinary weighted Haar/conditional L2 construction. It supplies no
cross-link influence, spatial decay, OS transfer identification, or physical
gap, and does not change the existing cutoff or any frontier premise.
-/

import YMGap.Continuum.BF4RoundedPositiveAFWindows
import YMGap.Continuum.BF4ExactSlabStarRateObstruction

namespace YMGap.Continuum.BF4ExactSlabRoundedStarBudget

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4RoundedPositiveAFWindows (bits)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

set_option autoImplicit false

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

local instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.mul_num, Q'.mul_den_cast]; ac_rfl))

private theorem headFloor_twice_lower (w : Q') :
    headFloor w ≈ (2 : Q') * SU2PointwiseHeatPositiveWindow.lower w := by
  unfold headFloor SU2PointwiseHeatPositiveWindow.lower SU2PointwiseHeatStrictFloor.finiteFloor
  let F := SU2PointwiseHeatStrictFloor.floor w
  let h := HalfPow.half
  change h * F ≈ (2 : Q') * ((F * h) * h)
  calc h * F ≈ F * h := Q'.mul_comm_eqv _ _
    _ ≈ F * (((2 : Q') * h) * h) := Q'.mul_eqv_congr_left _ _ _ (by decide)
    _ ≈ (2 : Q') * ((F * h) * h) := by mul_ring

private theorem localFloor_eq_headFloor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : localFloor w = headFloor w := by
  have h : headFloor w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (headFloor_twice_lower w))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
          (SU2RoundedHeatLower.lower_le_oneSixtyFourth hw0 hw1) (by decide))
        (by decide))
  unfold localFloor Q'.min'
  rw [if_pos h]

private theorem double_eqv (x : Q') : x + x ≈ (2 : Q') * x :=
  Q'.eqv_trans _ _ _
    (Cheb.add_eqv_congr _ _ _ _
      (Q'.eqv_symm (Q'.one_mul_eqv x)) (Q'.eqv_symm (Q'.one_mul_eqv x)))
    (Q'.eqv_symm (Q'.add_mul_eqv 1 1 x))

/-- The existing star's one-face cap/floor ratio has the actual window budget. -/
theorem localCap_le_bitBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    localCap w ≤ (4 : Q') ^ bits w * localFloor w := by
  rw [localFloor_eq_headFloor hw0 hw1]
  let L := SU2PointwiseHeatPositiveWindow.lower w
  let A := (4 : Q') ^ bits w
  have hc : prefixCap w ≤ A * L :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (SU2PointwiseHeatPositiveWindow.lower_pos hw0 hw1)))
      (BF4RoundedPositiveAFWindows.window_spread hw0 hw1)
  have hcap : localCap w ≤ prefixCap w + prefixCap w :=
    Q'.add_le_add_right _ _ _ (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1)
  have he : A * L + A * L ≈ A * headFloor w := by
    calc A * L + A * L ≈ (2 : Q') * (A * L) := double_eqv _
      _ ≈ A * ((2 : Q') * L) := by mul_ring
      _ ≈ A * headFloor w :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (headFloor_twice_lower w))
  exact Q'.le_trans' _ _ _ hcap
    (Q'.le_trans' _ _ _ (Q'.add_le_add hc hc) (Q'.le_of_eqv he))

/-- Six actual incident faces, with no volume-dependent exponent. -/
theorem upperFactor_le_bitBudget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    upperFactor w ≤ (4 : Q') ^ (6 * bits w) * lowerFactor w := by
  have h := HKConv.pow_le_pow_base
    (Q'.le_trans' _ _ _ Q'.zero_le_one (one_le_localCap hw0))
    (localCap_le_bitBudget hw0 hw1) 6
  have he : ((4 : Q') ^ bits w * localFloor w) ^ 6 ≈
      (4 : Q') ^ (6 * bits w) * lowerFactor w := by
    calc ((4 : Q') ^ bits w * localFloor w) ^ 6
        ≈ ((4 : Q') ^ bits w) ^ 6 * (localFloor w) ^ 6 :=
          TotalMajorantClose.mul_pow _ _ 6
      _ ≈ (4 : Q') ^ (6 * bits w) * lowerFactor w := by
        apply Q'.mul_eqv_congr_right
        have hp := TotalMajorantClose.pow_mul (4 : Q') (bits w) 6
        rw [Nat.mul_comm (bits w) 6] at hp
        exact hp
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)

/-- Denominator-free payment of the genuine original normalizer's ratio. -/
theorem starRatio_paid {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ (4 : Q') ^ (6 * bits w) * starRatio w := by
  let A := (4 : Q') ^ (6 * bits w)
  have hpin : starRatio w * upperFactor w ≈ lowerFactor w :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0))
  have he : upperFactor w * (A * starRatio w) ≈ A * lowerFactor w := by
    calc upperFactor w * (A * starRatio w) ≈ A * (starRatio w * upperFactor w) :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_assoc_eqv _ _ _)
      _ ≈ A * lowerFactor w := Q'.mul_eqv_congr_left _ _ _ hpin
  apply HKConvGen.mul_le_mul_left_cancel (upperFactor_positive hw0)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ (upperFactor_le_bitBudget hw0 hw1) (Q'.ge_of_eqv he))

/-- Direct original-law consumer: compare normalized positive insertions
while retaining both exact partition factors and every complementary face. -/
theorem original_star_normalized_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    {p : RatPoly} (P : Certificate (blocks extent) p) :
    let full := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
    let rest := complementHeat w K extent link
    quaternionHaar (blocks extent) (polyMul p rest) * quaternionHaar (blocks extent) full ≤
      (4 : Q') ^ (6 * bits w) *
        (quaternionHaar (blocks extent) (polyMul p full) * quaternionHaar (blocks extent) rest) := by
  let full := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
  let rest := complementHeat w K extent link
  let Y := quaternionHaar (blocks extent) (polyMul p rest)
  let Z := quaternionHaar (blocks extent) full
  let X := quaternionHaar (blocks extent) (polyMul p full) * quaternionHaar (blocks extent) rest
  let A := (4 : Q') ^ (6 * bits w)
  have hY : (0 : Q') ≤ Y :=
    (P.mul (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ hi => complementIds_physical hi))).haar_nonnegative
  have hZ : (0 : Q') ≤ Z :=
    (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent)
      (fun _ hi => hi)).haar_nonnegative
  have hpay : Y * Z ≤ (A * starRatio w) * (Y * Z) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (starRatio_paid hw0 hw1) (Q'.mul_nonneg _ _ hY hZ))
  have hcross : starRatio w * Y * Z ≤ X :=
    original_star_normalized_cross hw0 hw1 K extent hK link P
  have he : (A * starRatio w) * (Y * Z) ≈ A * (starRatio w * Y * Z) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  exact Q'.le_trans' _ _ _ hpay
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ A hcross (Q'.pow_nonneg _ (by decide) _)))

/-- AF-scaled exponent budget, not an AF-uniform mixing margin. -/
theorem bit_heat_cost (E : AFEnvelope) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ E.g₁) (hw : (0 : Q') < E.w g) :
    Q'.ofNat (6 * bits (E.w g)) * (BF4AFHeatSpacing.quarter * E.t g) ≤ (1080 : Q') := by
  have he : Q'.ofNat (6 * bits (E.w g)) * (BF4AFHeatSpacing.quarter * E.t g) ≈
      (6 : Q') * (Q'.ofNat (bits (E.w g)) * (BF4AFHeatSpacing.quarter * E.t g)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (SU3CharFactor.ofNat_mul_eqv 6 (bits (E.w g))))
      (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (6 : Q')
        (BF4RoundedPositiveAFWindows.bit_heat_cost E g hg hgle hw) (by decide))
      (by decide))

#print axioms localCap_le_bitBudget
#print axioms upperFactor_le_bitBudget
#print axioms starRatio_paid
#print axioms original_star_normalized_budget
#print axioms bit_heat_cost

end YMGap.Continuum.BF4ExactSlabRoundedStarBudget

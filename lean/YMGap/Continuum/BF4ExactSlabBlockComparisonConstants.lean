/-
# Extent-independent collar constants for original block tests

The certificate test may depend on every link. Only the list of selected
links controls how many original face factors are compared; the remaining
detached action is retained exactly. This is a form comparison, not a
conditional block projection or a block-angle estimate.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabLocalStarComparison
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.CRealLog

namespace YMGap.Continuum.BF4ExactSlabBlockComparisonConstants

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- A lower collar coefficient paid only for a supplied link-count budget. -/
def blockLower (w : Q') (size : Nat) : Q' := (localFloor w) ^ (6*size)

/-- An upper collar coefficient paid only for a supplied link-count budget. -/
def blockUpper (w : Q') (size : Nat) : Q' := (localCap w) ^ (6*size)

theorem blockLower_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < blockLower w size :=
  HKPos.pow_pos (localFloor_positive hw0 hw1) _

theorem blockUpper_positive {w : Q'} (hw0 : (0 : Q') < w)
    (size : Nat) : (0 : Q') < blockUpper w size :=
  HKPos.pow_pos (Q'.pos_add_nonneg (by decide : (0 : Q') < 1)
    (prefixCap_nonnegative hw0)) _

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {m n : Nat}
    (hmn : m ≤ n) : x ^ m ≤ x ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      exact Q'.le_trans' _ _ _ ih
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
            (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (m+d))))

/-- Collar comparison for an arbitrary certificate test and any physical
face list of bounded length. This is the generic input for family-projected
block normalizers; it does not require a supported-block observable. -/
theorem atMostBlockFaces_bounds {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (size : Nat) {q : RatPoly}
    (P : Certificate (boundaryCompleteSlabLinks extent).length q)
    (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hlen : ids.length ≤ 6*size) :
    blockLower w size * quaternionHaar (boundaryCompleteSlabLinks extent).length q ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length
        (polyMul q (polynomialProduct (faceHeatPolynomial w K extent) ids)) ∧
    quaternionHaar (boundaryCompleteSlabLinks extent).length
        (polyMul q (polynomialProduct (faceHeatPolynomial w K extent) ids)) ≤
      blockUpper w size * quaternionHaar (boundaryCompleteSlabLinks extent).length q := by
  have hlo : blockLower w size ≤ (headFloor w)^ids.length :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone
        (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_right hlen)
      (CRealLog.pow_le_pow_base _ _
        (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_left _)
  have hcap : prefixCap w ≤ localCap w :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hhi : (prefixCap w)^ids.length ≤ blockUpper w size :=
    Q'.le_trans' _ _ _
      (CRealLog.pow_le_pow_base _ _ (prefixCap_nonnegative hw0) hcap _)
      (pow_exponent_mono (one_le_localCap hw0) hlen)
  exact ⟨Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hlo P.haar_nonnegative)
      (headProduct_weighted_floor hw0 hw1 K extent hK P ids hi),
    Q'.le_trans' _ _ _ (headProduct_weighted_upper hw0 hw1 K extent P ids hi)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hhi P.haar_nonnegative)⟩

/-- The original full-face form is sandwiched by the detached-action form,
uniformly in extent and late heat cutoff at fixed nome and support budget.
There is no locality restriction on the certificate polynomial `q`. -/
theorem collar_weighted_bounds {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (links : List Z4Link) (size : Nat) (hsize : links.length ≤ size)
    {q : RatPoly}
    (P : Certificate (boundaryCompleteSlabLinks extent).length q) :
    blockLower w size *
        quaternionHaar (boundaryCompleteSlabLinks extent).length
          (polyMul q (background w K extent links)) ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length
        (polyMul q (fullWeight w K extent)) ∧
    quaternionHaar (boundaryCompleteSlabLinks extent).length
        (polyMul q (fullWeight w K extent)) ≤
      blockUpper w size *
        quaternionHaar (boundaryCompleteSlabLinks extent).length
          (polyMul q (background w K extent links)) := by
  let H := quaternionHaar (boundaryCompleteSlabLinks extent).length
    (polyMul q (background w K extent links))
  have hH : (0 : Q') ≤ H :=
    (P.mul (background_certificate hw0 hw1 K extent hK links)).haar_nonnegative
  have hlen : collarCount extent links ≤ 6*size :=
    Nat.le_trans (collarCount_le extent links) (Nat.mul_le_mul_left 6 hsize)
  have hlo : blockLower w size ≤ (headFloor w)^collarCount extent links := by
    apply Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone
        (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_right hlen)
    exact CRealLog.pow_le_pow_base _ _
      (Q'.le_of_lt (localFloor_positive hw0 hw1)) Q'.min_le_left _
  have hcap : prefixCap w ≤ localCap w :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hhi : (prefixCap w)^collarCount extent links ≤ blockUpper w size := by
    apply Q'.le_trans' _ _ _
      (CRealLog.pow_le_pow_base _ _ (prefixCap_nonnegative hw0) hcap _)
    exact pow_exponent_mono (one_le_localCap hw0) hlen
  have hweighted := weighted_bounds hw0 hw1 K extent hK links P
  exact ⟨Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hlo hH) hweighted.1,
    Q'.le_trans' _ _ _ hweighted.2
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hhi hH)⟩

end YMGap.Continuum.BF4ExactSlabBlockComparisonConstants

#print axioms YMGap.Continuum.BF4ExactSlabBlockComparisonConstants.blockLower
#print axioms YMGap.Continuum.BF4ExactSlabBlockComparisonConstants.blockUpper
#print axioms YMGap.Continuum.BF4ExactSlabBlockComparisonConstants.blockLower_positive
#print axioms YMGap.Continuum.BF4ExactSlabBlockComparisonConstants.blockUpper_positive
#print axioms YMGap.Continuum.BF4ExactSlabBlockComparisonConstants.atMostBlockFaces_bounds
#print axioms YMGap.Continuum.BF4ExactSlabBlockComparisonConstants.collar_weighted_bounds

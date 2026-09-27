/-
# Two-sided ORIGINAL variance comparison paid only on the local collar

The detached original action is retained in both the squared observable and
the partition. Comparing these two quantities before normalization cancels
the exterior mass exactly. Testing at the two explicit means then compares
the original interacting variance with product-Haar variance.

This applies to every literally link-local supported polynomial. The cost
depends on nome and its touching-face count, not the late heat cutoff. It is
not an all-state completed Dirichlet bound or a physical OS-time mass gap.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabSelectedStarVariance
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.BF4ExactSlabLocalSupportVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (selectedMass_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem chain {a b c : Q'} (h : a ≈ b) (j : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h j

private theorem normalize_product (a Z b : Q') (hZ : (0 : Q') < Z) :
    ((a*Z)*b)*Q'.recipPos Z hZ ≈ a*b :=
  chain (poly_identity_of_normal_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => Z | 2 => b | _ => Q'.recipPos Z hZ))
    (chain (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv _))

/-- Algebraic normalization never replaces the original partition by a
full-volume numerical floor. The common background cancels in the ratio. -/
private theorem normalized_sandwich {m M B Z E s : Q'}
    (hm : (0 : Q') ≤ m) (hM : (0 : Q') ≤ M) (hs : (0 : Q') ≤ s)
    (hZ : (0 : Q') < Z) (hlZ : m*B ≤ Z) (huZ : Z ≤ M*B)
    (hlE : m*(s*B) ≤ E) (huE : E ≤ M*(s*B)) :
    m*s ≤ M*(E*Q'.recipPos Z hZ) ∧
      m*(E*Q'.recipPos Z hZ) ≤ M*s := by
  have hl : (m*Z)*s ≤ M*E := by
    have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (m*s) huZ
      (Q'.mul_nonneg _ _ hm hs)
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ M hlE hM
    have he : (m*s)*(M*B) ≈ M*(m*(s*B)) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 2) (.mul (.var 0) (.mul (.var 1) (.var 3))))
        (by decide) (fun | 0 => m | 1 => s | 2 => M | _ => B)
    have hi : (m*Z)*s ≈ (m*s)*Z :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => m | 1 => Z | _ => s)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hi)
      (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h2))
  have hu : m*E ≤ (M*Z)*s := by
    have h1 := Q'.mul_le_mul_of_nonneg_left _ _ m huE hm
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (M*s) hlZ
      (Q'.mul_nonneg _ _ hM hs)
    have he : m*(M*(s*B)) ≈ (M*s)*(m*B) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
        (by decide) (fun | 0 => m | 1 => M | 2 => s | _ => B)
    have hf : (M*s)*Z ≈ (M*Z)*s :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => M | 1 => s | _ => Z)
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hf)))
  have hr := Q'.le_of_lt (Q'.recipPos_pos Z hZ)
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (normalize_product m Z s hZ))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hl hr)
        (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hu hr)
        (Q'.le_of_eqv (normalize_product M Z s hZ)))

/-- The unweighted Haar variance of the SAME polynomial, not a chosen
replacement for its interacting law. -/
def bareVariance (blocks : Nat) (p : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul p p) +
    -(quaternionHaar blocks p * quaternionHaar blocks p)

theorem bareVariance_nonnegative {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : (0 : Q') ≤ bareVariance blocks p :=
  Q'.le_trans' _ _ _
    (Certificate.square _ (shifted_supported hp (quaternionHaar blocks p))).haar_nonnegative
    (Q'.le_of_eqv (bare_mean_pin hp))

private theorem shifted_local {extent : Nat} {S : List Z4Link} {p : RatPoly}
    (hp : LinkLocal extent S p) (c : Q') : LinkLocal extent S (shifted p c) :=
  (hp.smul 1).add ((BlockLocal.one _ _).smul (-c))

/-- A support-size budget, not the number of faces in the full lattice. -/
def supportFloor (w : Q') (size : Nat) : Q' := (headFloor w)^(6*size)

def supportCap (w : Q') (size : Nat) : Q' := (prefixCap w)^(6*size)

theorem supportFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) : (0 : Q') < supportFloor w size :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

theorem supportCap_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) : (0 : Q') < supportCap w size :=
  HKPos.pow_pos (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1)) _

/-- Positive original/free variance ratio. There is no extent, cutoff,
location, degree or polynomial-coefficient argument. Nome is explicit. -/
def supportRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) : Q' :=
  Q'.recipPos (supportCap w size) (supportCap_positive hw0 hw1 size) * supportFloor w size

theorem supportRatio_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) : (0 : Q') < supportRatio hw0 hw1 size :=
  Q'.mul_pos (Q'.recipPos_pos _ _) (supportFloor_positive hw0 hw1 size)

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {i j : Nat}
    (hij : i ≤ j) : x^i ≤ x^j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
    exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
        (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (i+d))))

private theorem ratio_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) {X Y : Q'} (h : supportFloor w size * X ≤ supportCap w size * Y) :
    supportRatio hw0 hw1 size * X ≤ Y := by
  let a := supportFloor w size
  let b := supportCap w size
  let r := Q'.recipPos b (supportCap_positive hw0 hw1 size)
  have he : b*((r*a)*X) ≈ a*X :=
    chain (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => b | 1 => r | 2 => a | _ => X))
      (chain (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_recipPos_eqv b (supportCap_positive hw0 hw1 size)))
        (Q'.one_mul_eqv _))
  exact Q'.le_of_mul_le_mul_left (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h)
    (supportCap_positive hw0 hw1 size)

/-- The same explicit support budget bounds both exact collar constants. -/
theorem support_collar_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (S : List Z4Link) (size : Nat) (hsize : S.length ≤ size) :
    supportFloor w size ≤ (headFloor w)^(collarCount extent S) ∧
      (prefixCap w)^(collarCount extent S) ≤ supportCap w size := by
  have hc : collarCount extent S ≤ 6*size :=
    Nat.le_trans (collarCount_le extent S) (Nat.mul_le_mul_left 6 hsize)
  exact ⟨HKConvGen.pow_base_antitone (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (Q'.le_trans' _ _ _
        (BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond hw0 hw1)
        (by decide : Q'.mkPos 1 32 (by decide) ≤ 1)) hc,
    pow_exponent_mono (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1) hc⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (S : List Z4Link)

local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "W" => polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
local notation "hZ" => selectedMass_positive hw0 hw1 K extent hK
  (slabPhysicalFaceEdges extent) (fun _ hi => hi)
local notation "m" => (headFloor w)^(collarCount extent S)
local notation "M" => (prefixCap w)^(collarCount extent S)

/-- Normalized comparison for every literal local square. The exterior
partition is shared and eliminated before any norm bound is taken. -/
theorem normalized_square_comparison (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hl : LinkLocal extent S p) :
    m * quaternionHaar blocks (polyMul p p) ≤
        M * normalizedMoment blocks W (polyMul p p) hZ ∧
      m * normalizedMoment blocks W (polyMul p p) hZ ≤
        M * quaternionHaar blocks (polyMul p p) := by
  have he := haar_of_coeff («blocks» := blocks) (RatPolyCoeffEqv.mul_comm (polyMul p p) W)
  have hnorm := local_squared_norm_bounds hw0 hw1 K extent hK S hl hp
  have hpart := partition_bounds hw0 hw1 K extent hK S
  exact normalized_sandwich
    (Q'.pow_nonneg _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) _)
    (Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _)
    (Certificate.square p hp).haar_nonnegative hZ
    hpart.1 hpart.2
    (Q'.le_trans' _ _ _ hnorm.1 (Q'.le_of_eqv he))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hnorm.2)

/-- Compare at each law's explicit minimizing mean. This proves bounds
on the actual ORIGINAL interacting variance for arbitrary local p. -/
theorem normalized_variance_comparison (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hl : LinkLocal extent S p) :
    m * bareVariance blocks p ≤ M * normalizedVariance blocks W p hZ ∧
      m * normalizedVariance blocks W p hZ ≤ M * bareVariance blocks p := by
  let PW := headProduct_certificate hw0 hw1 K extent hK
    (slabPhysicalFaceEdges extent) (fun _ hi => hi)
  have hm := Q'.pow_nonneg _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) (collarCount extent S)
  constructor
  · let a := normalizedMoment blocks W p hZ
    have h := (normalized_square_comparison hw0 hw1 K extent hK S
      (shifted p a) (shifted_supported hp a) (shifted_local hl a)).1
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ m (bare_variance_le_shifted hp a) hm)
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (own_mean_pin PW hp hZ))))
  · let a := quaternionHaar blocks p
    have h := (normalized_square_comparison hw0 hw1 K extent hK S
      (shifted p a) (shifted_supported hp a) (shifted_local hl a)).2
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ m (normalized_variance_le_shifted PW hp hZ a) hm)
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (bare_mean_pin hp))))

/-- The original normalized variance and bare Haar variance are comparable
uniformly over every extent, placement and K >= headCutoff(w), for every
polynomial with at most `size` literal support links. The coefficient still
depends on nome and support size; no growing-support or scaling claim. -/
theorem support_variance_comparison (size : Nat) (hsize : S.length ≤ size)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) (hl : LinkLocal extent S p) :
    supportRatio hw0 hw1 size * bareVariance blocks p ≤ normalizedVariance blocks W p hZ ∧
      supportRatio hw0 hw1 size * normalizedVariance blocks W p hZ ≤ bareVariance blocks p := by
  have hbds := support_collar_bounds hw0 hw1 extent S size hsize
  have hv := normalizedVariance_nonnegative
    (headProduct_certificate hw0 hw1 K extent hK (slabPhysicalFaceEdges extent) (fun _ hi => hi)) hZ hp
  have hb := bareVariance_nonnegative hp
  have h := normalized_variance_comparison hw0 hw1 K extent hK S p hp hl
  constructor
  · exact ratio_le hw0 hw1 size (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbds.1 hb)
      (Q'.le_trans' _ _ _ h.1 (Q'.mul_le_mul_of_nonneg_right _ _ _ hbds.2 hv)))
  · exact ratio_le hw0 hw1 size (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbds.1 hv)
      (Q'.le_trans' _ _ _ h.2 (Q'.mul_le_mul_of_nonneg_right _ _ _ hbds.2 hb)))

#print axioms bareVariance_nonnegative
#print axioms normalized_square_comparison
#print axioms normalized_variance_comparison
#print axioms supportFloor_positive
#print axioms supportCap_positive
#print axioms supportRatio_positive
#print axioms support_collar_bounds
#print axioms support_variance_comparison

end YMGap.Continuum.BF4ExactSlabLocalSupportVariance

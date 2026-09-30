/-
# Volume cost defeats the existing finite-volume Chebyshev factor

Let F be the number of ORIGINAL physical faces. The constructed coercivity
is at most (1/32)^F. For every degree n <= F, the ACTUAL covariance factor
therefore lies in [1-(1/8)^F,1]. The literal geometry gives extent <= F,
so a tolerance supplies an extent modulus uniform in nome and in this
degree window. In particular it covers every n <= extent.

This concerns the multiplier in the existing upper covariance estimate,
NOT a lower bound on actual covariance. We do not assert that the stated
degree window contains every degree allowed by geometric disjointness.
Neither a stronger interacting estimate nor Yang--Mills decay is refuted.
The consumer excluded is promotion of this computed factor to useful
spatial decay along growing extents with degrees in the stated window.
-/

import YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevCovariance
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.BF4ExactSlabPhysicalFaceCount
import YMGap.Continuum.ChebyshevReciprocalNearOne
import YMGap.Continuum.CasimirMoment

namespace YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabHaarVarianceComparison
open YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
open YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevCovariance
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabPhysicalFaceCount
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private def faceBase : Q' := Q'.mkPos 1 32 (by decide)
private def eighth : Q' := Q'.mkPos 1 8 (by decide)

private theorem pow_exponent_mono {x : Q'} (hx : (1 : Q') ≤ x) {m n : Nat}
    (hmn : m ≤ n) : x^m ≤ x^n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      exact Q'.le_trans' _ _ _ ih
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hx
            (Q'.pow_nonneg x (Q'.le_trans' _ _ _ Q'.zero_le_one hx) (m+d))))

private theorem faceBase_four_pow (n : Nat) :
    faceBase^n * (4 : Q')^n ≈ eighth^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      change (faceBase * faceBase^n) * ((4 : Q') * (4 : Q')^n) ≈ eighth * eighth^n
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
          (by decide) (fun | 0 => faceBase | 1 => faceBase^n | 2 => 4 | _ => (4 : Q')^n))
        (Cheb.mul_eqv_congr _ _ _ _ (by decide : faceBase * (4 : Q') ≈ eighth) ih)

/-- The already constructed coefficient pays a floor/cap on EVERY face. -/
theorem coercivity_le_face_power {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat) :
    coercivity hw0 hw1 extent ≤
      (Q'.mkPos 1 32 (by decide))^(slabPhysicalFaceEdges extent).length := by
  have hcap : (1 : Q') ≤ volumeCap w extent :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (CasimirMoment.one_pow_eqv _))
      (HKConv.pow_le_pow_base Q'.zero_le_one
        (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1) _)
  have hr : Q'.recipPos (volumeCap w extent) (volumeCap_positive hw0 hw1 extent) ≤ 1 := by
    apply Q'.le_of_mul_le_mul_left (c := volumeCap w extent) ?_
      (volumeCap_positive hw0 hw1 extent)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ _))
      (Q'.le_trans' _ _ _ hcap (Q'.ge_of_eqv (Q'.mul_one_eqv _)))
  have hf : volumeFloor w extent ≤ faceBase^(slabPhysicalFaceEdges extent).length :=
    HKConv.pow_le_pow_base (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (headFloor_le_oneThirtySecond hw0 hw1) _
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hr
      (Q'.le_of_lt (volumeFloor_positive hw0 hw1 extent)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hf)

/-- The denominator stays near one throughout the explicit degree window. -/
theorem denominator_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent n : Nat)
    (hn : n ≤ (slabPhysicalFaceEdges extent).length) :
    (1 : Q') ≤ Cheb.T n (reverseCoefficient hw0 hw1 extent + -(1 : Q')) ∧
    Cheb.T n (reverseCoefficient hw0 hw1 extent + -(1 : Q')) ≤
      1 + (Q'.mkPos 1 8 (by decide))^(slabPhysicalFaceEdges extent).length := by
  let F := (slabPhysicalFaceEdges extent).length
  let e := geometricCalibration * coercivity hw0 hw1 extent
  have he0 : (0 : Q') ≤ e := Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (coercivity_positive hw0 hw1 extent))
  have hdelta := coercivity_le_face_power hw0 hw1 extent
  have hdelta1 : coercivity hw0 hw1 extent ≤ 1 := Q'.le_trans' _ _ _ hdelta
    (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ faceBase)
      (by decide : faceBase ≤ 1) (Nat.zero_le F))
  have hehalf : e ≤ HalfPow.half := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ geometricCalibration hdelta1 (by decide))
    (by decide : geometricCalibration * (1 : Q') ≤ HalfPow.half)
  have he : e ≤ faceBase^F := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : geometricCalibration ≤ 1)
      (Q'.le_of_lt (coercivity_positive hw0 hw1 extent)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hdelta)
  have hbudget : e*(4 : Q')^n ≤ eighth^F := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ he (Q'.pow_nonneg 4 (by decide) n))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_exponent_mono (by decide) hn)
        (Q'.pow_nonneg faceBase (by decide) F))
      (Q'.le_of_eqv (faceBase_four_pow F)))
  have harg : reverseCoefficient hw0 hw1 extent + -(1 : Q') ≈ 1+e :=
    poly_identity_of_normal_eq
      (.add (.add (.const 2) (.var 0)) (.neg (.const 1)))
      (.add (.const 1) (.var 0)) (by decide) (fun _ => e)
  have ht := ChebyshevNearOneUpper.T_congr _ _ harg n
  have hx := Q'.add_le_self_of_nonneg 1 e he0
  exact ⟨Q'.le_trans' _ _ _ (ChebyshevAboveOne.T_lower_and_step _ hx n).1
      (Q'.ge_of_eqv ht),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv ht)
      (Q'.le_trans' _ _ _ (ChebyshevNearOneUpper.T_near_one_upper e he0 hehalf n)
        (Q'.add_le_add_left 1 _ _ hbudget))⟩

/-- Two-sided bound on the multiplier used by the ORIGINAL covariance theorem. -/
theorem factor_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent n : Nat)
    (hn : n ≤ (slabPhysicalFaceEdges extent).length) :
    1 + -((Q'.mkPos 1 8 (by decide))^(slabPhysicalFaceEdges extent).length) ≤
        covarianceFactor hw0 hw1 extent n ∧ covarianceFactor hw0 hw1 extent n ≤ 1 := by
  have h := denominator_bounds hw0 hw1 extent n hn
  exact ChebyshevReciprocalNearOne.reciprocal_band _ _
    (denominator_positive hw0 hw1 extent n) h.1 h.2
    (Q'.pow_nonneg eighth (by decide) _)
    (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ eighth)
      (by decide : eighth ≤ 1) (Nat.zero_le _))

/-- Literal slab geometry converts the face-count estimate to an extent estimate. -/
theorem factor_extent_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent n : Nat)
    (hn : n ≤ (slabPhysicalFaceEdges extent).length) :
    1 + -((Q'.mkPos 1 8 (by decide))^extent) ≤ covarianceFactor hw0 hw1 extent n ∧
      covarianceFactor hw0 hw1 extent n ≤ 1 := by
  have h := factor_bounds hw0 hw1 extent n hn
  have hp := HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ eighth)
    (by decide : eighth ≤ 1) (extent_le_physicalFaces_length extent)
  exact ⟨Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hp)) h.1, h.2⟩

/-- In particular every degree at most the extent lies in the proved window. -/
theorem factor_bounds_of_degree_le_extent {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent n : Nat) (hn : n ≤ extent) :
    1 + -((Q'.mkPos 1 8 (by decide))^extent) ≤ covarianceFactor hw0 hw1 extent n ∧
      covarianceFactor hw0 hw1 extent n ≤ 1 :=
  factor_extent_bounds hw0 hw1 extent n
    (Nat.le_trans hn (extent_le_physicalFaces_length extent))

/-- Explicit extent cutoff for approach to ONE, independent of nome and degree. -/
def factorModulus (epsilon : Q') : Nat := epsilon.den

/-- All nomes and all degrees in the stated window share this degeneration modulus. -/
theorem factor_approaches_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (extent n : Nat)
    (hextent : factorModulus epsilon ≤ extent)
    (hn : n ≤ (slabPhysicalFaceEdges extent).length) :
    1 + -epsilon ≤ covarianceFactor hw0 hw1 extent n ∧
      covarianceFactor hw0 hw1 extent n ≤ 1 := by
  have h := factor_extent_bounds hw0 hw1 extent n hn
  have hp : eighth^extent ≤ epsilon := Q'.le_trans' _ _ _
    (HKConv.pow_le_pow_base (by decide : (0 : Q') ≤ eighth)
      (by decide : eighth ≤ HalfPow.half) extent)
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone HalfPow.half_nonneg (by decide : HalfPow.half ≤ 1) hextent)
      (HalfPow.pow_half_le epsilon he))
  exact ⟨Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hp)) h.1, h.2⟩

end YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.coercivity_le_face_power
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.denominator_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.factor_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.factor_extent_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.factor_bounds_of_degree_le_extent
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.factorModulus
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevObstruction.factor_approaches_one

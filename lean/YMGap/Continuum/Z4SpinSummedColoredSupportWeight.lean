/-
# Colored-support envelope for the arbitrary-cutoff spin-summed gas

The two-replica carrier has three nonempty color states per union face.  This
module combines that exact finite count with the spin-summed one-face envelope
`1/7500`.  The resulting animal/color ratio is the already derived exact
quantity `anchorDecoratedEffectiveRatio = 1/4`.
-/

import YMGap.Continuum.Z4CanonicalColoredSupportWeight
import YMGap.Continuum.Z4SpinSummedFaceActivityBound

namespace YMGap.Continuum.Z4SpinSummedColoredSupportWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalColoredSupportWeight
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def spinSummedColoredPinnedSizeWeightSum
    (n rootFace size : Nat) : Q' :=
  listQSum (fun _ : ColoredSupportPair =>
      anchorDecoratedFaceEnvelope ^ size)
    (canonicalColoredPinnedSizePairs n rootFace size)

theorem spinSummedColoredPinnedSizeWeightSum_nonnegative
    (n rootFace size : Nat) :
    (0 : Q') ≤
      spinSummedColoredPinnedSizeWeightSum n rootFace size := by
  unfold spinSummedColoredPinnedSizeWeightSum
  exact listQSum_nonnegative _
    (fun _ => Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative size) _

theorem spinSummedColoredPinnedSizeWeightSum_le_lengthEnvelope
    (n rootFace size : Nat) :
    spinSummedColoredPinnedSizeWeightSum n rootFace size ≤
      Q'.ofNat (canonicalColoredPinnedSizePairs n rootFace size).length *
        anchorDecoratedFaceEnvelope ^ size := by
  unfold spinSummedColoredPinnedSizeWeightSum
  apply listQSum_le_length_mul
    (fun _ : ColoredSupportPair => anchorDecoratedFaceEnvelope ^ size)
    (Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative size)
  intro _ _
  exact Q'.le_refl' _

theorem spinSummedColoredPinnedSizeWeightSum_le_animalEnvelope
    (n rootFace size : Nat) :
    spinSummedColoredPinnedSizeWeightSum n rootFace size ≤
      ((z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorDecoratedFaceEnvelope ^ size) * eSurrogate ^ size := by
  have hq0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^ size :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative size
  have he0 : (0 : Q') ≤ eSurrogate ^ size :=
    Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
  have hcolored :
      Q'.ofNat (canonicalColoredPinnedSizePairs n rootFace size).length *
          anchorDecoratedFaceEnvelope ^ size ≤
        (Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
            eSurrogate ^ size) * anchorDecoratedFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (coloredPairCount_le_pinned_mul_ePow n rootFace size) hq0
  have hreorder :
      ((Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          eSurrogate ^ size) * anchorDecoratedFaceEnvelope ^ size) ≈
        ((Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          anchorDecoratedFaceEnvelope ^ size) * eSurrogate ^ size) :=
    mul_three_swap_eqv _ _ _
  have hpinned :
      Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          anchorDecoratedFaceEnvelope ^ size ≤
        (z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorDecoratedFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalPinnedSize_count_le_animalCount n rootFace size) hq0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hpinned he0
  exact Q'.le_trans' _ _ _
    (spinSummedColoredPinnedSizeWeightSum_le_lengthEnvelope
      n rootFace size)
    (Q'.le_trans' _ _ _ hcolored
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hscaled))

theorem spinSummedColoredPinnedSizeWeightSum_le_geom
    (n rootFace size : Nat) :
    spinSummedColoredPinnedSizeWeightSum n rootFace size ≤
      anchorDecoratedEffectiveRatio ^ size := by
  have hq0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^ size :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative size
  have he0 : (0 : Q') ≤ eSurrogate ^ size :=
    Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
  have hcount :
      (z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorDecoratedFaceEnvelope ^ size ≤
        animalK z4Chain ^ size * anchorDecoratedFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      ((z4ClusterCountBound
        (boxPlaquetteAt n rootFace)).count_le size) hq0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hcount he0
  have hpow :
      anchorDecoratedEffectiveRatio ^ size ≈
        animalK z4Chain ^ size * anchorDecoratedFaceEnvelope ^ size *
          eSurrogate ^ size := by
    unfold anchorDecoratedEffectiveRatio
    exact pow_mul3_eqv (animalK z4Chain)
      anchorDecoratedFaceEnvelope eSurrogate size
  exact Q'.le_trans' _ _ _
    (spinSummedColoredPinnedSizeWeightSum_le_animalEnvelope
      n rootFace size)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hpow))

end YMGap.Continuum.Z4SpinSummedColoredSupportWeight

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedColoredSupportWeight.spinSummedColoredPinnedSizeWeightSum_le_animalEnvelope
#print axioms YMGap.Continuum.Z4SpinSummedColoredSupportWeight.spinSummedColoredPinnedSizeWeightSum_le_geom

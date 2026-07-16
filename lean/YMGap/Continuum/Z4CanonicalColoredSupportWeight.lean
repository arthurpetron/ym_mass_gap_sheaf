/-
# Weighted three-color canonical-support bound

The exact three-state encoding of a pair of colored supports is combined
with the per-face activity envelope.  At fixed union size, the complete
colored-support sum is bounded by the same geometric factor
`anchorEffectiveRatio ^ size` that already controls pinned canonical
polymers.  No numerical estimate enters: the factor three is the exact
cardinality of the nonempty left/right color states.
-/

import YMGap.Continuum.Z4CanonicalColoredSupportCount

namespace YMGap.Continuum.Z4CanonicalColoredSupportWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact rational form of the three-state multiplicity -/

theorem ofNat_three_pow_eqv_eSurrogate_pow :
    ∀ size : Nat, Q'.ofNat (3 ^ size) ≈ eSurrogate ^ size
  | 0 => Q'.eqv_refl 1
  | size + 1 => by
      rw [Nat.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _ _ _
        (ofNat_mul_eqv (3 ^ size) 3) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          (Q'.ofNat (3 ^ size)) (eSurrogate ^ size)
          (Q'.ofNat 3) (ofNat_three_pow_eqv_eSurrogate_pow size)) ?_
      unfold eSurrogate
      exact Q'.mul_comm_eqv (Q'.ofNat 3 ^ size) (Q'.ofNat 3)

theorem coloredPairCount_le_pinned_mul_ePow
    (n rootFace size : Nat) :
    Q'.ofNat (canonicalColoredPinnedSizePairs n rootFace size).length ≤
      Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
        eSurrogate ^ size := by
  have hnat := canonicalColoredPinnedSizePairs_length_le n rootFace size
  have hcast :
      Q'.ofNat (canonicalColoredPinnedSizePairs n rootFace size).length ≤
        Q'.ofNat
          ((canonicalPinnedSizePolymers n rootFace size).length * 3 ^ size) :=
    Q'.ofNat_le_ofNat hnat
  have heq :
      Q'.ofNat
          ((canonicalPinnedSizePolymers n rootFace size).length * 3 ^ size) ≈
        Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          eSurrogate ^ size := by
    refine Q'.eqv_trans _ _ _
      (ofNat_mul_eqv
        (canonicalPinnedSizePolymers n rootFace size).length
        (3 ^ size)) ?_
    exact Q'.mul_eqv_congr_left
      (Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length)
      (Q'.ofNat (3 ^ size)) (eSurrogate ^ size)
      (ofNat_three_pow_eqv_eSurrogate_pow size)
  exact Q'.le_trans' _ _ _ hcast (Q'.le_of_eqv heq)

/-! ## Weighted fixed-size sum -/

def canonicalColoredPinnedSizeWeightSum
    (n rootFace size : Nat) : Q' :=
  listQSum (fun _ : ColoredSupportPair =>
      anchorPerFaceEnvelope ^ size)
    (canonicalColoredPinnedSizePairs n rootFace size)

theorem canonicalColoredPinnedSizeWeightSum_nonnegative
    (n rootFace size : Nat) :
    (0 : Q') ≤ canonicalColoredPinnedSizeWeightSum n rootFace size := by
  unfold canonicalColoredPinnedSizeWeightSum
  exact listQSum_nonnegative _
    (fun _ => Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size)
    (canonicalColoredPinnedSizePairs n rootFace size)

theorem canonicalColoredPinnedSizeWeightSum_le_lengthEnvelope
    (n rootFace size : Nat) :
    canonicalColoredPinnedSizeWeightSum n rootFace size ≤
      Q'.ofNat (canonicalColoredPinnedSizePairs n rootFace size).length *
        anchorPerFaceEnvelope ^ size := by
  unfold canonicalColoredPinnedSizeWeightSum
  apply listQSum_le_length_mul
    (fun _ : ColoredSupportPair => anchorPerFaceEnvelope ^ size)
    (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size)
  intro _ _
  exact Q'.le_refl' _

theorem mul_three_swap_eqv (a b c : Q') :
    ((a * b) * c) ≈ ((a * c) * b) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b c) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a (b * c) (c * b)
      (Q'.mul_comm_eqv b c)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c b)

theorem canonicalColoredPinnedSizeWeightSum_le_animalEnvelope
    (n rootFace size : Nat) :
    canonicalColoredPinnedSizeWeightSum n rootFace size ≤
      ((z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorPerFaceEnvelope ^ size) * eSurrogate ^ size := by
  have hq0 : (0 : Q') ≤ anchorPerFaceEnvelope ^ size :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size
  have he0 : (0 : Q') ≤ eSurrogate ^ size :=
    Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
  have hcolored :
      Q'.ofNat (canonicalColoredPinnedSizePairs n rootFace size).length *
          anchorPerFaceEnvelope ^ size ≤
        (Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
            eSurrogate ^ size) * anchorPerFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (coloredPairCount_le_pinned_mul_ePow n rootFace size) hq0
  have hreorder :
      ((Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          eSurrogate ^ size) * anchorPerFaceEnvelope ^ size) ≈
        ((Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          anchorPerFaceEnvelope ^ size) * eSurrogate ^ size) :=
    mul_three_swap_eqv _ _ _
  have hpinned :
      Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          anchorPerFaceEnvelope ^ size ≤
        (z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorPerFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalPinnedSize_count_le_animalCount n rootFace size) hq0
  have hscaled :
      (Q'.ofNat (canonicalPinnedSizePolymers n rootFace size).length *
          anchorPerFaceEnvelope ^ size) * eSurrogate ^ size ≤
        ((z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorPerFaceEnvelope ^ size) * eSurrogate ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpinned he0
  exact Q'.le_trans' _ _ _
    (canonicalColoredPinnedSizeWeightSum_le_lengthEnvelope n rootFace size)
    (Q'.le_trans' _ _ _ hcolored
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hscaled))

theorem canonicalColoredPinnedSizeWeightSum_le_geom
    (n rootFace size : Nat) :
    canonicalColoredPinnedSizeWeightSum n rootFace size ≤
      anchorEffectiveRatio ^ size := by
  have hq0 : (0 : Q') ≤ anchorPerFaceEnvelope ^ size :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) size
  have he0 : (0 : Q') ≤ eSurrogate ^ size :=
    Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
  have hcount :
      (z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorPerFaceEnvelope ^ size ≤
        animalK z4Chain ^ size * anchorPerFaceEnvelope ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      ((z4ClusterCountBound (boxPlaquetteAt n rootFace)).count_le size) hq0
  have hscaled :
      ((z4ClusterCountBound (boxPlaquetteAt n rootFace)).animalCount size *
          anchorPerFaceEnvelope ^ size) * eSurrogate ^ size ≤
        (animalK z4Chain ^ size * anchorPerFaceEnvelope ^ size) *
          eSurrogate ^ size :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcount he0
  have hpow :
      anchorEffectiveRatio ^ size ≈
        animalK z4Chain ^ size * anchorPerFaceEnvelope ^ size *
          eSurrogate ^ size := by
    unfold anchorEffectiveRatio
    exact pow_mul3_eqv (animalK z4Chain)
      anchorPerFaceEnvelope eSurrogate size
  exact Q'.le_trans' _ _ _
    (canonicalColoredPinnedSizeWeightSum_le_animalEnvelope n rootFace size)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hpow))

end YMGap.Continuum.Z4CanonicalColoredSupportWeight

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalColoredSupportWeight.ofNat_three_pow_eqv_eSurrogate_pow
#print axioms YMGap.Continuum.Z4CanonicalColoredSupportWeight.coloredPairCount_le_pinned_mul_ePow
#print axioms YMGap.Continuum.Z4CanonicalColoredSupportWeight.canonicalColoredPinnedSizeWeightSum_le_geom

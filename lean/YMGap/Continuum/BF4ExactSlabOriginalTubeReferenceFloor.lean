/-
# A positive, volume-independent reference term inside the original numerator

The literal twelve-face tube has at most 336 collar faces, independent of
the volume margin. The ORIGINAL shared-link partition comparison therefore
costs at most (1+delta(w))^672 after squaring. The explicit linear guard
1/2 <= 1-672*delta(w) bounds this factor by two. In particular it holds at
the existing nome 1/1024, at every cutoff and margin.

Thus the actual dressed tube term is at least (w^36/2)*Z_full^2. The full
numerator has this lower bound PLUS the signed otherCoreRemainder, not this
lower bound alone. No bound on that remainder or positive full response is
asserted. The coupling is explicit; no continuum or coupling-uniform gap
is obtained here.
-/

import YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit
import YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.RationalLinearPowerCeiling

namespace YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit
open YMGap.Continuum.BF4ExactSlabOriginalTubeActionSweep
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem tube_collar_length_le (margin : Nat) :
    (collarIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
      (tubeIds margin) (slabPhysicalFaceEdges (responseExtent margin))).length ≤ 336 := by
  have h := full_collarIds_length_le (responseExtent margin)
    (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) (tubeIds margin)
  rw [tubeIds_length] at h
  exact h

/-- Same full partition, with a count depending only on the fixed tube. -/
theorem tube_partition_ceiling {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hs : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w ≤ 1) (K margin : Nat) :
    partitionSquare w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) ≤
      (1+heatRemainderBound w)^672 * partitionSquare w K (responseExtent margin)
        (detachedIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
          (tubeIds margin) (slabPhysicalFaceEdges (responseExtent margin))) :=
  relative_square_bounded_count hw0 hw1 hs hd K (responseExtent margin) 336 _ _ _
    (fun _ hi => collar_mem hi) (fun _ hi => detached_mem hi)
    (region_partition _ _ _ _) (tube_collar_length_le margin)

/-- Uniform in K and margin on the named small-nome/linear-guard domain. -/
theorem detached_half_floor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hs : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w ≤ 1)
    (hlinear : HalfPow.half ≤ 1 + -(Q'.ofNat 672*heatRemainderBound w)) (K margin : Nat) :
    HalfPow.half * partitionSquare w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) ≤
      partitionSquare w K (responseExtent margin)
        (detachedIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
          (tubeIds margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
  have hp := RationalLinearPowerCeiling.power_le_two (heatRemainderBound_nonnegative hw0) 672 hlinear
  have htwo := Q'.le_trans' _ _ _ (tube_partition_ceiling hw0 hw1 hs hd K margin)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hp (SumOfSquares.q_mul_self_nonneg _))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half htwo (by decide)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half*2 ≈ 1))
      (Q'.one_mul_eqv _))))

theorem existingNome_linear_guard :
    HalfPow.half ≤ 1 + -(Q'.ofNat 672*heatRemainderBound nome) := by decide

/-- The original detached/full comparison at every cutoff and volume margin. -/
theorem existingNome_detached_half_floor (K margin : Nat) :
    HalfPow.half * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) ≤
      partitionSquare nome K (responseExtent margin)
        (detachedIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
          (tubeIds margin) (slabPhysicalFaceEdges (responseExtent margin))) :=
  detached_half_floor (Q'.le_of_lt nome_pos) (Q'.le_of_lt nome_lt_one)
    existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) existingNome_linear_guard K margin

def referenceFloor (w : Q') : Q' := HalfPow.half * RingNormaliser.qpow w 36

private theorem power_pos {w : Q'} (hw : (0 : Q') < w) : ∀ n, (0 : Q') < RingNormaliser.qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_pos hw n) hw

theorem referenceFloor_pos {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < referenceFloor w :=
  Q'.mul_pos (by decide) (power_pos hw 36)

theorem existingNome_dressed_tube_floor (K margin : Nat) :
    referenceFloor nome * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) ≤
      RingNormaliser.qpow nome 36 * partitionSquare nome K (responseExtent margin)
        (detachedIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
          (tubeIds margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (RingNormaliser.qpow nome 36)
    (existingNome_detached_half_floor K margin) (Q'.le_of_lt (power_pos nome_pos 36))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun i => if i=0 then HalfPow.half else if i=1 then RingNormaliser.qpow nome 36 else
      partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))))) h

/-- The signed remainder is retained, not assumed positive or discarded. -/
theorem original_numerator_lower_with_remainder (K margin : Nat) (hK : 1 ≤ K) :
    referenceFloor nome * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) +
      otherCoreRemainder nome K margin ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (existingNome_dressed_tube_floor K margin))
    (Q'.ge_of_eqv (original_dressed_tube_split nome K margin hK))

end YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor

#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.tube_collar_length_le
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.tube_partition_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.detached_half_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.existingNome_linear_guard
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.existingNome_detached_half_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.referenceFloor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.referenceFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.existingNome_dressed_tube_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor.original_numerator_lower_with_remainder

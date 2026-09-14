/-
# The complete original leading coefficient is exactly one

At every cutoff K >= 1, the explicit tube/zero pair passes the ORIGINAL
connected-selection, representation, odd-cut, leaf and leading-moment
filters. It has Casimir power 36. Prior uniqueness then evaluates the
complete count to one, without modifying the original enumeration.
The same full numerator is w^36 * (1 + w*B(w)). Its signed higher remainder
is still unbounded here; positivity of the full response does not follow.
-/

import YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments
import YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected

namespace YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments
open YMGap.Continuum.BF4ExactSlabCanonicalTubeConnected
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness
open YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount
open YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower
open YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem small_excess_zero (state : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → state id ≤ 1) → excessSum state ids = 0
  | [], _ => rfl
  | id::ids, hs => by
      have hb := hs id List.mem_cons_self
      have ih := small_excess_zero state ids (fun i hi => hs i (List.mem_cons_of_mem id hi))
      change (c4 (state id) - 3) + excessSum state ids = 0
      by_cases hz : state id = 0
      · rw [hz,ih]
        rfl
      · have ho : state id = 1 := by omega
        rw [ho,ih]
        rfl

theorem binary_casimir (state : Nat → Nat) (ids : List Nat)
    (hs : ∀ id, id ∈ ids → state id ≤ 1) : casimirSum state ids = 3 * positiveCount state ids := by
  rw [casimir_decomposition,small_excess_zero state ids hs,Nat.add_zero]

theorem tube_pair_power (margin : Nat) : pairPower margin (tubePair margin) = 36 := by
  have ht := (tube_positive_perm margin).length_eq
  rw [tubeSides_length,positiveFaces_length] at ht
  have hz := congrArg List.length (zero_positive (responseExtent margin))
  rw [positiveFaces_length] at hz
  change casimirSum (tubeLabelling margin) (slabPhysicalFaceEdges (responseExtent margin)) +
    casimirSum zeroEdgeLabelling (slabPhysicalFaceEdges (responseExtent margin)) = 36
  rw [binary_casimir _ _ (fun id _ => tube_small margin id),
    binary_casimir zeroEdgeLabelling _ (fun _ _ => Nat.zero_le 1),ht,hz]
  rfl

theorem tubePair_retained (K margin time : Nat) (hK : 1 ≤ K) : tubePair margin ∈ retainedPairs K margin time :=
  List.mem_flatMap.mpr ⟨tubeIds margin,tubeIds_connected margin,
    List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨tubePair_enumerated K margin hK,tube_pairKeep margin time⟩,
      tube_pairLeafKeep margin⟩⟩

theorem tubePair_leading (K margin time : Nat) (hK : 1 ≤ K) :
    tubePair margin ∈ (retainedPairs K margin time).filter (leadingKeep margin) :=
  List.mem_filter.mpr ⟨tubePair_retained K margin time hK,
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true (tube_pair_power margin),tube_amplitudeKeep margin⟩⟩

theorem leadingCount_one (K margin time : Nat) (hK : 1 ≤ K) : leadingCount K margin time = 1 := by
  have hp := List.length_pos_of_mem (tubePair_leading K margin time hK)
  have hb := leadingCount_le_one K margin time
  change 0 < leadingCount K margin time at hp
  omega

theorem leadingCoefficient_one (K margin time : Nat) (hK : 1 ≤ K) : leadingCoefficient K margin time ≈ 1 := by
  have he := leadingCoefficient_count K margin time
  rw [leadingCount_one K margin time hK] at he
  exact he

theorem original_unit_leading_remainder (w : Q') (K margin time : Nat) (hK : 1 ≤ K) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
        qpow w 36 * (1 + w * higherResidual w K margin time) :=
  Q'.eqv_trans _ _ _ (original_leading_remainder w K margin time)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' (leadingCoefficient_one K margin time hK) (Q'.eqv_refl _)))

theorem residual_at_zero_one (K margin time : Nat) (hK : 1 ≤ K) : numeratorResidual 0 K margin time ≈ 1 :=
  Q'.eqv_trans _ _ _ (residual_at_zero K margin time) (leadingCoefficient_one K margin time hK)

end YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne

#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.small_excess_zero
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.binary_casimir
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.tube_pair_power
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.tubePair_retained
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.tubePair_leading
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.leadingCount_one
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.leadingCoefficient_one
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.original_unit_leading_remainder
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientOne.residual_at_zero_one

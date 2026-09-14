/-
# Zero-spatial non-tube terms pay a quantitative higher-label cost

Every nonzero original pair in this sector has exactly twelve parity
bits. Outside the tube support it also has a positive higher count.
Thus its original weighted magnitude is at most 8*oddRate^12*higherRate
when both heat activities have the displayed guards. At the unchanged
nome this is (9/2^53)*w^36 PER PAIR. Neither the number of pairs nor their
detached partition factors are bounded here; no response floor follows yet.
-/

import YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost

namespace YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabZeroSpatialChannels
open YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem parityCount_congr (left right : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id % 2 = right id % 2) → parityCount left ids = parityCount right ids
  | [], _ => rfl
  | id::ids, h => by
    rw [parityCount, parityCount, h id List.mem_cons_self,
      parityCount_congr left right ids (fun i hi => h i (List.mem_cons_of_mem id hi))]

theorem parityCount_small (state : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → state id ≤ 1) → parityCount state ids = positiveCount state ids
  | [], _ => rfl
  | id::ids, h => by
    have hb := h id List.mem_cons_self
    have ih := parityCount_small state ids (fun i hi => h i (List.mem_cons_of_mem id hi))
    by_cases hz : state id = 0
    · simpa only [parityCount, positiveCount, List.filter_cons, hz, Nat.zero_mod,
        Nat.zero_add, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte] using ih
    · have ho : state id = 1 := by omega
      simpa only [parityCount, positiveCount, List.filter_cons, ho, Nat.mod_eq_of_lt (by decide : 1 < 2),
        Nat.zero_lt_one, decide_true, ↓reduceIte, List.length_cons, Nat.add_comm] using congrArg (fun n => 1+n) ih

theorem zero_parityCount : ∀ ids : List Nat, parityCount zeroEdgeLabelling ids = 0
  | [] => rfl
  | _::ids => by
    simpa only [parityCount, zeroEdgeLabelling, Nat.zero_mod, Nat.zero_add] using zero_parityCount ids

theorem tube_parityCount (margin : Nat) :
    parityCount (tubeLabelling margin) (slabPhysicalFaceEdges (responseExtent margin)) = 12 := by
  rw [parityCount_small _ _ (fun id _ => tube_small margin id), ← positiveFaces_length]
  exact (tube_positive_perm margin).length_eq.trans (tubeSides_length margin)

theorem nonzero_pairParity_twelve (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hl : spatialOddFaces margin pair.1 = []) (hr : spatialOddFaces margin pair.2 = [])
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) : pairParity margin pair = 12 := by
  have hc := nonzero_pair_checks margin pair.1 pair.2 hl hne
  have hleft := parityCount_congr pair.1 (tubeLabelling margin) (slabPhysicalFaceEdges (responseExtent margin))
    (fun id hi => (mixed_parity_pin margin pair.1 hl hc.1 id hi).trans
      (Nat.mod_eq_of_lt (show tubeLabelling margin id < 2 from by have h := tube_small margin id; omega)).symm)
  have hright := parityCount_congr pair.2 zeroEdgeLabelling (slabPhysicalFaceEdges (responseExtent margin))
    (fun id hi => partition_parity_zero margin pair.2 hr hc.2 id hi)
  unfold pairParity
  rw [hleft, hright, zero_parityCount, Nat.add_zero, tube_parityCount]

theorem nonTube_zeroSpatial_weight_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hrate : higherRate w ≤ (1 : Q')) {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K ids) (ht : ids ≠ tubeIds margin)
    (hl : spatialOddFaces margin pair.1 = []) (hr : spatialOddFaces margin pair.2 = []) :
    Q'.abs (weightedPairTerm w K margin pair) ≤ 8*(qpow (oddRate w) 12 * higherRate w) := by
  by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
  · have he : weightedPairTerm w K margin pair ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr he)
      (by decide : Q'.abs (0 : Q') ≈ 0)))
      (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _
        (qpow_nonneg _ (oddRate_nonnegative hw0) 12) (higherRate_nonnegative hw0)))
  · have hB := nonzero_pairParity_twelve margin pair hl hr hz
    have hH := nonTube_nonzero_higher hK hs hp ht hl hr hz
    have hb := weightedPairTerm_parity_bound hw0 hw1 K margin pair (fun id _ => bounded K ids pair hp id)
    rw [hB] at hb
    have hh : qpow (higherRate w) (pairHigher margin pair) ≤ higherRate w :=
      Q'.le_trans' _ _ _ (HeatKernelRGStep.qpow_antitone (higherRate_nonnegative hw0) hrate 1 _ hH)
        (Q'.le_of_eqv (Q'.one_mul_eqv _))
    exact Q'.le_trans' _ _ _ hb (Q'.mul_le_mul_of_nonneg_left _ _ 8
      (Q'.mul_le_mul_of_nonneg_left _ _ (qpow (oddRate w) 12) hh
        (qpow_nonneg _ (oddRate_nonnegative hw0) 12)) (by decide))

def zeroSpatialRelativeCap : Q' := 9*Q'.invSucc (2^53-1)

theorem existingNome_cap_pin :
    8*(qpow (oddRate nome) 12 * higherRate nome) ≈ zeroSpatialRelativeCap*qpow nome 36 := by decide

/-- A per-pair estimate only; the original finite sum and detached partitions still need control. -/
theorem existingNome_nonTube_zeroSpatial_bound {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K ids) (ht : ids ≠ tubeIds margin)
    (hl : spatialOddFaces margin pair.1 = []) (hr : spatialOddFaces margin pair.2 = []) :
    Q'.abs (weightedPairTerm nome K margin pair) ≤ zeroSpatialRelativeCap*qpow nome 36 :=
  Q'.le_trans' _ _ _ (nonTube_zeroSpatial_weight_bound (by decide) (by decide) (by decide) hK hs hp ht hl hr)
    (Q'.le_of_eqv existingNome_cap_pin)

end YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound

#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.parityCount_congr
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.parityCount_small
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.zero_parityCount
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.tube_parityCount
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.nonzero_pairParity_twelve
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.nonTube_zeroSpatial_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.zeroSpatialRelativeCap
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.existingNome_cap_pin
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound.existingNome_nonTube_zeroSpatial_bound

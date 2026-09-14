/-
# The complete original leading coefficient is an explicit finite count

The exact original connected selections, representation labels, and both
earlier filters are retained, including their enumeration multiplicities.
Each leading amplitude is its computed zero-one checker. Therefore the
whole signed coefficient is a natural count and is nonnegative. The count
is NOT evaluated to one or proved positive here; the higher signed
remainder and original positive-response certificate remain open.
-/

import YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude
import YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder
import YMGap.Continuum.FiniteBistochasticCarrierBalance

namespace YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBistochasticCarrierBalance
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabOriginalLeadingRemainder
open YMGap.Continuum.BF4ExactSlabMinimalPairAmplitude
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def leadingKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (pairPower margin pair = 36) && amplitudeKeep margin pair

theorem retained_leading_bit {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin))) :
    leadingPair margin pair ≈ (if leadingKeep margin pair then 1 else 0) := by
  by_cases he : pairPower margin pair = 36
  · simpa only [leadingPair,leadingKeep,he,↓reduceIte,decide_true,Bool.true_and] using
      retained_amplitude_bit hs hp he
  · simp only [leadingPair,leadingKeep,he,↓reduceIte,decide_false,Bool.false_and,Bool.false_eq_true]
    exact Q'.eqv_refl _

/-- Original enumeration with multiplicity; no deduplication or selected-tube substitution. -/
def retainedPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
    (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin))).flatMap
      (fun ids => (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))

def leadingCount (K margin time : Nat) : Nat :=
  ((retainedPairs K margin time).filter (leadingKeep margin)).length

theorem leadingCoefficient_bits (K margin time : Nat) : leadingCoefficient K margin time ≈
    listQSum (fun pair => if leadingKeep margin pair then 1 else 0) (retainedPairs K margin time) := by
  have hf := listQSum_flatMap (leadingPair margin)
    (fun ids => (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hf)
    (listQSum_congr_on _ _ (retainedPairs K margin time) (fun pair hp => by
      obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp hp
      exact retained_leading_bit hs hm))

theorem indicator_count {A : Type} (keep : A → Bool) (xs : List A) :
    listQSum (fun x => if keep x then 1 else 0) xs ≈ Q'.ofNat (xs.filter keep).length := by
  have hf := sum_filter_zero (fun x => if keep x then 1 else 0) keep xs (fun x _ hx => by
    dsimp only
    rw [hx]
    exact Q'.eqv_refl _)
  have hc := listQSum_congr_on (fun x => if keep x then 1 else 0) (fun _ => (1 : Q'))
    (xs.filter keep) (fun x hx => by
      dsimp only
      rw [(List.mem_filter.mp hx).2]
      exact Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hf (Q'.eqv_trans _ _ _ hc (listQSum_one_eqv_ofNat_length _))

theorem leadingCoefficient_count (K margin time : Nat) :
    leadingCoefficient K margin time ≈ Q'.ofNat (leadingCount K margin time) :=
  Q'.eqv_trans _ _ _ (leadingCoefficient_bits K margin time) (indicator_count _ _)

theorem leadingCoefficient_nonnegative (K margin time : Nat) : (0 : Q') ≤ leadingCoefficient K margin time := by
  have h := listQSum_nonnegative_on (fun pair => if leadingKeep margin pair then (1 : Q') else 0)
    (retainedPairs K margin time) (fun pair _ => by
      change (0 : Q') ≤ (if leadingKeep margin pair then 1 else 0)
      cases leadingKeep margin pair <;> decide)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm (leadingCoefficient_bits K margin time)))

end YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount

#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.leadingKeep
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.retained_leading_bit
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.leadingCount
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.leadingCoefficient_bits
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.indicator_count
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.leadingCoefficient_count
#print axioms YMGap.Continuum.BF4ExactSlabLeadingCoefficientCount.leadingCoefficient_nonnegative

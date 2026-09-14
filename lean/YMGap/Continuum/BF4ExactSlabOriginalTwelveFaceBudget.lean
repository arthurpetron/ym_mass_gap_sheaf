/-
# Original shifted-probe numerator: explicit twelve-face partition budget

The small-support cancellation is proved for the actual original
coefficients and fed into the cancellation-aware spectator resummation.
The two literal probes each have interval cap two, carrier size one and
four links. The resulting rational budget names the nome but contains
neither cutoff nor margin. It multiplies the SAME full partition square.

This is an absolute upper bound on the FULL original numerator, not on
its higher residual after subtracting the unit leading tube. No positive
response, continuum passage or Clay closure follows from this bound.
-/

import YMGap.Continuum.BF4ExactSlabShortSupportCancellation
import YMGap.Continuum.BF4ExactSlabCancellationTailBudget
import YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals

namespace YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabShortSupportCancellation
open YMGap.Continuum.BF4ExactSlabCancellationTailBudget
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def sliceInterval (margin : Nat) (time : Fin 4) :
    Interval (boundaryCompleteSlabLinks (responseExtent margin)).length
      (characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin) (sliceFace margin time.val)).scalar 1) 2 := by
  have hf := slice_physical margin time
  have hi : (boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf (sliceFace margin time.val) ∈
      slabPhysicalFaceEdges (responseExtent margin) := List.mem_range.mpr (List.idxOf_lt_length_of_mem hf)
  have I := fundamentalInterval (responseExtent margin) _ hi
  rw [face_lookup hf] at I
  exact I

def lowerInterval (margin : Nat) : Interval (boundaryCompleteSlabLinks (responseExtent margin)).length
    (lower (enlarge margin shiftedProbe)) 2 := by
  rw [lower_shifted_probe_pin]
  exact sliceInterval margin ⟨0,by decide⟩

def upperInterval (margin : Nat) : Interval (boundaryCompleteSlabLinks (responseExtent margin)).length
    (upper (enlarge margin shiftedProbe)) 2 := by
  rw [upper_shifted_probe_pin]
  exact sliceInterval margin ⟨3,by decide⟩

/-- Explicit nome-dependent data, independent of cutoff and receding-volume margin. -/
def responseBudget (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  (((2 : Q')*2+2*2)*probePrefactor w hd 8)*tailBudget 1562500 625 12 (adjustedCoreRate w hd) hs

theorem literal_budget_pin (margin : Nat) (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    twoProbeBudget (singletonCarrier (sliceFace margin 0)) (singletonCarrier (sliceFace margin 3))
      w hd hs 2 2 12 = responseBudget w hd hs := by
  have hc : countPrefactor (singletonCarrier (sliceFace margin 0))
      (singletonCarrier (sliceFace margin 3)) = 1562500 := by
    change 2^2*625^2 = 1562500
    decide
  have hl : (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)).length = 8 := rfl
  unfold twoProbeBudget responseBudget
  rw [hc,hl]

theorem original_large_expansion (w : Q') (K margin : Nat) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
      listQSum (fun ids => connectedCoefficient w K (responseExtent margin)
        (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids *
        partitionSquare w K (responseExtent margin) (detachedIds (responseExtent margin)
          (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3)) ids
          (slabPhysicalFaceEdges (responseExtent margin))))
        (largeConnectingAnchors (responseExtent margin) (edgesOf (sliceFace margin 0))
          (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) 12) := by
  apply resummed_large_expansion w K (responseExtent margin)
    (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe))
    2 2 (lowerInterval margin) (upperInterval margin)
    (edgesOf (sliceFace margin 0)) (edgesOf (sliceFace margin 3))
    (lower_link_local margin) (upper_link_local margin)
    (slabPhysicalFaceEdges (responseExtent margin)) 12 (CayleyParentInj.range_nodup _)
  intro ids hi hshort
  exact original_short_coefficient_zero w K margin ids (connecting_selected hi) hshort

/-- All cutoffs and margins, with the nome and all smallness guards visible. -/
theorem original_response_partition_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (K margin : Nat) :
    Q'.abs (connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe))) ≤
      responseBudget w hd hs * partitionSquare w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) := by
  rw [← literal_budget_pin margin]
  apply connectedNumerator_tail_of_small_zero hw0 hw1 hsmall hd hs K (responseExtent margin)
    (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) 2 2
    (lowerInterval margin) (upperInterval margin) _ _
    (singletonCarrier (sliceFace margin 0)) (singletonCarrier (sliceFace margin 3))
    (lower_link_local margin) (upper_link_local margin)
    (slabPhysicalFaceEdges (responseExtent margin)) 12 (CayleyParentInj.range_nodup _)
    (fun _ hi => hi)
  intro ids hi hshort
  exact original_short_coefficient_zero w K margin ids (connecting_selected hi) hshort

theorem existingNome_original_response_partition_bound (K margin : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    Q'.abs (connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe))) ≤
      responseBudget w hd hs * partitionSquare w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) :=
  original_response_partition_bound (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos)
    (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one)
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2 K margin

end YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget

#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.sliceInterval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.lowerInterval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.upperInterval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.responseBudget
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.literal_budget_pin
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.original_large_expansion
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.original_response_partition_bound
#print axioms YMGap.Continuum.BF4ExactSlabOriginalTwelveFaceBudget.existingNome_original_response_partition_bound

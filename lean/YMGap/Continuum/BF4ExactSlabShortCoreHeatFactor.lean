/-
# Exact w^39 suppression on the remaining ORIGINAL short-core sum

Each non-tube coefficient has its original signed leading term removed
before multiplication by its own detached partition square. Finite
distributivity extracts w^39 from the entire short-other-core remainder,
without replacing any partition or altering the retained representation
carrier. This holds at all rational nomes, including zero, all K>=1,
thresholds, margins and filter times.

At the existing nome, the proved large-tail absorption now leaves a
positive w^36/4 reference plus this w^39-dressed signed cofactor. The
cofactor has no useful uniform magnitude bound yet. Positive full
response and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabNonTubeHeatPower
import YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate

namespace YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabNonTubeHeatPower
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem shortOtherCores_connected {threshold margin : Nat} {ids : List Nat}
    (hi : ids ∈ shortOtherCores threshold margin) :
    ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hc := (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp hi).1).1).1
  exact List.mem_filter.mpr ⟨connecting_selected hc,connecting_keep hc⟩

def shortResidualTerm (w : Q') (K margin time : Nat) (ids : List Nat) : Q' :=
  nonTubeCoefficientResidual w K margin time ids * partitionSquare w K (responseExtent margin)
    (detachedIds (responseExtent margin) (edgesOf (sliceFace margin 0)++edgesOf (sliceFace margin 3))
      ids (slabPhysicalFaceEdges (responseExtent margin)))

def shortHeatResidual (w : Q') (K threshold margin time : Nat) : Q' :=
  listQSum (shortResidualTerm w K margin time) (shortOtherCores threshold margin)

theorem short_core_term_factorization (w : Q') (K threshold margin time : Nat) (ids : List Nat)
    (hK : 1 ≤ K) (hi : ids ∈ shortOtherCores threshold margin) :
    coreTerm w K margin ids ≈ qpow w 39 * shortResidualTerm w K margin time ids :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
    (nonTube_coefficient_factorization w K margin time ids hK (shortOtherCores_connected hi)
      (shortOtherCores_window hi).2.2)) (Q'.mul_assoc_eqv _ _ _)

/-- Exact signed cofactor on the same short-core list, with every detached partition retained. -/
theorem shortOtherRemainder_factorization (w : Q') (K threshold margin time : Nat) (hK : 1 ≤ K) :
    shortOtherRemainder w K threshold margin ≈ qpow w 39 * shortHeatResidual w K threshold margin time := by
  exact Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _
    (fun ids hi => short_core_term_factorization w K threshold margin time ids hK hi))
    (listQSum_mul_left (qpow w 39) (shortResidualTerm w K margin time) (shortOtherCores threshold margin))

private theorem lower_recode (a s r n : Q') (he : s ≈ r) (h : a+s ≤ n) : a+r ≤ n :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left a _ _ he)) h

/-- Original numerator bound after both large-tail absorption and local leading cancellation. -/
theorem original_numerator_lower_with_heat_residual (K margin time : Nat) (hK : 1 ≤ K) :
    tailAllowance * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) +
      qpow nome 39 * shortHeatResidual nome K 33 margin time ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) :=
  lower_recode
    (tailAllowance * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (shortOtherRemainder nome K 33 margin) (qpow nome 39 * shortHeatResidual nome K 33 margin time)
    (connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)))
    (shortOtherRemainder_factorization nome K 33 margin time hK)
    (original_numerator_lower_with_short_remainder K margin hK)

end YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor

#print axioms YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor.shortOtherCores_connected
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor.shortResidualTerm
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor.shortHeatResidual
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor.short_core_term_factorization
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor.shortOtherRemainder_factorization
#print axioms YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor.original_numerator_lower_with_heat_residual

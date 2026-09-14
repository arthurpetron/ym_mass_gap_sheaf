/-
# The COMPLETE original connected numerator has an explicit w^36 cofactor

The exact connected-selection and representation expansion retains the
original face weights and four signed moments. Each retained pair has
power at least 36. Finite distributivity extracts w^36 from the entire
numerator, leaving a computed signed cofactor. No division, small-nome
assumption, leading-coefficient sign or uniform remainder bound is used.
-/

import YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower

namespace YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

/-- Explicit finite cofactor on the same retained replica carrier, including all signs. -/
def numeratorResidual (w : Q') (K margin time : Nat) : Q' :=
  listQSum (fun ids => listQSum (pairResidual w margin)
    (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))

theorem original_numerator_factorization (w : Q') (K margin time : Nat) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
        qpow w 36 * numeratorResidual w K margin time := by
  refine Q'.eqv_trans _ _ _ (original_numerator_leaf_filter w K margin time) ?_
  refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ (fun ids => qpow w 36 *
    listQSum (pairResidual w margin)
      (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin))) _ (fun ids hs => ?_)) ?_
  · refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun pair hp =>
      retained_pair_factorization w hs hp)) ?_
    exact listQSum_mul_left (qpow w 36) (pairResidual w margin) _
  · exact listQSum_mul_left (qpow w 36) _ _

end YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower

#print axioms YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower.numeratorResidual
#print axioms YMGap.Continuum.BF4ExactSlabOriginalNumeratorHeatPower.original_numerator_factorization

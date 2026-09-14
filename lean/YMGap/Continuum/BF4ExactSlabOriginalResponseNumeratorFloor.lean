/-
# A positive floor for the complete ORIGINAL shifted-probe numerator

All original signed remainder families, including every spatial forest and
every higher spin, are now absorbed into the same tube reference. For every
K>=1 and volume margin, the full connected numerator is at least
(1/16)*w^36*Z_full^2 at fixed SU(2) nome w=1/1024.

The partition is the SAME original full partition, not a detached or
positive-model replacement. This is the finite-cutoff numerator floor;
cutoff removal, exact normalization and thermodynamic response transport
must still preserve this floor before claiming an excited-response witness.
No continuum or coupling-uniform physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound

namespace YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound
open YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder
open YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder (absorb_signed_branch)
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def responseFloor : Q' := Q'.invSucc 15*qpow nome 36

theorem responseFloor_positive : (0 : Q') < responseFloor := by decide

theorem responseFloor_available : responseFloor ≤ afterFourCapAllowance + -remainingAllowance := by decide

theorem original_numerator_floor (K margin : Nat) (hK : 1 ≤ K) :
    responseFloor*partitionSquare nome K (responseExtent margin)
      (slabPhysicalFaceEdges (responseExtent margin)) ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) := by
  have h := absorb_signed_branch afterFourCapAllowance remainingAllowance
    (partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (afterFourCapRemainder nome K margin 0) (afterFourCapRemainder nome K margin 0) 0 _
    (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))
    (original_remaining_remainder_bound K margin 0)
    (original_numerator_lower_after_fourCap K margin 0 hK)
  have hc := Q'.mul_le_mul_of_nonneg_right _ _
    (partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    responseFloor_available (SumOfSquares.q_mul_self_nonneg _)
  exact Q'.le_trans' _ _ _ hc (Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))) h)

end YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor

#print axioms YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor.responseFloor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor.responseFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor.responseFloor_available
#print axioms YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor.original_numerator_floor

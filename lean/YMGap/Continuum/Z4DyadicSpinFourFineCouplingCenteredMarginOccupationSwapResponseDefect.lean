/-
# Expanded-fiber lift of the occupation cocycle and its response defect

The cutoff-one antisymmetric source determinant factors through a common
coupling-one physical product.  That physical product still contains the
cardinality of the SU(2) intertwiner fiber, so it is not pointwise invariant
under a physical support swap.  This module expands those cardinalities into
literal pairs of intertwiner assignments.  Each expanded pair then carries
only the coupling-one face product, which is exactly invariant under every
facewise transposition.

For one expanded assignment pair, the occupation cocycle lifts to the exact
three-term identity

  source term
    = switched term
      + component-skew term
      + switched-cofactor * switched-row-response defect.

Thus the algebraic and multiplicity seams are closed separately.  The final
term records precisely the remaining analytic obligation: prove that a
support component disconnected from the selected coarse event does not
change that event's block-kernel row response, or bound the change on the
component which reaches it.

No response-locality theorem, connected-residue estimate, uniform covariance
bound, continuum construction, OS/GNS reconstruction, Hamiltonian gap, or
Yang--Mills mass gap is asserted here.

Constructive contract: exact finite disintegration and rational setoid
algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
import YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem cocycle_response_decompose_local
    (switched correction weight response switchedResponse : Q') :
    (switched + correction) * (weight * response) ≈
      switched * (weight * switchedResponse) +
        (correction * (weight * response) +
          switched * (weight * (response - switchedResponse))) := by
  have hresponse : response ≈
      switchedResponse + (response - switchedResponse) :=
    Q'.add_sub_cancel_eqv response switchedResponse
  have hweighted : weight * response ≈
      weight * switchedResponse +
        weight * (response - switchedResponse) :=
    Q'.eqv_trans _
      (weight * (switchedResponse +
        (response - switchedResponse))) _
      (Q'.mul_eqv_congr_left weight _ _ hresponse)
      (Q'.mul_add_eqv weight switchedResponse
        (response - switchedResponse))
  refine Q'.eqv_trans _
    (switched * (weight * response) +
      correction * (weight * response)) _
    (Q'.add_mul_eqv switched correction (weight * response)) ?_
  refine Q'.eqv_trans _
    (switched *
        (weight * switchedResponse +
          weight * (response - switchedResponse)) +
      correction * (weight * response)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left switched _ _ hweighted)
  refine Q'.eqv_trans _
    ((switched * (weight * switchedResponse) +
        switched * (weight * (response - switchedResponse))) +
      correction * (weight * response)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_add_eqv switched
        (weight * switchedResponse)
        (weight * (response - switchedResponse)))
  refine Q'.eqv_trans _
    (switched * (weight * switchedResponse) +
      (switched * (weight * (response - switchedResponse)) +
        correction * (weight * response))) _ ?_ ?_
  · exact Q'.add_assoc_eqv _ _ _
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.add_comm_eqv
      (switched * (weight * (response - switchedResponse)))
      (correction * (weight * response)))

/-! ## 1. The literal coupling-one expanded fiber -/

/-- The fine slab with unchanged cutoff and geometry and with heat nome one.
Its physical and auxiliary carriers are definitionally independent of the
changed coupling; only their numerical weights change. -/
def fineUnitCouplingSlabPhysicalData (S : SlabScalePair) : SlabPhysicalData where
  coupling := 1
  coupling_nonnegative := by decide
  cutoff := S.fine.cutoff
  half := S.fine.half

theorem fineUnitCouplingSlabPhysicalData_extent (S : SlabScalePair) :
    (fineUnitCouplingSlabPhysicalData S).extent = S.fine.extent := rfl

theorem fineUnitCouplingSlabPhysicalData_physicalTerm
    (S : SlabScalePair) (source : EdgeLabelling) :
    (fineUnitCouplingSlabPhysicalData S).physicalTerm source =
      fineUnitCouplingPhysicalTerm S source := rfl

/-- The two independent SU(2) intertwiner assignments above one physical
source pair. -/
def fineUnitCouplingExpandedFiberPairCarrier
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair) :
    List (SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :=
  cartesian
    (slabFineFusionWitnesses (fineUnitCouplingSlabPhysicalData S) pair.1)
    (slabFineFusionWitnesses (fineUnitCouplingSlabPhysicalData S) pair.2)

/-- One coupling-one expanded two-replica fiber weight.  Each retained
assignment has one counting unit, so its numerical content is the common
face-factor product. -/
def fineUnitCouplingExpandedFiberPairWeight
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair)
    (assignments : SlabFusionWitnessAssignment ×
      SlabFusionWitnessAssignment) : Q' :=
  retainedFineIntertwinerPhysicalFiberWeight
      (fineUnitCouplingSlabPhysicalData S) pair.1 assignments.1 *
    retainedFineIntertwinerPhysicalFiberWeight
      (fineUnitCouplingSlabPhysicalData S) pair.2 assignments.2

/-- Summing the literal assignment-pair fiber reconstructs the two physical
coupling-one multiplicities exactly. -/
theorem fineUnitCouplingExpandedFiberPairWeight_total
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair) :
    listQSum
        (fineUnitCouplingExpandedFiberPairWeight S pair)
        (fineUnitCouplingExpandedFiberPairCarrier S pair) ≈
      fineUnitCouplingPhysicalTerm S pair.1 *
        fineUnitCouplingPhysicalTerm S pair.2 := by
  refine Q'.eqv_trans _
    (listQSum
        (retainedFineIntertwinerPhysicalFiberWeight
          (fineUnitCouplingSlabPhysicalData S) pair.1)
        (slabFineFusionWitnesses
          (fineUnitCouplingSlabPhysicalData S) pair.1) *
      listQSum
        (retainedFineIntertwinerPhysicalFiberWeight
          (fineUnitCouplingSlabPhysicalData S) pair.2)
        (slabFineFusionWitnesses
          (fineUnitCouplingSlabPhysicalData S) pair.2)) _ ?_ ?_
  · exact listQSum_cartesian_product
      (retainedFineIntertwinerPhysicalFiberWeight
        (fineUnitCouplingSlabPhysicalData S) pair.1)
      (retainedFineIntertwinerPhysicalFiberWeight
        (fineUnitCouplingSlabPhysicalData S) pair.2)
      (slabFineFusionWitnesses
        (fineUnitCouplingSlabPhysicalData S) pair.1)
      (slabFineFusionWitnesses
        (fineUnitCouplingSlabPhysicalData S) pair.2)
  · exact mul_eqv_both_local
      (by
        simpa only [fineUnitCouplingSlabPhysicalData_physicalTerm] using
          retainedFineIntertwinerPhysicalFiberWeight_total
            (fineUnitCouplingSlabPhysicalData S) pair.1)
      (by
        simpa only [fineUnitCouplingSlabPhysicalData_physicalTerm] using
          retainedFineIntertwinerPhysicalFiberWeight_total
            (fineUnitCouplingSlabPhysicalData S) pair.2)

/-- Once physical multiplicity has been expanded into assignments, the
coupling-one pair weight is exactly invariant under the canonical support
swap, for arbitrary source and target assignment choices. -/
theorem fineUnitCouplingExpandedFiberPairWeight_supportSwap
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (sourceAssignments targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    fineUnitCouplingExpandedFiberPairWeight S
        (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair)
        targetAssignments ≈
      fineUnitCouplingExpandedFiberPairWeight S pair sourceAssignments := by
  unfold fineUnitCouplingExpandedFiberPairWeight
    fineCouplingPhysicalSupportSwappedPair
  exact retainedFineIntertwinerPhysicalFiberWeight_pair_faceSwap
    (fineUnitCouplingSlabPhysicalData S)
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.1 pair.2 sourceAssignments.1 sourceAssignments.2
    targetAssignments.1 targetAssignments.2

/-! ## 2. Expanded antisymmetric response terms -/

/-- Difference of the two selected block-kernel row responses. -/
def fineCouplingPhysicalPairEventResponseDifference
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalSourcePair) : Q' :=
  fineCouplingKernelOutputEventMass K pair.1 event -
    fineCouplingKernelOutputEventMass K pair.2 event

/-- Change in the row-response difference under the canonical support swap.
This is the exact analytic defect left after weight transport. -/
def fineCouplingPhysicalSupportSwapResponseDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) : Q' :=
  fineCouplingPhysicalPairEventResponseDifference K event pair -
    fineCouplingPhysicalPairEventResponseDifference K event
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair)

/-- One literal expanded-fiber term of the antisymmetric occupation
determinant against a kernel-row response difference. -/
def fineCouplingExpandedOccupationResponseTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalSourcePair)
    (assignments : SlabFusionWitnessAssignment ×
      SlabFusionWitnessAssignment) : Q' :=
  fineCouplingPhysicalOccupationSkewCoefficient S pair *
    (fineUnitCouplingExpandedFiberPairWeight S pair assignments *
      fineCouplingPhysicalPairEventResponseDifference K event pair)

/-- The sum over the two literal intertwiner fibers is exactly the original
physical antisymmetric source-pair term.  In particular no link-multiplicity
factor is discarded when passing to the switchable carrier. -/
theorem fineCouplingExpandedOccupationResponseTerm_total
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool)
    (pair : FineCouplingPhysicalSourcePair)
    (hleft : pair.1 ∈ S.fine.physicalLabellings)
    (hright : pair.2 ∈ S.fine.physicalLabellings) :
    listQSum
        (fineCouplingExpandedOccupationResponseTerm K event pair)
        (fineUnitCouplingExpandedFiberPairCarrier S pair) ≈
      fineCouplingPhysicalAntisymmetricSourcePairDifferenceTerm
        K event pair := by
  let coefficient := fineCouplingPhysicalOccupationSkewCoefficient S pair
  let response := fineCouplingPhysicalPairEventResponseDifference K event pair
  let weight := fineUnitCouplingExpandedFiberPairWeight S pair
  let carrier := fineUnitCouplingExpandedFiberPairCarrier S pair
  refine Q'.eqv_trans _
    (coefficient * listQSum (fun choice => weight choice * response) carrier)
    _ ?_ ?_
  · exact listQSum_mul_left coefficient
      (fun choice => weight choice * response) carrier
  refine Q'.eqv_trans _
    (coefficient * (listQSum weight carrier * response)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coefficient _ _
      (listQSum_mul_right weight response carrier)
  refine Q'.eqv_trans _
    (coefficient *
      ((fineUnitCouplingPhysicalTerm S pair.1 *
        fineUnitCouplingPhysicalTerm S pair.2) * response)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coefficient _ _
      (Q'.mul_eqv_congr_right _ _ response
        (fineUnitCouplingExpandedFiberPairWeight_total S pair))
  refine Q'.eqv_trans _
    ((coefficient *
      (fineUnitCouplingPhysicalTerm S pair.1 *
        fineUnitCouplingPhysicalTerm S pair.2)) * response) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv coefficient
        (fineUnitCouplingPhysicalTerm S pair.1 *
          fineUnitCouplingPhysicalTerm S pair.2) response)
  unfold fineCouplingPhysicalAntisymmetricSourcePairDifferenceTerm
    antisymmetricPairDifferenceTerm
  change
    (coefficient *
        (fineUnitCouplingPhysicalTerm S pair.1 *
          fineUnitCouplingPhysicalTerm S pair.2)) * response ≈
      (fineCouplingPhysicalMarginTerm S pair.1 *
          S.fine.physicalTerm pair.2 -
        S.fine.physicalTerm pair.1 *
          fineCouplingPhysicalMarginTerm S pair.2) * response
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (fineCouplingPhysicalAntisymmetricMassDeterminant_eqv_occupationSkew
        S hfineCutoff pair hleft hright))

/-! ## 3. The exact response-defect decomposition -/

/-- **Expanded support-swap decomposition.**  The scalar cocycle and exact
expanded-fiber weight preservation leave only the component occupation skew
and the literal change of the selected block-kernel row response. -/
theorem fineCouplingExpandedOccupationResponseTerm_supportSwap_decomposition
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (sourceAssignments targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    fineCouplingExpandedOccupationResponseTerm
        K event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm K event
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair) targetAssignments +
        (((qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.1) +
            qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.2)) *
          fineCouplingPhysicalComponentOccupationSkewCoefficient
            S targetFaceId pair) *
          (fineUnitCouplingExpandedFiberPairWeight
              S pair sourceAssignments *
            fineCouplingPhysicalPairEventResponseDifference
              K event pair) +
          fineCouplingPhysicalOccupationSkewCoefficient S
            (fineCouplingPhysicalSupportSwappedPair
              S targetFaceId pair) *
          (fineUnitCouplingExpandedFiberPairWeight S
              (fineCouplingPhysicalSupportSwappedPair
                S targetFaceId pair) targetAssignments *
            fineCouplingPhysicalSupportSwapResponseDefect
              K event targetFaceId pair)) := by
  let swapped := fineCouplingPhysicalSupportSwappedPair
    S targetFaceId pair
  let coefficient := fineCouplingPhysicalOccupationSkewCoefficient S pair
  let switchedCoefficient :=
    fineCouplingPhysicalOccupationSkewCoefficient S swapped
  let componentCorrection :=
    (qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.1) +
      qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.2)) *
      fineCouplingPhysicalComponentOccupationSkewCoefficient
        S targetFaceId pair
  let weight := fineUnitCouplingExpandedFiberPairWeight
    S pair sourceAssignments
  let switchedWeight := fineUnitCouplingExpandedFiberPairWeight
    S swapped targetAssignments
  let response := fineCouplingPhysicalPairEventResponseDifference
    K event pair
  let switchedResponse := fineCouplingPhysicalPairEventResponseDifference
    K event swapped
  have hcoefficient : coefficient ≈
      switchedCoefficient + componentCorrection := by
    simpa only [coefficient, switchedCoefficient, componentCorrection,
      swapped] using
      fineCouplingPhysicalOccupationSkewCoefficient_componentSwap_cocycle
        S targetFaceId pair
  have hweight : switchedWeight ≈ weight := by
    simpa only [switchedWeight, weight, swapped] using
      fineUnitCouplingExpandedFiberPairWeight_supportSwap
        S targetFaceId pair sourceAssignments targetAssignments
  change coefficient * (weight * response) ≈
    switchedCoefficient * (switchedWeight * switchedResponse) +
      (componentCorrection * (weight * response) +
      switchedCoefficient *
        (switchedWeight * (response - switchedResponse)))
  refine Q'.eqv_trans _
    ((switchedCoefficient + componentCorrection) *
      (weight * response)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hcoefficient
  refine Q'.eqv_trans _
    (switchedCoefficient * (weight * switchedResponse) +
      (componentCorrection * (weight * response) +
        switchedCoefficient * (weight * (response - switchedResponse)))) _ ?_ ?_
  · exact cocycle_response_decompose_local
      switchedCoefficient componentCorrection weight response
      switchedResponse
  apply Q'.add_eqv_congr'
  · exact Q'.mul_eqv_congr_left switchedCoefficient _ _
      (Q'.mul_eqv_congr_right _ _ switchedResponse
        (Q'.eqv_symm hweight))
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_refl _
  · exact Q'.mul_eqv_congr_left switchedCoefficient _ _
      (Q'.mul_eqv_congr_right _ _ (response - switchedResponse)
        (Q'.eqv_symm hweight))

#print axioms fineUnitCouplingSlabPhysicalData
#print axioms fineUnitCouplingSlabPhysicalData_extent
#print axioms fineUnitCouplingSlabPhysicalData_physicalTerm
#print axioms fineUnitCouplingExpandedFiberPairCarrier
#print axioms fineUnitCouplingExpandedFiberPairWeight
#print axioms fineUnitCouplingExpandedFiberPairWeight_total
#print axioms fineUnitCouplingExpandedFiberPairWeight_supportSwap
#print axioms fineCouplingPhysicalPairEventResponseDifference
#print axioms fineCouplingPhysicalSupportSwapResponseDefect
#print axioms fineCouplingExpandedOccupationResponseTerm
#print axioms fineCouplingExpandedOccupationResponseTerm_total
#print axioms fineCouplingExpandedOccupationResponseTerm_supportSwap_decomposition

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect

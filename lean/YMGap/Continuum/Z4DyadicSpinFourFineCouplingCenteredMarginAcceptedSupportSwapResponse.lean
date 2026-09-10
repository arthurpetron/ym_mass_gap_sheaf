/-
# Accepted support-swap coordinates and the actual raw response seam

The expanded occupation-response cocycle is stated for an arbitrary pair of
physical fine states and arbitrary source/target intertwiner assignments.
This module places it on the literal support-disconnected observable carrier.
The source coordinates are the two accepted expanded entries, while the
target coordinates are an actual recoupled target pair in the opposite
four-cell.  Their physical pair is exactly the canonical support swap.

For the production cutoff-one block kernel, the remaining response defect is
then rewritten as a difference of four whole-slab raw event ratios.  This is
the decisive locality seam: every numerator is selected from the literal
globally link-glued raw row and every denominator is its complete row
partition.  No event-locality or cancellation across those denominators is
assumed.

No response bound, balanced-blocking estimate, continuum construction,
OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills mass gap is asserted.

Constructive contract: exact finite carriers and rational setoid algebra
only; no choice, proof hole, classical witness erasure, trusted external
computation, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem sub_eqv_zero_of_eqv_local {a b : Q'}
    (h : a ≈ b) : a - b ≈ 0 := by
  exact Q'.eqv_trans _ (b + -b) _
    (Q'.add_eqv_congr' h (Q'.eqv_refl _))
    (Q'.add_neg_self_eqv b)

/-! ## 1. Literal accepted source and recoupled target coordinates -/

/-- The physical pair underlying one support-disconnected accepted source. -/
def fineCouplingAcceptedSeparatedPhysicalPair
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : FineCouplingPhysicalSourcePair :=
  (source.1.1.1.1, source.1.2.1.1)

/-- The two literal source assignments attached to the accepted pair. -/
def fineCouplingAcceptedSeparatedAssignmentPair
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    SlabFusionWitnessAssignment × SlabFusionWitnessAssignment :=
  (source.1.1.1.2, source.1.2.1.2)

/-- The physical coordinates of one actual recoupled target in the opposite
observable four-cell. -/
def fineCouplingAcceptedRecoupledPhysicalPair
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    FineCouplingPhysicalSourcePair :=
  let target := slabObservablePairedSupportRecoupledTargetPair
    S.fine rootFaceId targetFaceId htarget source choice
  (target.1.1.1, target.2.1.1)

/-- The two accepted auxiliary assignments of the same recoupled target. -/
def fineCouplingAcceptedRecoupledAssignmentPair
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    SlabFusionWitnessAssignment × SlabFusionWitnessAssignment :=
  let target := slabObservablePairedSupportRecoupledTargetPair
    S.fine rootFaceId targetFaceId htarget source choice
  (target.1.1.2, target.2.1.2)

theorem fineCouplingAcceptedSeparated_supportSwapped_left
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (fineCouplingPhysicalSupportSwappedPair S targetFaceId
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)).1 =
      slabObservablePairSupportSwitchedLeftPhysical
        S.fine targetFaceId source.1 := rfl

theorem fineCouplingAcceptedSeparated_supportSwapped_right
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (fineCouplingPhysicalSupportSwappedPair S targetFaceId
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)).2 =
      slabObservablePairSupportSwitchedRightPhysical
        S.fine targetFaceId source.1 := rfl

/-- The generic target-rooted support swap is the physical pair carried by
every realized recoupling column. -/
theorem fineCouplingAcceptedSeparated_supportSwapped_eq_recoupledPhysical
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    fineCouplingPhysicalSupportSwappedPair S targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source) =
      fineCouplingAcceptedRecoupledPhysicalPair
        S rootFaceId targetFaceId htarget source choice := by
  apply Prod.ext
  · change
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source)).1 =
        (slabObservablePairedSupportRecoupledLeftEntry
          S.fine rootFaceId targetFaceId htarget source choice).1.1
    exact Eq.trans
      (fineCouplingAcceptedSeparated_supportSwapped_left
        S rootFaceId targetFaceId source)
      (slabObservablePairedSupportRecoupledLeftEntry_physical
        S.fine rootFaceId targetFaceId htarget source choice).symm
  · change
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source)).2 =
        (slabObservablePairedSupportRecoupledRightEntry
          S.fine rootFaceId targetFaceId htarget source choice).1.1
    exact Eq.trans
      (fineCouplingAcceptedSeparated_supportSwapped_right
        S rootFaceId targetFaceId source)
      (slabObservablePairedSupportRecoupledRightEntry_physical
        S.fine rootFaceId targetFaceId htarget source choice).symm

/-- The recoupled coordinate pair used below is not a formal surrogate: its
bundled pair is a literal member of the common target four-cell. -/
theorem fineCouplingAcceptedRecoupledTargetPair_mem
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    slabObservablePairedSupportRecoupledTargetPair
        S.fine rootFaceId targetFaceId htarget source choice ∈
      slabObservableFourCellTargetPairs
        S.fine rootFaceId targetFaceId :=
  slabObservablePairedSupportRecoupledTargetPair_mem
    S.fine rootFaceId targetFaceId htarget source choice

/-! ## 2. Accepted specialization of the expanded cocycle -/

/-- The exact expanded response decomposition now uses the literal accepted
source assignments and the literal assignments of an actual recoupled target
four-cell member. -/
theorem fineCouplingAcceptedSeparatedOccupationResponse_decomposition
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingAcceptedRecoupledPhysicalPair
      S rootFaceId targetFaceId htarget source choice
    let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
      S rootFaceId targetFaceId source
    let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
      S rootFaceId targetFaceId htarget source choice
    fineCouplingExpandedOccupationResponseTerm
        K event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm
          K event swapped targetAssignments +
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
          fineCouplingPhysicalOccupationSkewCoefficient S swapped *
          (fineUnitCouplingExpandedFiberPairWeight
              S swapped targetAssignments *
            fineCouplingPhysicalSupportSwapResponseDefect
              K event targetFaceId pair)) := by
  dsimp only
  rw [← fineCouplingAcceptedSeparated_supportSwapped_eq_recoupledPhysical
    S rootFaceId targetFaceId htarget source choice]
  exact fineCouplingExpandedOccupationResponseTerm_supportSwap_decomposition
    K event targetFaceId
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      (fineCouplingAcceptedSeparatedAssignmentPair
        S rootFaceId targetFaceId source)
      (fineCouplingAcceptedRecoupledAssignmentPair
        S rootFaceId targetFaceId htarget source choice)

/-! ## 3. The precise event-response locality certificate -/

/-- The minimal two-row statement that the selected output event is
unchanged by the canonical support swap.  It is intentionally a proposition,
not a field added to the generic finite-kernel structure. -/
structure FineCouplingSupportSwapEventInvariant
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) : Prop where
  left : fineCouplingKernelOutputEventMass K pair.1 event ≈
    fineCouplingKernelOutputEventMass K
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair).1 event
  right : fineCouplingKernelOutputEventMass K pair.2 event ≈
    fineCouplingKernelOutputEventMass K
      (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair).2 event

theorem FineCouplingSupportSwapEventInvariant.pairResponseDifference
    {S : SlabScalePair} {K : S.FiniteSlabKernel}
    {event : EdgeLabelling → Bool} {targetFaceId : Nat}
    {pair : FineCouplingPhysicalSourcePair}
    (h : FineCouplingSupportSwapEventInvariant
      K event targetFaceId pair) :
    fineCouplingPhysicalPairEventResponseDifference K event pair ≈
      fineCouplingPhysicalPairEventResponseDifference K event
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair) := by
  unfold fineCouplingPhysicalPairEventResponseDifference
  exact sub_eqv_both_local h.left h.right

theorem FineCouplingSupportSwapEventInvariant.responseDefect_eqv_zero
    {S : SlabScalePair} {K : S.FiniteSlabKernel}
    {event : EdgeLabelling → Bool} {targetFaceId : Nat}
    {pair : FineCouplingPhysicalSourcePair}
    (h : FineCouplingSupportSwapEventInvariant
      K event targetFaceId pair) :
    fineCouplingPhysicalSupportSwapResponseDefect
        K event targetFaceId pair ≈ 0 := by
  unfold fineCouplingPhysicalSupportSwapResponseDefect
  exact sub_eqv_zero_of_eqv_local h.pairResponseDifference

/-- Once the response defect itself vanishes, the accepted decomposition
contracts exactly to the switched target term plus the explicit component
occupation correction.  This is the weakest exact compiler needed by a
cross-partition cancellation proof. -/
theorem fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_responseDefect_eqv_zero
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source)
    (hresponseDefect : fineCouplingPhysicalSupportSwapResponseDefect
      K event targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source) ≈ 0) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingAcceptedRecoupledPhysicalPair
      S rootFaceId targetFaceId htarget source choice
    let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
      S rootFaceId targetFaceId source
    let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
      S rootFaceId targetFaceId htarget source choice
    fineCouplingExpandedOccupationResponseTerm
        K event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm
          K event swapped targetAssignments +
        ((qpow S.fine.coupling
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
              K event pair) := by
  dsimp only
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingAcceptedRecoupledPhysicalPair
    S rootFaceId targetFaceId htarget source choice
  let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
    S rootFaceId targetFaceId source
  let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
    S rootFaceId targetFaceId htarget source choice
  let correction :=
    ((qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.1) +
        qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.2)) *
      fineCouplingPhysicalComponentOccupationSkewCoefficient
        S targetFaceId pair) *
      (fineUnitCouplingExpandedFiberPairWeight
          S pair sourceAssignments *
        fineCouplingPhysicalPairEventResponseDifference K event pair)
  let defectTerm :=
    fineCouplingPhysicalOccupationSkewCoefficient S swapped *
      (fineUnitCouplingExpandedFiberPairWeight
          S swapped targetAssignments *
        fineCouplingPhysicalSupportSwapResponseDefect
          K event targetFaceId pair)
  have hfull :
      fineCouplingExpandedOccupationResponseTerm
          K event pair sourceAssignments ≈
        fineCouplingExpandedOccupationResponseTerm
            K event swapped targetAssignments +
          (correction + defectTerm) := by
    simpa only [pair, swapped, sourceAssignments, targetAssignments,
      correction, defectTerm] using
      fineCouplingAcceptedSeparatedOccupationResponse_decomposition
        K event rootFaceId targetFaceId htarget source choice
  have hinner :
      fineUnitCouplingExpandedFiberPairWeight
            S swapped targetAssignments *
          fineCouplingPhysicalSupportSwapResponseDefect
            K event targetFaceId pair ≈ 0 :=
    Q'.eqv_trans _
      (fineUnitCouplingExpandedFiberPairWeight
        S swapped targetAssignments * 0) _
      (Q'.mul_eqv_congr_left
        (fineUnitCouplingExpandedFiberPairWeight
          S swapped targetAssignments) _ _ hresponseDefect)
      (Q'.mul_zero_eqv _)
  have hdefectTerm : defectTerm ≈ 0 := by
    unfold defectTerm
    exact Q'.eqv_trans _
      (fineCouplingPhysicalOccupationSkewCoefficient S swapped * 0) _
      (Q'.mul_eqv_congr_left
        (fineCouplingPhysicalOccupationSkewCoefficient S swapped)
        _ _ hinner)
      (Q'.mul_zero_eqv _)
  refine Q'.eqv_trans _
    (fineCouplingExpandedOccupationResponseTerm
        K event swapped targetAssignments +
      (correction + defectTerm)) _ hfull ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_refl _
  exact Q'.eqv_trans _ (correction + 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) hdefectTerm)
    (Q'.eqv_of_eq (Q'.add_zero' correction))

/-- The stronger two-row event-invariance certificate supplies the minimal
vanishing-response-defect compiler automatically. -/
theorem fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_eventInvariant
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source)
    (hinvariant : FineCouplingSupportSwapEventInvariant
      K event targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source)) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingAcceptedRecoupledPhysicalPair
      S rootFaceId targetFaceId htarget source choice
    let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
      S rootFaceId targetFaceId source
    let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
      S rootFaceId targetFaceId htarget source choice
    fineCouplingExpandedOccupationResponseTerm
        K event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm
          K event swapped targetAssignments +
        ((qpow S.fine.coupling
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
              K event pair) := by
  exact
    fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_responseDefect_eqv_zero
      K event rootFaceId targetFaceId htarget source choice
      hinvariant.responseDefect_eqv_zero

/-! ## 4. Positive accepted rows and the actual raw-ratio normal form -/

private theorem qOfNat_pos_of_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

/-- Positive heat coefficients plus one accepted global intertwiner
assignment make the complete physical source term strictly positive. -/
theorem slabPhysicalTerm_pos_of_bounded_of_fusionWitness
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded D.cutoff D.extent physical)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical) :
    (0 : Q') < D.physicalTerm physical := by
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent physical :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      D hcoupling physical hbounded
  have hlength : 0 < (slabFineFusionWitnesses D physical).length :=
    List.length_pos_of_mem hassignment
  have hmultiplicity : 0 < slabExplicitLinkMultiplicityProduct
      D.cutoff D.extent physical := by
    rwa [slabFineFusionWitnesses_length] at hlength
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos_local hmultiplicity)

/-- The first physical row of an accepted separated source is positive at
positive fine coupling. -/
theorem fineCouplingAcceptedSeparated_left_physicalTerm_pos
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (0 : Q') < S.fine.physicalTerm
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source).1 := by
  exact slabPhysicalTerm_pos_of_bounded_of_fusionWitness
    S.fine hfineCoupling source.1.1.1.1
    (SlabObservablePositiveSourceEntry.physical_bounded source.1.1)
    source.1.1.1.2
    source.1.1.assignment_mem

/-- The second source row is positive for the same reason. -/
theorem fineCouplingAcceptedSeparated_right_physicalTerm_pos
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (0 : Q') < S.fine.physicalTerm
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source).2 := by
  exact slabPhysicalTerm_pos_of_bounded_of_fusionWitness
    S.fine hfineCoupling source.1.2.1.1
    (SlabExpandedFineSourceEntry.physical_bounded source.1.2)
    source.1.2.1.2
    (slabExpandedFineSourceEntryAssignment_mem source.1.2)

/-- The left switched row remains positive because the whole-link switch
constructs a literal accepted assignment above it. -/
theorem fineCouplingAcceptedSeparated_swappedLeft_physicalTerm_pos
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (0 : Q') < S.fine.physicalTerm
      (slabObservablePairSupportSwitchedLeftPhysical
        S.fine targetFaceId source.1) := by
  exact slabPhysicalTerm_pos_of_bounded_of_fusionWitness
    S.fine hfineCoupling
    (slabObservablePairSupportSwitchedLeftPhysical
      S.fine targetFaceId source.1)
    (slabObservablePairedSupportSwitchedLeftPhysical_bounded
      S.fine source)
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment_mem htarget)

/-- The right switched row likewise remains strictly positive. -/
theorem fineCouplingAcceptedSeparated_swappedRight_physicalTerm_pos
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (0 : Q') < S.fine.physicalTerm
      (slabObservablePairSupportSwitchedRightPhysical
        S.fine targetFaceId source.1) := by
  exact slabPhysicalTerm_pos_of_bounded_of_fusionWitness
    S.fine hfineCoupling
    (slabObservablePairSupportSwitchedRightPhysical
      S.fine targetFaceId source.1)
    (slabObservablePairedSupportSwitchedRightPhysical_bounded
      S.fine source)
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment_mem htarget)

private theorem fineCouplingKernelOutputEventMass_eqv_finiteEventMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (source : EdgeLabelling) (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass K source event ≈
      finiteEventMass (K.kernel source)
        S.coarse.physicalLabellings event := by
  unfold fineCouplingKernelOutputEventMass finiteEventMass
  exact listQSum_filter (K.kernel source) event
    S.coarse.physicalLabellings

/-- On a positive row of the actual block kernel, the event response used by
the occupation cocycle is exactly the globally normalized raw event ratio. -/
theorem fineCouplingPhysicalKernelOutputEventMass_eqv_positiveRawRatio
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (event : EdgeLabelling → Bool) :
    fineCouplingKernelOutputEventMass
        (physicalKernel S hfineCutoff hcoarseCoupling) source event ≈
      positivePhysicalRawEventRatio S hfineCutoff hcoarseCoupling
        source hsource hpositive event := by
  exact Q'.eqv_trans _ _ _
    (fineCouplingKernelOutputEventMass_eqv_finiteEventMass
      (physicalKernel S hfineCutoff hcoarseCoupling) source event)
    (physicalKernelRowEventMass_eqv_positiveRawRatio
      S hfineCutoff hcoarseCoupling source hsource hpositive event)

/-- **Actual raw response seam.**  For an accepted disconnected source at
positive fine coupling, the support-swap response defect of the production
kernel is exactly a difference of four literal whole-slab raw-event ratios.
The two complete row partitions remain visible inside those ratios. -/
theorem fineCouplingAcceptedSeparated_actualResponseDefect_eqv_rawRatios
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    fineCouplingPhysicalSupportSwapResponseDefect
        (physicalKernel S hfineCutoff hcoarseCoupling)
        event targetFaceId pair ≈
      (positivePhysicalRawEventRatio S hfineCutoff hcoarseCoupling
          source.1.1.1.1 source.1.1.physical_mem
          (fineCouplingAcceptedSeparated_left_physicalTerm_pos
            S hfineCoupling rootFaceId targetFaceId source) event -
        positivePhysicalRawEventRatio S hfineCutoff hcoarseCoupling
          source.1.2.1.1
          (mem_slabExpandedFineSources_iff.mp source.1.2.2).1
          (fineCouplingAcceptedSeparated_right_physicalTerm_pos
            S hfineCoupling rootFaceId targetFaceId source) event) -
      (positivePhysicalRawEventRatio S hfineCutoff hcoarseCoupling
          (slabObservablePairSupportSwitchedLeftPhysical
            S.fine targetFaceId source.1)
          (slabObservablePairedSupportSwitchedLeftPhysical_mem
            S.fine source)
          (fineCouplingAcceptedSeparated_swappedLeft_physicalTerm_pos
            S hfineCoupling rootFaceId targetFaceId htarget source) event -
        positivePhysicalRawEventRatio S hfineCutoff hcoarseCoupling
          (slabObservablePairSupportSwitchedRightPhysical
            S.fine targetFaceId source.1)
          (slabObservablePairedSupportSwitchedRightPhysical_mem
            S.fine source)
          (fineCouplingAcceptedSeparated_swappedRight_physicalTerm_pos
            S hfineCoupling rootFaceId targetFaceId htarget source) event) := by
  dsimp only
  unfold fineCouplingPhysicalSupportSwapResponseDefect
    fineCouplingPhysicalPairEventResponseDifference
  rw [fineCouplingAcceptedSeparated_supportSwapped_left
      S rootFaceId targetFaceId source,
    fineCouplingAcceptedSeparated_supportSwapped_right
      S rootFaceId targetFaceId source]
  apply sub_eqv_both_local
  · exact sub_eqv_both_local
      (fineCouplingPhysicalKernelOutputEventMass_eqv_positiveRawRatio
        S hfineCutoff hcoarseCoupling _ source.1.1.physical_mem
        (fineCouplingAcceptedSeparated_left_physicalTerm_pos
          S hfineCoupling rootFaceId targetFaceId source) event)
      (fineCouplingPhysicalKernelOutputEventMass_eqv_positiveRawRatio
        S hfineCutoff hcoarseCoupling _
        (mem_slabExpandedFineSources_iff.mp source.1.2.2).1
        (fineCouplingAcceptedSeparated_right_physicalTerm_pos
          S hfineCoupling rootFaceId targetFaceId source) event)
  · exact sub_eqv_both_local
      (fineCouplingPhysicalKernelOutputEventMass_eqv_positiveRawRatio
        S hfineCutoff hcoarseCoupling _
        (slabObservablePairedSupportSwitchedLeftPhysical_mem
          S.fine source)
        (fineCouplingAcceptedSeparated_swappedLeft_physicalTerm_pos
          S hfineCoupling rootFaceId targetFaceId htarget source) event)
      (fineCouplingPhysicalKernelOutputEventMass_eqv_positiveRawRatio
        S hfineCutoff hcoarseCoupling _
        (slabObservablePairedSupportSwitchedRightPhysical_mem
          S.fine source)
        (fineCouplingAcceptedSeparated_swappedRight_physicalTerm_pos
          S hfineCoupling rootFaceId targetFaceId htarget source) event)

#print axioms fineCouplingAcceptedSeparatedPhysicalPair
#print axioms fineCouplingAcceptedSeparatedAssignmentPair
#print axioms fineCouplingAcceptedRecoupledPhysicalPair
#print axioms fineCouplingAcceptedRecoupledAssignmentPair
#print axioms fineCouplingAcceptedSeparated_supportSwapped_eq_recoupledPhysical
#print axioms fineCouplingAcceptedSeparated_supportSwapped_left
#print axioms fineCouplingAcceptedSeparated_supportSwapped_right
#print axioms fineCouplingAcceptedRecoupledTargetPair_mem
#print axioms fineCouplingAcceptedSeparatedOccupationResponse_decomposition
#print axioms FineCouplingSupportSwapEventInvariant
#print axioms FineCouplingSupportSwapEventInvariant.pairResponseDifference
#print axioms FineCouplingSupportSwapEventInvariant.responseDefect_eqv_zero
#print axioms fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_responseDefect_eqv_zero
#print axioms fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_eventInvariant
#print axioms slabPhysicalTerm_pos_of_bounded_of_fusionWitness
#print axioms fineCouplingAcceptedSeparated_left_physicalTerm_pos
#print axioms fineCouplingAcceptedSeparated_right_physicalTerm_pos
#print axioms fineCouplingAcceptedSeparated_swappedLeft_physicalTerm_pos
#print axioms fineCouplingAcceptedSeparated_swappedRight_physicalTerm_pos
#print axioms fineCouplingPhysicalKernelOutputEventMass_eqv_positiveRawRatio
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_eqv_rawRatios

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse

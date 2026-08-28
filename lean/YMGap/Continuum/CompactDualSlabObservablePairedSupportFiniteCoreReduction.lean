/-
# The paired connected covariance contracts to one finite-core remainder

The arbitrary-coupling SU(2) switch bounds the signed face covariance by the
normalized mass of the connected two-replica support carrier.  That carrier
is a literal sublist of

  root-positive first replica x arbitrary second replica.

Finite weighted injection and exact Fubini therefore bound its unnormalized
mass by `positiveSourceWeight * physicalPartition`.  Cancelling one positive
partition factor turns the two-replica probability into the one-replica
positive-face probability.

The established high-spin theorem can now be substituted without identifying
the union-support component with a one-replica strand component.  The result
is the explicit arbitrary-coupling covariance bound

  covariance <= 8/17 + 50 * (4/5)^(floor+1)
                + normalizedFiniteCoreRemainder.

Only the last literal term is open.  No smallness, distance decay, completed
operator bound, spacing normalization, or continuum conclusion is asserted.

Constructive contract: finite subcarrier injection, exact rational Fubini,
positive division, and the previously verified SU(2) switch and high-spin
estimates only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservableHighSpinFiniteCoreRemainder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The paired carrier is bounded by one positive marginal -/

/-- The broad product carrier consisting of every root-positive first
replica and every expanded second replica. -/
def slabObservablePositiveTimesAllPairs
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  cartesian
    (slabObservablePositiveSourceEntries D rootFaceId)
    (slabExpandedFineSourceEntries D)

/-- Every paired-support connected source-cell pair lies in the broad
positive-times-all product carrier. -/
theorem slabObservablePairedSupportConnected_mem_positiveTimesAll
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId) :
    pair ∈ slabObservablePositiveTimesAllPairs D rootFaceId := by
  have hconnected := List.mem_filter.mp hpair
  have hsource :=
    (mem_cartesian_iff
      (slabObservableRootTargetEntries
        D rootFaceId targetFaceId)
      (slabObservableRootComplementTargetComplementEntries
        D rootFaceId targetFaceId) pair).mp hconnected.1
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D rootFaceId)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp hsource.1).1,
    (List.mem_filter.mp hsource.2).1⟩

/-- Exact Fubini identifies the broad product mass with the positive first
marginal times the complete physical partition. -/
theorem slabObservablePositiveTimesAllPairs_weight_eqv
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePositiveTimesAllPairs D rootFaceId) ≈
      slabObservablePositiveSourceWeight D rootFaceId *
        D.physicalPartition := by
  have hcart := listQSum_cartesian_product
    (slabObservablePositiveEntryWeight D)
    (slabExpandedFineEntryWeight D)
    (slabObservablePositiveSourceEntries D rootFaceId)
    (slabExpandedFineSourceEntries D)
  have hpositive :
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservablePositiveSourceEntries D rootFaceId) ≈
        slabObservablePositiveSourceWeight D rootFaceId := by
    unfold slabObservablePositiveEntryWeight
      slabObservablePositiveSourceEntries
      slabObservablePositiveSourceWeight
    exact Q'.eqv_of_eq
      (listQSum_attach
        (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D rootFaceId))
  have hpartition := slabExpandedFineSourceEntries_weight_total D
  exact Q'.eqv_trans _ _ _ hcart
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hpositive)
      (Q'.mul_eqv_congr_left _ _ _ hpartition))

/-- The complete connected paired-support residue is no larger than one
positive marginal times the partition.  No geometry or decay is used. -/
theorem slabObservablePairedSupportConnected_weight_le_positiveSourceProduct
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      slabObservablePositiveSourceWeight D rootFaceId *
        D.physicalPartition := by
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) <=
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePositiveTimesAllPairs D rootFaceId) := by
    apply listQSum_le_of_injective
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId)
      (slabObservablePositiveTimesAllPairs D rootFaceId)
      (slabObservableTwoReplicaPairWeight D)
      (slabObservableTwoReplicaPairWeight D)
      (fun pair => pair)
      ((slabObservableFourCellSourcePairs_nodup
        D rootFaceId targetFaceId).filter _)
    · intro pair hpair
      exact slabObservablePairedSupportConnected_mem_positiveTimesAll
        D rootFaceId targetFaceId pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId pair
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (slabObservablePositiveTimesAllPairs_weight_eqv
        D rootFaceId))

/-! ## 2. Cancel the unused replica -/

/-- Dividing the connected two-replica mass by `Z^2` leaves at most the
one-replica positive probability `positiveSourceWeight / Z`. -/
theorem slabObservableNormalizedPairedSupportConnectedMass_le_positiveProbability
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId <=
      Q'.divPos
        (slabObservablePositiveSourceWeight D rootFaceId)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent) := by
  let positive := slabObservablePositiveSourceWeight D rootFaceId
  let partition := D.physicalPartition
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hpartitionSquare : (0 : Q') < partition * partition :=
    YMGap.Continuum.HKPos.q_mul_pos hpartition hpartition
  have hconnected :=
    slabObservablePairedSupportConnected_weight_le_positiveSourceProduct
      D rootFaceId targetFaceId
  have hcancel :
      Q'.divPos positive partition hpartition *
          (partition * partition) ≈
        positive * partition := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.divPos positive partition hpartition)
          partition partition))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.divPos_mul_eqv positive partition hpartition))
  unfold slabObservableNormalizedPairedSupportConnectedMass
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hconnected (Q'.ge_of_eqv hcancel)

/-! ## 3. The sole normalized finite-core remainder -/

/-- The explicit scalar already paid by the exterior and entropy-tail
branches. -/
def slabObservableResolvedPositiveRate (floor : Nat) : Q' :=
  Q'.mkPos 8 17 (by decide) +
    50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)

/-- The first convenient explicit floor at which the already resolved scalar
budget is strictly below one. -/
def slabObservableFiniteCoreStrictFloor : Nat := 20

/-- The exact rational room left for the normalized finite-core remainder at
the displayed floor. -/
def slabObservableFiniteCoreStrictMargin : Q' :=
  (1 : Q') +
    -(slabObservableResolvedPositiveRate
      slabObservableFiniteCoreStrictFloor)

theorem slabObservableResolvedPositiveRate_strictFloor_lt_one :
    slabObservableResolvedPositiveRate
        slabObservableFiniteCoreStrictFloor < (1 : Q') := by
  decide

theorem slabObservableFiniteCoreStrictMargin_pos :
    (0 : Q') < slabObservableFiniteCoreStrictMargin := by
  decide

/-- The only unresolved positive mass, normalized by the same physical
partition that appears in the observable law. -/
def slabObservableNormalizedFiniteCoreRemainder
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (w : Q') (floor : Nat) : Q' :=
  Q'.divPos
    (slabObservableHighSpinFiniteCoreRemainderWeight
      D rootFaceId hroot (anchorPaidExteriorThreshold w) (32 * floor))
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-- The one-replica positive probability is bounded by the explicit resolved
rate plus precisely the normalized finite-core remainder. -/
theorem slabObservablePositiveProbability_le_resolvedRate_add_finiteCoreRemainder
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat) :
    Q'.divPos
        (slabObservablePositiveSourceWeight D rootFaceId)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent) <=
      slabObservableResolvedPositiveRate floor +
        slabObservableNormalizedFiniteCoreRemainder
          D rootFaceId hroot w floor := by
  let q := Q'.mkPos 8 17 (by decide)
  let tail := 50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)
  let remainder := slabObservableHighSpinFiniteCoreRemainderWeight
    D rootFaceId hroot (anchorPaidExteriorThreshold w) (32 * floor)
  let partition := D.physicalPartition
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hsource :=
    slabObservablePositiveSourceWeight_le_resolved_add_finiteCoreRemainder
      hw0 hw1 cutoff half D hD rootFaceId hroot floor
  have hexpand :
      ((q + tail) + Q'.divPos remainder partition hpartition) *
          partition ≈
        q * partition + (tail * partition + remainder) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv
        (q + tail) (Q'.divPos remainder partition hpartition)
        partition) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right
        ((q + tail) * partition)
        (q * partition + tail * partition)
        (Q'.divPos remainder partition hpartition * partition)
        (Q'.add_mul_eqv q tail partition)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (q * partition + tail * partition)
        (Q'.divPos remainder partition hpartition * partition)
        remainder
        (Q'.divPos_mul_eqv remainder partition hpartition)) ?_
    exact Q'.add_assoc_eqv
      (q * partition) (tail * partition) remainder
  unfold slabObservableResolvedPositiveRate
    slabObservableNormalizedFiniteCoreRemainder
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hsource (Q'.ge_of_eqv hexpand)

/-! ## 4. Signed covariance contraction -/

/-- **Arbitrary-coupling finite-core covariance reduction.**  Every resolved
piece has been contracted to an explicit scalar.  Proving a strict covariance
bound now requires only a bound on the displayed normalized finite-core
remainder. -/
theorem slabObservableFaceBooleanCovariance_le_resolvedRate_add_finiteCoreRemainder
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (rootFaceId targetFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat) :
    slabObservableFaceBooleanCovariance
        D rootFaceId targetFaceId <=
      slabObservableResolvedPositiveRate floor +
        slabObservableNormalizedFiniteCoreRemainder
          D rootFaceId hroot w floor := by
  exact Q'.le_trans' _ _ _
    (slabObservableFaceBooleanCovariance_le_pairedSupportConnectedMass
      D rootFaceId targetFaceId htarget)
    (Q'.le_trans' _ _ _
      (slabObservableNormalizedPairedSupportConnectedMass_le_positiveProbability
        D rootFaceId targetFaceId)
      (slabObservablePositiveProbability_le_resolvedRate_add_finiteCoreRemainder
        hw0 hw1 cutoff half D hD rootFaceId hroot floor))

#print axioms slabObservablePositiveTimesAllPairs
#print axioms slabObservablePairedSupportConnected_mem_positiveTimesAll
#print axioms slabObservablePositiveTimesAllPairs_weight_eqv
#print axioms slabObservablePairedSupportConnected_weight_le_positiveSourceProduct
#print axioms slabObservableNormalizedPairedSupportConnectedMass_le_positiveProbability
#print axioms slabObservableResolvedPositiveRate
#print axioms slabObservableFiniteCoreStrictFloor
#print axioms slabObservableFiniteCoreStrictMargin
#print axioms slabObservableResolvedPositiveRate_strictFloor_lt_one
#print axioms slabObservableFiniteCoreStrictMargin_pos
#print axioms slabObservableNormalizedFiniteCoreRemainder
#print axioms slabObservablePositiveProbability_le_resolvedRate_add_finiteCoreRemainder
#print axioms slabObservableFaceBooleanCovariance_le_resolvedRate_add_finiteCoreRemainder

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction

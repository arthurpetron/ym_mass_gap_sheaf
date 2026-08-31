/-
# Accepted backgrounds partition into guarded observable rows

The complete accepted two-replica carrier is partitioned by the literal
guarded graft it produces.  One concrete representative is retained for each
realized guarded row.  The already proved peeling and insertion payments pay
the complete inverse fiber into that representative's physical Gibbs weight
times its successful connected-row mass.

Multiplying by the fixed provenance scale and summing the exact representative
fibers produces a cutoff-independent positive candidate rate against the full
two-replica partition.  This module stops before transporting the representative
rows through the final receiver columns; that is the next finite composition.

Constructive contract: structural finite key representatives, exact `Q'`
weights, and previously proved payments only.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.FiniteKeyRepresentativePartition
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedRowCarrier
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionFiber

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedRowPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedRowCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private def expandedEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  expandedEntryDecidableEq D

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

private theorem scale_product_bound
    (scale rate sourceMass sourceWeight rowMass : Q')
    (scale_nonnegative : (0 : Q') ≤ scale)
    (hbound : rate * sourceMass ≤ sourceWeight * rowMass) :
    (scale * rate) * sourceMass ≤
      sourceWeight * (scale * rowMass) := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ scale hbound
    scale_nonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv scale rate sourceMass))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv scale sourceWeight rowMass))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ rowMass
              (Q'.mul_comm_eqv scale sourceWeight))
            (Q'.mul_assoc_eqv sourceWeight scale rowMass)))))

private theorem anchorDataExtentFive (cutoff : Nat) :
    (anchorSlabPhysicalData cutoff 2).extent = 5 := rfl

/-! ## 1. One fixed positive rate -/

/-- The provenance scale times the already constructed three-payment
separated-transition rate.  Neither factor depends on the representation
cutoff. -/
def reflectedBentGuardScaledSeparatedTransitionRate : Q' :=
  reflectedBentGuardConnectedRowScale *
    reflectedBentGuardSeparatedTransitionRate
      anchorCoupling reflectedBentPatternGuardFaceIds

theorem reflectedBentGuardScaledSeparatedTransitionRate_pos :
    (0 : Q') < reflectedBentGuardScaledSeparatedTransitionRate := by
  unfold reflectedBentGuardScaledSeparatedTransitionRate
    reflectedBentGuardConnectedRowScale
  exact Q'.mul_pos
    (Q'.invSucc_pos reflectedBentGuardProvenanceCodeSpace.length)
    (reflectedBentGuardSeparatedTransitionRate_pos
      anchorCoupling (by decide) reflectedBentPatternGuardFaceIds)

/-! ## 2. Exact realized-row representatives -/

/-- The accepted guarded graft used as the row key of one background. -/
def reflectedBentGuardAcceptedRowKey
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (state : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)) :
    SlabAcceptedTwoReplicaState (anchorSlabPhysicalData cutoff 2) :=
  reflectedBentGuardGraftAcceptedStateOfOneLE
    (anchorSlabPhysicalData cutoff 2) hcutoff
      (anchorDataExtentFive cutoff) state

/-- One actual accepted background for every guarded row realized by the
complete accepted-state carrier. -/
def reflectedBentGuardAcceptedRowRepresentatives
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)) :=
  keyRepresentatives
    (reflectedBentGuardAcceptedRowKey cutoff hcutoff)
    (slabAcceptedTwoReplicaStates (anchorSlabPhysicalData cutoff 2))

/-- The complete accepted-background fiber producing the same guarded row as
one representative. -/
def reflectedBentGuardAcceptedRowFiber
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (representative : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)) :
    List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)) :=
  representativeFiber
    (slabAcceptedTwoReplicaStates (anchorSlabPhysicalData cutoff 2))
    (reflectedBentGuardAcceptedRowKey cutoff hcutoff)
    representative

theorem reflectedBentGuardAcceptedRowFiber_nodup
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (representative : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)) :
    (reflectedBentGuardAcceptedRowFiber
      cutoff hcutoff representative).Nodup := by
  unfold reflectedBentGuardAcceptedRowFiber representativeFiber
  exact List.filter_sublist.nodup
    (slabAcceptedTwoReplicaStates_nodup
      (anchorSlabPhysicalData cutoff 2))

/-! ## 3. Pay each complete row fiber -/

/-- The scaled separated-transition rate pays every complete accepted-state
row fiber into its representative's Gibbs weight times the scaled successful
row mass. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_mul_rowFiberWeight_le
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (representative : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)) :
    reflectedBentGuardScaledSeparatedTransitionRate *
        listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2)
          (reflectedBentGuardAcceptedRowFiber
            cutoff hcutoff representative) ≤
      slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff 2)
          (reflectedBentGuardGraftObservableSourcePairAtCutoff
            (anchorSlabPhysicalData cutoff 2) hcutoff
              (anchorDataExtentFive cutoff) representative) *
        reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) representative := by
  let D := anchorSlabPhysicalData cutoff 2
  let fiber := reflectedBentGuardAcceptedRowFiber
    cutoff hcutoff representative
  let rowMass := listQSum
    (slabObservablePairedConnectedStrandWeight D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff (anchorDataExtentFive cutoff) representative))
    (slabObservablePairedConnectedStrandChoices D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff (anchorDataExtentFive cutoff) representative))
  have hfiber :=
    reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_joint
      cutoff hcutoff fiber
      (reflectedBentGuardAcceptedRowFiber_nodup
        cutoff hcutoff representative)
      representative
      (fun source hsource => by
        have hparts := List.mem_filter.mp hsource
        exact (of_decide_eq_true hparts.2).symm)
      rowMass
      (reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_quarter
        D hcutoff (anchorDataExtentFive cutoff) representative)
  exact scale_product_bound
    reflectedBentGuardConnectedRowScale
    (reflectedBentGuardSeparatedTransitionRate
      anchorCoupling reflectedBentPatternGuardFaceIds)
    (listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) fiber)
    (slabObservableTwoReplicaPairWeight D
      (reflectedBentGuardGraftObservableSourcePairAtCutoff
        D hcutoff (anchorDataExtentFive cutoff) representative))
    rowMass
    (Q'.invSucc_nonneg reflectedBentGuardProvenanceCodeSpace.length)
    (by simpa only [D] using hfiber)

/-! ## 4. Sum the exact partition -/

/-- **Accepted-state row partition bound.**  The fixed positive rate times the
complete two-replica Gibbs mass is bounded by the sum of the scaled successful
guarded rows indexed by one representative per realized row. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_mul_acceptedWeight_le_rows
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    reflectedBentGuardScaledSeparatedTransitionRate *
        listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2)
          (slabAcceptedTwoReplicaStates
            (anchorSlabPhysicalData cutoff 2)) ≤
      listQSum
        (fun representative =>
          slabObservableTwoReplicaPairWeight
              (anchorSlabPhysicalData cutoff 2)
              (reflectedBentGuardGraftObservableSourcePairAtCutoff
                (anchorSlabPhysicalData cutoff 2) hcutoff
                  (anchorDataExtentFive cutoff) representative) *
            reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
              (anchorSlabPhysicalData cutoff 2) hcutoff
                (anchorDataExtentFive cutoff) representative)
        (reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff) := by
  let states := slabAcceptedTwoReplicaStates
    (anchorSlabPhysicalData cutoff 2)
  let representatives :=
    reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff
  let fiberMass := fun representative =>
    listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2)
      (reflectedBentGuardAcceptedRowFiber cutoff hcutoff representative)
  have hpartition : listQSum fiberMass representatives ≈
      listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) states := by
    exact keyRepresentativeFibers_weight_total
      states (slabAcceptedTwoReplicaStateWeight cutoff 2)
      (reflectedBentGuardAcceptedRowKey cutoff hcutoff)
  have hrecode :
      reflectedBentGuardScaledSeparatedTransitionRate *
          listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) states ≈
        listQSum
          (fun representative =>
            reflectedBentGuardScaledSeparatedTransitionRate *
              fiberMass representative)
          representatives :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left reflectedBentGuardScaledSeparatedTransitionRate
        _ _ (Q'.eqv_symm hpartition))
      (Q'.eqv_symm
        (listQSum_mul_left
          reflectedBentGuardScaledSeparatedTransitionRate
          fiberMass representatives))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrecode)
    (listQSum_le_termwise_local _ _ representatives
      (fun representative _ =>
        reflectedBentGuardScaledSeparatedTransitionRate_mul_rowFiberWeight_le
          cutoff hcutoff representative))

/-- The same bound with the complete accepted-state sum identified as the
square of the corrected-slab physical partition. -/
theorem reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_rows
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff) :
    reflectedBentGuardScaledSeparatedTransitionRate *
        ((anchorSlabPhysicalData cutoff 2).physicalPartition *
          (anchorSlabPhysicalData cutoff 2).physicalPartition) ≤
      listQSum
        (fun representative =>
          slabObservableTwoReplicaPairWeight
              (anchorSlabPhysicalData cutoff 2)
              (reflectedBentGuardGraftObservableSourcePairAtCutoff
                (anchorSlabPhysicalData cutoff 2) hcutoff
                  (anchorDataExtentFive cutoff) representative) *
            reflectedBentGuardGraftConnectedScaledRowMassAtCutoff
              (anchorSlabPhysicalData cutoff 2) hcutoff
                (anchorDataExtentFive cutoff) representative)
        (reflectedBentGuardAcceptedRowRepresentatives cutoff hcutoff) := by
  have htotal := slabAcceptedTwoReplicaStates_weight_total cutoff 2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left reflectedBentGuardScaledSeparatedTransitionRate
        _ _ (Q'.eqv_symm htotal)))
    (reflectedBentGuardScaledSeparatedTransitionRate_mul_acceptedWeight_le_rows
      cutoff hcutoff)

#print axioms reflectedBentGuardScaledSeparatedTransitionRate
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_pos
#print axioms reflectedBentGuardAcceptedRowRepresentatives
#print axioms reflectedBentGuardAcceptedRowFiber_nodup
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_mul_rowFiberWeight_le
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_mul_acceptedWeight_le_rows
#print axioms reflectedBentGuardScaledSeparatedTransitionRate_mul_partition_sq_le_rows

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedRowPartition

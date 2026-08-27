/-
# Terminal/mass partition of the global paired connected residue

The global fixed-fiber estimate is useful only if the actual connected source
sector can be partitioned without paying for the number of terminals.  This
module performs that finite Fubini step literally.

Each connected attached source is sent to its deterministic canonical output

  (paid trace mass, terminal accepted pair).

The paid mass lies between observable separation plus one and the explicit
two-replica physical ceiling.  The terminal lies in the Cartesian terminal
carrier.  Exact deterministic fiber summation, followed by the proved
`(16/25)^M` bound on each fiber, gives

  connectedWeight <=
    (sum_{M >= separation+1} (16/25)^M) * partition^2.

No terminal-count or volume prefactor is introduced.

Constructive contract: finite filters, Cartesian products, exact deterministic
fibers, and rational order only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Proof-carrying connected source entries -/

private theorem attach_filter_map_val
    {A : Type} (items : List A) (test : A → Bool) :
    (items.attach.filter (fun item => test item.1)).map Subtype.val =
      items.filter test := by
  change (items.attach.filter (test ∘ Subtype.val)).map Subtype.val = _
  rw [← List.filter_map, List.attach_map_subtype_val]

/-- The actual connected source list, now carrying unfiltered four-cell
membership proofs. -/
def slabObservablePairedSupportConnectedFourCellSourceEntries
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableFourCellPairEntry D rootFaceId targetFaceId) :=
  (slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId).attach.filter fun source =>
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source.1

theorem slabObservablePairedSupportConnectedFourCellSourceEntries_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservablePairedSupportConnectedFourCellSourceEntries
      D rootFaceId targetFaceId).Nodup := by
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (slabObservableFourCellSourcePairs_nodup
        D rootFaceId targetFaceId))

theorem slabObservablePairedSupportConnectedEntry_connected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (hsource : source ∈
      slabObservablePairedSupportConnectedFourCellSourceEntries
        D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source.1 = true := by
  exact (List.mem_filter.mp hsource).2

/-- Passing through proof-carrying attached entries preserves the literal
connected residue weight. -/
theorem slabObservablePairedSupportConnectedFourCellSourceEntries_weight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId) =
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) := by
  have hmap :
      (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId).map Subtype.val =
        slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId := by
    unfold slabObservablePairedSupportConnectedFourCellSourceEntries
      slabObservablePairedSupportConnectedFourCellSourcePairs
    exact attach_filter_map_val
      (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
      (fun pair => slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair)
  calc
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId) =
      listQSum (slabObservableTwoReplicaPairWeight D)
        ((slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId).map Subtype.val) :=
            (listQSum_map _ _ _).symm
    _ = listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) := congrArg _ hmap

/-! ## 2. Deterministic terminal/mass keys -/

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

/-- The exact paid mass and terminal produced by one source entry. -/
def slabObservablePairTargetSupportCanonicalPeelingKey
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) :
    Nat × SlabAcceptedTwoReplicaState D :=
  let output := slabObservablePairTargetSupportCanonicalPeeling
    D rootFaceId targetFaceId htarget source.1 source.2
  (slabAcceptedPairedPeelTraceMass output.2, output.1)

/-- Only masses above the observable floor and below the literal paired
physical ceiling. -/
def slabObservablePairedSupportPaidMasses
    (D : SlabPhysicalData) (floor : Nat) : List Nat :=
  (List.range (2 * slabObservableRemovalMaxSize D + 1)).filter
    fun mass => decide (floor ≤ mass)

/-- Rectangular carrier of every admissible paid mass and every literal
accepted terminal. -/
def slabObservablePairedSupportCanonicalPeelingKeyCarrier
    (D : SlabPhysicalData) (floor : Nat) :
    List (Nat × SlabAcceptedTwoReplicaState D) :=
  cartesian (slabObservablePairedSupportPaidMasses D floor)
    (slabAcceptedTwoReplicaStates D)

private theorem range_nodup : ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count :=
              List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

theorem slabObservablePairedSupportCanonicalPeelingKeyCarrier_nodup
    (D : SlabPhysicalData) (floor : Nat) :
    (slabObservablePairedSupportCanonicalPeelingKeyCarrier
      D floor).Nodup := by
  apply cartesian_nodup
  · exact List.filter_sublist.nodup (range_nodup _)
  · exact slabAcceptedTwoReplicaStates_nodup D

theorem slabObservablePairTargetSupportCanonicalPeelingKey_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId floor : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (hconnectedFloor : floor ≤
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2) :
    slabObservablePairTargetSupportCanonicalPeelingKey
        D rootFaceId targetFaceId htarget source ∈
      slabObservablePairedSupportCanonicalPeelingKeyCarrier D floor := by
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      exact Nat.lt_succ_of_le
        (slabAcceptedPairCanonicalPeeling_traceMass_le
          D
          (slabTwoReplicaTargetSupportComponent D.extent
            source.1.1.1.1 source.1.2.1.1 targetFaceId)
          (fun faceId hface =>
            slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
              D rootFaceId targetFaceId htarget source.1 source.2
                faceId hface)
          (slabObservableTwoReplicaPairToAcceptedState source.1))
    · exact decide_eq_true hconnectedFloor
  · exact slabAcceptedTwoReplicaState_mem D
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget source.1 source.2).1

/-! ## 3. Exact partition and fixed-key estimate -/

private theorem listQSum_le_termwise
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
    listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-- One deterministic terminal/mass fiber obeys the global `(16/25)^M`
bound. -/
theorem slabObservablePairedSupportCanonicalPeeling_fiberWeight_le
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (anchorSlabPhysicalData cutoff half).extent)
    (key : Nat × SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)) :
    fiberWeight
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff half) source.1)
        (slabObservablePairTargetSupportCanonicalPeelingKey
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId htarget)
        key ≤
      slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
        slabAcceptedTwoReplicaStateWeight cutoff half key.2 := by
  unfold fiberWeight
  apply
    slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_weight_sum_le
      cutoff half rootFaceId targetFaceId key.1 htarget key.2
  · exact List.filter_sublist.nodup
      (slabObservablePairedSupportConnectedFourCellSourceEntries_nodup
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId)
  · intro source hsource
    have hkey := of_decide_eq_true (List.mem_filter.mp hsource).2
    exact (congrArg Prod.snd hkey).symm
  · intro source hsource
    have hkey := of_decide_eq_true (List.mem_filter.mp hsource).2
    exact (congrArg Prod.fst hkey).symm

/-- Exact finite Fubini over all admissible terminal/mass keys. -/
theorem slabObservablePairedSupportCanonicalPeeling_fiberWeight_total
    (D : SlabPhysicalData) (rootFaceId targetFaceId floor : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (hfloor : ∀ source, source ∈
        slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId →
      floor ≤ slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2) :
    listQSum
        (fiberWeight
          (slabObservablePairedSupportConnectedFourCellSourceEntries
            D rootFaceId targetFaceId)
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          (slabObservablePairTargetSupportCanonicalPeelingKey
            D rootFaceId targetFaceId htarget))
        (slabObservablePairedSupportCanonicalPeelingKeyCarrier
          D floor) ≈
      listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId) := by
  exact fiberWeight_total
    (slabObservablePairedSupportConnectedFourCellSourceEntries
      D rootFaceId targetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    (slabObservablePairTargetSupportCanonicalPeelingKey
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedSupportCanonicalPeelingKeyCarrier D floor)
    (slabObservablePairedSupportCanonicalPeelingKeyCarrier_nodup D floor)
    (fun source hsource =>
      slabObservablePairTargetSupportCanonicalPeelingKey_mem
        D rootFaceId targetFaceId floor htarget source
          (hfloor source hsource))

/-! ## 4. Sum every key without a terminal-count prefactor -/

/-- The actual connected residue is bounded by a finite geometric paid-mass
sum times the square of the genuine slab partition. -/
theorem slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (anchorSlabPhysicalData cutoff half).extent) :
    let D := anchorSlabPhysicalData cutoff half
    let floor := linfDist
      (slabPlaquetteAt D.extent rootFaceId)
      (slabPlaquetteAt D.extent targetFaceId) + 1
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum
          (fun mass =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
          (slabObservablePairedSupportPaidMasses D floor) *
        (D.physicalPartition * D.physicalPartition) := by
  let D := anchorSlabPhysicalData cutoff half
  let floor := linfDist
    (slabPlaquetteAt D.extent rootFaceId)
    (slabPlaquetteAt D.extent targetFaceId) + 1
  have hfloor : ∀ source, source ∈
        slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId →
      floor ≤ slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 := by
    intro source hsource
    exact
      slabObservablePairTargetSupportCanonicalPeeling_traceMass_floor
        D rootFaceId targetFaceId htarget source.1 source.2
          (slabObservablePairedSupportConnectedEntry_connected
            D rootFaceId targetFaceId source hsource)
  have hpartition :=
    slabObservablePairedSupportCanonicalPeeling_fiberWeight_total
      D rootFaceId targetFaceId floor htarget hfloor
  have hfibers :
      listQSum
          (fiberWeight
            (slabObservablePairedSupportConnectedFourCellSourceEntries
              D rootFaceId targetFaceId)
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            (slabObservablePairTargetSupportCanonicalPeelingKey
              D rootFaceId targetFaceId htarget))
          (slabObservablePairedSupportCanonicalPeelingKeyCarrier
            D floor) ≤
        listQSum
          (fun key =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
              slabAcceptedTwoReplicaStateWeight cutoff half key.2)
          (slabObservablePairedSupportCanonicalPeelingKeyCarrier
            D floor) := by
    apply listQSum_le_termwise
    intro key _
    exact
      slabObservablePairedSupportCanonicalPeeling_fiberWeight_le
        cutoff half rootFaceId targetFaceId htarget key
  have hcart := listQSum_cartesian_product
    (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
    (slabAcceptedTwoReplicaStateWeight cutoff half)
    (slabObservablePairedSupportPaidMasses D floor)
    (slabAcceptedTwoReplicaStates D)
  have hterminals := slabAcceptedTwoReplicaStates_weight_total cutoff half
  have hentries :=
    slabObservablePairedSupportConnectedFourCellSourceEntries_weight
      D rootFaceId targetFaceId
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq hentries.symm) (Q'.eqv_symm hpartition))) ?_
  refine Q'.le_trans' _ _ _ hfibers ?_
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _
    (listQSum
        (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
        (slabObservablePairedSupportPaidMasses D floor) *
      listQSum (slabAcceptedTwoReplicaStateWeight cutoff half)
        (slabAcceptedTwoReplicaStates D)) _ ?_ ?_
  · simpa only [slabObservablePairedSupportCanonicalPeelingKeyCarrier]
      using hcart
  · exact Q'.mul_eqv_congr_left _ _ _ hterminals

#print axioms slabObservablePairedSupportConnectedFourCellSourceEntries
#print axioms slabObservablePairedSupportConnectedFourCellSourceEntries_nodup
#print axioms slabObservablePairedSupportConnectedFourCellSourceEntries_weight
#print axioms slabObservablePairTargetSupportCanonicalPeelingKey
#print axioms slabObservablePairedSupportCanonicalPeelingKeyCarrier
#print axioms slabObservablePairTargetSupportCanonicalPeelingKey_mem
#print axioms slabObservablePairedSupportCanonicalPeeling_fiberWeight_le
#print axioms slabObservablePairedSupportCanonicalPeeling_fiberWeight_total
#print axioms slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition

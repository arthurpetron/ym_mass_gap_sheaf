/-
# Weighted provenance fibers for guarded connected preimages

Package those connected final-target preimages whose intermediate successful
switchable pair has the two physical fields of a reflected guard graft.
Within one provenance-code fiber, the guarded receiver decoder identifies all
intermediate recoupled pairs.  The generic coherent-subfamily theorem then
places the entire fiber in one bistochastic physical column and bounds its
local recoupling weight by one.

Summing the code fibers gives the fixed unscaled capacity

`2 ^ |pattern faces| * 4096 ^ pattern physical mass`,

and scaling by the reciprocal of one more than that carrier length gives unit
capacity.  This theorem concerns an arbitrary duplicate-free finite list of
guarded preimages at one final receiver.  A later row-level compiler must
construct the guarded preimage list uniformly and preserve the literal
quarter event.

Constructive contract: proof-carrying subtypes, finite code fibers, the proved
guard decoder, and bistochastic column normalization only.  No `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedCoherentSubfamilyCapacity
import YMGap.Continuum.FiniteCodeFiberScaledCapacity
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardReceiverFiberCapacity

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedCodeFiberCapacity

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedCoherentSubfamilyCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder.SlabObservablePairedFaceSwitchDecoderCertificate
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteCodeFiberScaledCapacity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAuxiliaryCodeCapacity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardProvenanceDecoder
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardReceiverFiberCapacity

local infix:50 " ≈ " => Q'.eqv

local instance reflectedBentGuardConnectedTargetPairDecidableEq
    (D : SlabPhysicalData) :
    DecidableEq (SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D reflectedBentRootFaceId

def reflectedBentGuardConnectedTargetFace_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5) :
    reflectedBentTargetFaceId ∈ slabPhysicalFaceEdges D.extent := by
  simpa only [hextent] using reflectedBentTargetFaceId_physical

/-- One final-target preimage whose intermediate switchable source has guarded
left and right physical fields.  The background witness is proposition-only,
so it does not create duplicate data. -/
abbrev ReflectedBentGuardConnectedTargetPreimage
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :=
  { item : SlabObservablePairedConnectedStrandTargetPreimage
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentGuardConnectedTargetFace_mem D hextent) target //
    ∃ state : SlabAcceptedTwoReplicaState D,
      (slabObservablePairedStrandSuccessfulSwitchablePair
        item.1.1.toRecouplingSource item.1.2).pair.1.1.1 =
          reflectedBentGuardGraftLeftPhysical D hextent state ∧
      (slabObservablePairedStrandSuccessfulSwitchablePair
        item.1.1.toRecouplingSource item.1.2).pair.2.1.1 =
          reflectedBentGuardGraftRightPhysical D hextent state }

def reflectedBentGuardConnectedTargetPreimageSwitchableSource
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    {target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId}
    (item : ReflectedBentGuardConnectedTargetPreimage D hextent target) :
    ReflectedBentGuardSwitchableSource D hextent :=
  ⟨slabObservablePairedStrandSuccessfulSwitchablePair
      item.1.1.1.toRecouplingSource item.1.1.2,
    item.2⟩

def reflectedBentGuardConnectedTargetPreimageCode
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    {target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId}
    (item : ReflectedBentGuardConnectedTargetPreimage D hextent target) :
    ReflectedBentGuardProvenanceCode :=
  reflectedBentGuardSwitchableSourceCode D
    (reflectedBentGuardConnectedTargetPreimageSwitchableSource D item)

def reflectedBentGuardConnectedTargetPreimageWeight
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    {target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId}
    (item : ReflectedBentGuardConnectedTargetPreimage D hextent target) : Q' :=
  slabObservablePairedConnectedStrandSourceChoiceWeight
    D reflectedBentRootFaceId reflectedBentTargetFaceId item.1.1

def reflectedBentGuardConnectedTargetPreimageCodeFiber
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    {target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId}
    (items : List (ReflectedBentGuardConnectedTargetPreimage
      D hextent target))
    (key : ReflectedBentGuardProvenanceCode) :
    List (ReflectedBentGuardConnectedTargetPreimage D hextent target) :=
  codeFiber items (reflectedBentGuardConnectedTargetPreimageCode D) key

theorem reflectedBentGuardConnectedTargetPreimageCode_mem_codeSpace
    (D : SlabPhysicalData) {hextent : D.extent = 5}
    {target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId}
    (item : ReflectedBentGuardConnectedTargetPreimage D hextent target) :
    reflectedBentGuardConnectedTargetPreimageCode D item ∈
      reflectedBentGuardProvenanceCodeSpace :=
  reflectedBentGuardSwitchableReceiverFiberCode_mem_codeSpace
    D hextent
      (reflectedBentGuardConnectedTargetPreimageSwitchableSource D item)

/-- Equal codes at the already-fixed final receiver identify the intermediate
recoupled pair. -/
theorem reflectedBentGuardConnectedTargetPreimage_intermediatePair_eq_of_code_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (first second : ReflectedBentGuardConnectedTargetPreimage
      D hextent target)
    (hcode : reflectedBentGuardConnectedTargetPreimageCode D first =
      reflectedBentGuardConnectedTargetPreimageCode D second) :
    slabObservablePairedConnectedPreimageIntermediatePair
        D reflectedBentRootFaceId reflectedBentTargetFaceId first.1 =
      slabObservablePairedConnectedPreimageIntermediatePair
        D reflectedBentRootFaceId reflectedBentTargetFaceId second.1 := by
  let firstSource :=
    reflectedBentGuardConnectedTargetPreimageSwitchableSource D first
  let secondSource :=
    reflectedBentGuardConnectedTargetPreimageSwitchableSource D second
  have hfirstTarget : target =
      reflectedBentGuardSwitchableSourceTarget D hextent firstSource := by
    exact first.1.target_eq.trans (by
      simpa only [firstSource,
          reflectedBentGuardConnectedTargetPreimageSwitchableSource,
          reflectedBentGuardSwitchableSourceTarget] using
        (slabObservablePairedStrandRecoupledTargetPair_eq_direct
          (reflectedBentGuardConnectedTargetFace_mem D hextent)
          first.1.1.1.toRecouplingSource first.1.1.2))
  have hsecondTarget : target =
      reflectedBentGuardSwitchableSourceTarget D hextent secondSource := by
    exact second.1.target_eq.trans (by
      simpa only [secondSource,
          reflectedBentGuardConnectedTargetPreimageSwitchableSource,
          reflectedBentGuardSwitchableSourceTarget] using
        (slabObservablePairedStrandRecoupledTargetPair_eq_direct
          (reflectedBentGuardConnectedTargetFace_mem D hextent)
          second.1.1.1.toRecouplingSource second.1.1.2))
  have hfirstMem : firstSource ∈
      reflectedBentGuardSwitchableReceiverFiber
        D hextent [firstSource, secondSource] target :=
    (mem_reflectedBentGuardSwitchableReceiverFiber_iff
      D hextent [firstSource, secondSource] target firstSource).mpr
        ⟨List.mem_cons_self, hfirstTarget⟩
  have hsecondMem : secondSource ∈
      reflectedBentGuardSwitchableReceiverFiber
        D hextent [firstSource, secondSource] target :=
    (mem_reflectedBentGuardSwitchableReceiverFiber_iff
      D hextent [firstSource, secondSource] target secondSource).mpr
        ⟨List.mem_cons_of_mem firstSource List.mem_cons_self,
          hsecondTarget⟩
  have hsources : firstSource = secondSource :=
    reflectedBentGuardSwitchableSource_eq_of_mem_receiverFiber_of_code_eq
      D hextent [firstSource, secondSource] target
      firstSource secondSource hfirstMem hsecondMem (by
        simpa only [firstSource, secondSource,
          reflectedBentGuardConnectedTargetPreimageCode] using hcode)
  simpa only [slabObservablePairedConnectedPreimageIntermediatePair,
      firstSource, secondSource,
      reflectedBentGuardConnectedTargetPreimageSwitchableSource,
      slabObservablePairedStrandSuccessfulSwitchablePair] using
    congrArg (fun source : ReflectedBentGuardSwitchableSource D hextent =>
      source.1.pair) hsources

private theorem nodup_map_subtype_val_local {A : Type} {p : A → Prop} :
    ∀ items : List {item : A // p item}, items.Nodup →
      (items.map Subtype.val).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        apply hparts.1
        have hsame : item = head := Subtype.ext heq
        exact hsame ▸ hitem
      · exact nodup_map_subtype_val_local tail hparts.2

/-- Every fixed provenance-code fiber occupies one common bistochastic
physical column and hence has total local weight at most one. -/
theorem reflectedBentGuardConnectedTargetPreimageCodeFiber_sum_le_one
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (items : List (ReflectedBentGuardConnectedTargetPreimage
      D hextent target))
    (hitems : items.Nodup)
    (key : ReflectedBentGuardProvenanceCode) :
    listQSum
        (reflectedBentGuardConnectedTargetPreimageWeight D)
        (reflectedBentGuardConnectedTargetPreimageCodeFiber
          D items key) ≤ (1 : Q') := by
  let fiber := reflectedBentGuardConnectedTargetPreimageCodeFiber D items key
  have hfiberNodup : fiber.Nodup := by
    unfold fiber reflectedBentGuardConnectedTargetPreimageCodeFiber
    exact List.filter_sublist.nodup hitems
  cases hfiber : fiber with
  | nil =>
      rw [show reflectedBentGuardConnectedTargetPreimageCodeFiber
          D items key = [] by simpa only [fiber] using hfiber]
      exact Q'.zero_le_one
  | cons anchor rest =>
      let ordinary := (anchor :: rest).map Subtype.val
      have ordinaryNodup : ordinary.Nodup := by
        apply nodup_map_subtype_val_local
        simpa only [hfiber] using hfiberNodup
      have hpairs : ∀ item, item ∈ ordinary →
          slabObservablePairedConnectedPreimageIntermediatePair
              D reflectedBentRootFaceId reflectedBentTargetFaceId item =
            slabObservablePairedConnectedPreimageIntermediatePair
              D reflectedBentRootFaceId reflectedBentTargetFaceId anchor.1 := by
        intro item hitem
        obtain ⟨guarded, hguarded, rfl⟩ := List.mem_map.mp hitem
        have hguardedFiber : guarded ∈
            reflectedBentGuardConnectedTargetPreimageCodeFiber
              D items key := by
          rw [show reflectedBentGuardConnectedTargetPreimageCodeFiber
              D items key = anchor :: rest by
                simpa only [fiber] using hfiber]
          exact hguarded
        have hanchorFiber : anchor ∈
            reflectedBentGuardConnectedTargetPreimageCodeFiber
              D items key := by
          rw [show reflectedBentGuardConnectedTargetPreimageCodeFiber
              D items key = anchor :: rest by
                simpa only [fiber] using hfiber]
          exact List.mem_cons_self
        have hguardedCode :=
          (mem_codeFiber_iff items
            (reflectedBentGuardConnectedTargetPreimageCode D)
            key guarded).mp hguardedFiber |>.2
        have hanchorCode :=
          (mem_codeFiber_iff items
            (reflectedBentGuardConnectedTargetPreimageCode D)
            key anchor).mp hanchorFiber |>.2
        exact
          reflectedBentGuardConnectedTargetPreimage_intermediatePair_eq_of_code_eq
            D hextent target guarded anchor
              (hguardedCode.symm.trans hanchorCode)
      have hcommon :=
        slabObservablePairedConnectedCoherentSubfamilySum_le_one
          D reflectedBentRootFaceId reflectedBentTargetFaceId
          ordinary ordinaryNodup anchor.1 hpairs
      rw [show reflectedBentGuardConnectedTargetPreimageCodeFiber
          D items key = anchor :: rest by
            simpa only [fiber] using hfiber]
      simpa only [reflectedBentGuardConnectedTargetPreimageWeight,
          ordinary, listQSum_map] using hcommon

/-- The unscaled guarded preimage family has capacity bounded by the exact
fixed provenance carrier length. -/
theorem reflectedBentGuardConnectedTargetPreimages_sum_le_codeSpace_length
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (items : List (ReflectedBentGuardConnectedTargetPreimage
      D hextent target))
    (hitems : items.Nodup) :
    listQSum
        (reflectedBentGuardConnectedTargetPreimageWeight D) items ≤
      Q'.ofNat reflectedBentGuardProvenanceCodeSpace.length := by
  exact listQSum_le_codeSpace_length
    items (reflectedBentGuardConnectedTargetPreimageWeight D)
    (reflectedBentGuardConnectedTargetPreimageCode D)
    reflectedBentGuardProvenanceCodeSpace
    (fun item _ =>
      reflectedBentGuardConnectedTargetPreimageCode_mem_codeSpace D item)
    (fun key _ =>
      reflectedBentGuardConnectedTargetPreimageCodeFiber_sum_le_one
        D hextent target items hitems key)

/-- Scaling all guarded preimages by the reciprocal of one more than the fixed
provenance carrier length yields unit receiver capacity. -/
theorem reflectedBentGuardConnectedTargetPreimages_scaled_sum_le_one
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (items : List (ReflectedBentGuardConnectedTargetPreimage
      D hextent target))
    (hitems : items.Nodup) :
    listQSum
        (fun item => Q'.invSucc
            reflectedBentGuardProvenanceCodeSpace.length *
          reflectedBentGuardConnectedTargetPreimageWeight D item)
        items ≤ (1 : Q') := by
  exact listQSum_invSucc_codeSpace_length_mul_le_one
    items (reflectedBentGuardConnectedTargetPreimageWeight D)
    (reflectedBentGuardConnectedTargetPreimageCode D)
    reflectedBentGuardProvenanceCodeSpace
    (fun item _ =>
      reflectedBentGuardConnectedTargetPreimageCode_mem_codeSpace D item)
    (fun key _ =>
      reflectedBentGuardConnectedTargetPreimageCodeFiber_sum_le_one
        D hextent target items hitems key)

theorem reflectedBentGuardConnectedTargetPreimages_sum_le_fixed
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (target : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (items : List (ReflectedBentGuardConnectedTargetPreimage
      D hextent target))
    (hitems : items.Nodup) :
    listQSum
        (reflectedBentGuardConnectedTargetPreimageWeight D) items ≤
      Q'.ofNat (2 ^ reflectedBentPatternFaceIds.length *
        4096 ^ reflectedBentGuardPatternPhysicalMass) := by
  rw [← reflectedBentGuardProvenanceCodeSpace_length]
  exact reflectedBentGuardConnectedTargetPreimages_sum_le_codeSpace_length
    D hextent target items hitems

#print axioms reflectedBentGuardConnectedTargetPreimageCode
#print axioms reflectedBentGuardConnectedTargetPreimage_intermediatePair_eq_of_code_eq
#print axioms reflectedBentGuardConnectedTargetPreimageCodeFiber_sum_le_one
#print axioms reflectedBentGuardConnectedTargetPreimages_sum_le_codeSpace_length
#print axioms reflectedBentGuardConnectedTargetPreimages_scaled_sum_le_one
#print axioms reflectedBentGuardConnectedTargetPreimages_sum_le_fixed

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardConnectedCodeFiberCapacity

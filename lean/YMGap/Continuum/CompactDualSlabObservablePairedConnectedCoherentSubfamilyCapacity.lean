/-
# Common-column capacity for a coherent connected subfamily

The global face-switch decoder is stronger than the finite column argument
needs.  For any duplicate-free list of final-target preimages, it is enough
to know that their intermediate recoupled pairs all equal one anchor pair.
That equality transports every entry into one physical-pair recoupling
column, whose bistochastic normalization bounds the complete subfamily sum
by one.

This is the reusable bridge needed by a finite provenance partition: the
guarded decoder can establish coherence separately in each code fiber without
claiming a decoder on the full connected carrier.

Constructive contract: finite dependent lists, equality transport, and the
proved physical-pair column normalization only.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity

namespace YMGap.Continuum.CompactDualSlabObservablePairedConnectedCoherentSubfamilyCapacity

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedDecoderColumnCapacity
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem nodup_map_of_injective_local {A B : Type}
    (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

def slabObservablePairedConnectedPreimageIntermediatePair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  slabObservablePairedStrandRecoupledPair
    D rootFaceId targetFaceId item.1.1.toRecouplingSource item.1.2.1

/-- Transport one preimage source into the physical data of an anchor once
their intermediate recoupled pairs are equal. -/
def slabObservablePairedConnectedCoherentContributor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (anchor item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : slabObservablePairedConnectedPreimageIntermediatePair
        D rootFaceId targetFaceId item =
      slabObservablePairedConnectedPreimageIntermediatePair
        D rootFaceId targetFaceId anchor) :
    SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 where
  source := item.1.1
  leftPhysical_eq := by
    simpa only [slabObservablePairedConnectedPreimageIntermediatePair,
        slabObservablePairedStrandRecoupledPair_leftPhysical] using
      congrArg
        (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.1.1.1)
        hpairs
  rightPhysical_eq := by
    simpa only [slabObservablePairedConnectedPreimageIntermediatePair,
        slabObservablePairedStrandRecoupledPair_rightPhysical] using
      congrArg
        (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.2.1.1)
        hpairs

theorem slabObservablePairedConnectedCoherentChoice_transport_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (anchor item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : slabObservablePairedConnectedPreimageIntermediatePair
        D rootFaceId targetFaceId item =
      slabObservablePairedConnectedPreimageIntermediatePair
        D rootFaceId targetFaceId anchor) :
    transportSlabPhysicalPairRecouplingTargetAssignment
        (slabObservablePairedConnectedCoherentContributor
          D rootFaceId targetFaceId anchor item hpairs).leftPhysical_eq
        (slabObservablePairedConnectedCoherentContributor
          D rootFaceId targetFaceId anchor item hpairs).rightPhysical_eq
        item.1.2.1 = anchor.1.2.1 := by
  apply item.1.1.toRecouplingSource.anchor.target_eq_of_realizations_eq
    anchor.1.1.toRecouplingSource.anchor
  · exact congrArg
      (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.1.1.2)
      hpairs
  · exact congrArg
      (fun pair : SlabObservableTwoReplicaPair D rootFaceId => pair.2.1.2)
      hpairs

theorem slabObservablePairedConnectedCoherentWeight_eqv_commonColumnWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (anchor item : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : slabObservablePairedConnectedPreimageIntermediatePair
        D rootFaceId targetFaceId item =
      slabObservablePairedConnectedPreimageIntermediatePair
        D rootFaceId targetFaceId anchor) :
    slabObservablePairedConnectedStrandSourceChoiceWeight
        D rootFaceId targetFaceId item.1 ≈
      slabObservablePairedConnectedContributorColumnWeight
        D rootFaceId targetFaceId
        anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1
        (slabObservablePairedConnectedCoherentContributor
          D rootFaceId targetFaceId anchor item hpairs) := by
  have hchoice :=
    slabObservablePairedConnectedCoherentChoice_transport_eq
      D rootFaceId targetFaceId anchor item hpairs
  simpa only [slabObservablePairedConnectedStrandSourceChoiceWeight] using
    (slabObservablePairedConnectedStrandWeight_transport
      D rootFaceId targetFaceId item.1.1 item.1.2
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1
      (slabObservablePairedConnectedCoherentContributor
        D rootFaceId targetFaceId anchor item hpairs).leftPhysical_eq
      (slabObservablePairedConnectedCoherentContributor
        D rootFaceId targetFaceId anchor item hpairs).rightPhysical_eq
      hchoice)

def slabObservablePairedConnectedCoherentContributors
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (items : List (SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target))
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : ∀ item, item ∈ items →
      slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId item =
        slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId anchor) :
    List (SlabObservablePairedConnectedContributorAt
      D rootFaceId targetFaceId
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1) :=
  items.attach.map fun item =>
    slabObservablePairedConnectedCoherentContributor
      D rootFaceId targetFaceId anchor item.1 (hpairs item.1 item.2)

theorem slabObservablePairedConnectedCoherentContributors_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (items : List (SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target))
    (hitems : items.Nodup)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : ∀ item, item ∈ items →
      slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId item =
        slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId anchor) :
    (slabObservablePairedConnectedCoherentContributors
      D rootFaceId targetFaceId items anchor hpairs).Nodup := by
  unfold slabObservablePairedConnectedCoherentContributors
  apply nodup_map_of_injective_local
  · intro left right heq
    apply Subtype.ext
    have hsources : left.1.1.1 = right.1.1.1 := congrArg
      (fun contributor : SlabObservablePairedConnectedContributorAt
        D rootFaceId targetFaceId
        anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 => contributor.source) heq
    cases left with
    | mk leftItem leftMem =>
      cases right with
      | mk rightItem rightMem =>
        cases leftItem with
        | mk leftPreimage leftPreimageMem =>
          cases rightItem with
          | mk rightPreimage rightPreimageMem =>
            cases leftPreimage with
            | mk leftSource leftChoice =>
              cases rightPreimage with
              | mk rightSource rightChoice =>
                dsimp only at hsources
                have hpairsLR :
                    slabObservablePairedStrandRecoupledPair
                        D rootFaceId targetFaceId
                        leftSource.toRecouplingSource leftChoice.1 =
                      slabObservablePairedStrandRecoupledPair
                        D rootFaceId targetFaceId
                        rightSource.toRecouplingSource rightChoice.1 := by
                  exact
                    (hpairs ⟨⟨leftSource, leftChoice⟩, leftPreimageMem⟩
                      leftMem).trans
                    (hpairs ⟨⟨rightSource, rightChoice⟩,
                      rightPreimageMem⟩ rightMem).symm
                subst rightSource
                have hleft := congrArg
                  (fun pair : SlabObservableTwoReplicaPair D rootFaceId =>
                    pair.1.1.2) hpairsLR
                have hright := congrArg
                  (fun pair : SlabObservableTwoReplicaPair D rootFaceId =>
                    pair.2.1.2) hpairsLR
                have htargetChoice :=
                  leftSource.toRecouplingSource.anchor.target_eq_of_realizations_eq
                    leftSource.toRecouplingSource.anchor rfl rfl
                    leftChoice.1 rightChoice.1 hleft hright
                rw [transportSlabPhysicalPairRecouplingTargetAssignment_rfl]
                  at htargetChoice
                have hchoices : leftChoice = rightChoice :=
                  Subtype.ext htargetChoice
                subst rightChoice
                rfl
  · exact attach_nodup_of_nodup _ hitems

theorem slabObservablePairedConnectedCoherentSum_eqv_commonColumnSum
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (items : List (SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target))
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : ∀ item, item ∈ items →
      slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId item =
        slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId anchor) :
    listQSum
        (fun item => slabObservablePairedConnectedStrandSourceChoiceWeight
          D rootFaceId targetFaceId item.1)
        items ≈
      listQSum
        (slabObservablePairedConnectedContributorColumnWeight
          D rootFaceId targetFaceId
          anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1)
        (slabObservablePairedConnectedCoherentContributors
          D rootFaceId targetFaceId items anchor hpairs) := by
  rw [← listQSum_attach]
  unfold slabObservablePairedConnectedCoherentContributors
  rw [listQSum_map]
  apply listQSum_congr
  intro item
  exact slabObservablePairedConnectedCoherentWeight_eqv_commonColumnWeight
    D rootFaceId targetFaceId anchor item.1 (hpairs item.1 item.2)

/-- A duplicate-free coherent subfamily of one final-target preimage has
total local recoupling weight at most one. -/
theorem slabObservablePairedConnectedCoherentSubfamilySum_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (items : List (SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target))
    (hitems : items.Nodup)
    (anchor : SlabObservablePairedConnectedStrandTargetPreimage
      D rootFaceId targetFaceId htarget target)
    (hpairs : ∀ item, item ∈ items →
      slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId item =
        slabObservablePairedConnectedPreimageIntermediatePair
          D rootFaceId targetFaceId anchor) :
    listQSum
        (fun item => slabObservablePairedConnectedStrandSourceChoiceWeight
          D rootFaceId targetFaceId item.1)
        items ≤ (1 : Q') := by
  have hcommon :=
    slabObservablePairedConnectedCoherentSum_eqv_commonColumnSum
      D rootFaceId targetFaceId items anchor hpairs
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcommon)
    (slabObservablePairedConnectedContributorColumnWeight_sum_le_one
      D rootFaceId targetFaceId
      anchor.1.1.1.1.1.1 anchor.1.1.1.2.1.1 anchor.1.2.1
      (slabObservablePairedConnectedCoherentContributors
        D rootFaceId targetFaceId items anchor hpairs)
      (slabObservablePairedConnectedCoherentContributors_nodup
        D rootFaceId targetFaceId items hitems anchor hpairs))

#print axioms slabObservablePairedConnectedPreimageIntermediatePair
#print axioms slabObservablePairedConnectedCoherentChoice_transport_eq
#print axioms slabObservablePairedConnectedCoherentContributors_nodup
#print axioms slabObservablePairedConnectedCoherentSubfamilySum_le_one

end YMGap.Continuum.CompactDualSlabObservablePairedConnectedCoherentSubfamilyCapacity

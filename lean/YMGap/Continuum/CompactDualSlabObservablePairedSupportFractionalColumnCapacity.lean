/-
# Global column capacity for the paired-support fractional kernel

Fix one concrete four-cell target.  Its duplicate-free source-choice
preimage is empty or has a literal head.  In the nonempty case that head
selects one switched physical pair and one abstract target column.
Common-preimage coherence transports every other term to that column.
The retained source pairs are distinct contributors, so exact column
normalization bounds their total mass by one.

This discharges the finite dependent-kernel capacity node.  It is not a
Gibbs estimate, a beta-uniform statement, or a continuum claim.

Constructive contract: head/tail case analysis, equality transport, finite
injective summation, and exact `Q'`; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence
import YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportColumnNoOverload
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPreimageCoherence
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Transport one source row into a fixed physical column -/

def slabObservablePairedSupportContributorTransport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (leftPhysical rightPhysical : SlabLabelling)
    (hleft : slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId source.1 = leftPhysical)
    (hright : slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId source.1 = rightPhysical) :
    SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId leftPhysical rightPhysical where
  pair := source.1
  pair_mem := source.pair_mem_fourCell
  disconnected := source.disconnected
  leftPhysical_eq := hleft
  rightPhysical_eq := hright

theorem slabObservablePairedSupportRecouplingWeight_transport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source)
    (leftPhysical rightPhysical : SlabLabelling)
    (targetColumn : SlabPhysicalPairRecouplingTargetAssignment
      D.extent leftPhysical rightPhysical)
    (hleft : slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId source.1 = leftPhysical)
    (hright : slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId source.1 = rightPhysical)
    (hchoice : transportSlabPhysicalPairRecouplingTargetAssignment
        hleft hright choice = targetColumn) :
    slabObservablePairedSupportRecouplingWeight
        D rootFaceId targetFaceId htarget source choice ≈
      slabObservablePairedSupportContributorColumnWeight
        D rootFaceId targetFaceId leftPhysical rightPhysical
        htarget targetColumn
        (slabObservablePairedSupportContributorTransport
          D rootFaceId targetFaceId source
          leftPhysical rightPhysical hleft hright) := by
  cases hleft
  cases hright
  rw [transportSlabPhysicalPairRecouplingTargetAssignment_rfl] at hchoice
  subst targetColumn
  exact Q'.eqv_refl _

/-! ## 2. Equality on source choices inside one realized target -/

theorem slabObservablePairedSupportRecoupledTargetPair_injective_fixed_source
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (first second : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source)
    (heq : slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget source first =
      slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget source second) :
    first = second := by
  have htransport :=
    slabObservablePairedSupportTransportChoiceOfTargetPairEq_eq
      D rootFaceId targetFaceId htarget
      source source first second heq
  unfold slabObservablePairedSupportTransportChoiceOfTargetPairEq at htransport
  have hleft :
      slabObservablePairedSupportRecoupledTargetPair_leftPhysical_eq
        D rootFaceId targetFaceId htarget
        source source first second heq = rfl :=
    Subsingleton.elim _ _
  have hright :
      slabObservablePairedSupportRecoupledTargetPair_rightPhysical_eq
        D rootFaceId targetFaceId htarget
        source source first second heq = rfl :=
    Subsingleton.elim _ _
  rw [hleft, hright,
    transportSlabPhysicalPairRecouplingTargetAssignment_rfl] at htransport
  exact htransport

theorem slabObservablePairedSupportRecouplingSourceChoice_eq_of_source_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId)
    (hsource : first.1 = second.1)
    (hrealize : slabObservablePairedSupportRecouplingSourceChoiceRealize
        D rootFaceId targetFaceId htarget first =
      slabObservablePairedSupportRecouplingSourceChoiceRealize
        D rootFaceId targetFaceId htarget second) :
    first = second := by
  cases first with
  | mk firstSource firstChoice =>
      cases second with
      | mk secondSource secondChoice =>
          dsimp only at hsource
          subst secondSource
          have hchoice :=
            slabObservablePairedSupportRecoupledTargetPair_injective_fixed_source
              D rootFaceId targetFaceId htarget
              firstSource firstChoice secondChoice hrealize
          subst secondChoice
          rfl

/-! ## 3. The literal preimage subtype and its anchor column -/

abbrev SlabObservablePairedSupportRecouplingTargetPreimage
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :=
  {item // item ∈ slabObservablePairedSupportRecouplingTargetPreimages
    D rootFaceId targetFaceId htarget target}

abbrev SlabObservablePairedSupportRecouplingTargetAnchor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :=
  {item : SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId //
    target = slabObservablePairedSupportRecouplingSourceChoiceRealize
      D rootFaceId targetFaceId htarget item}

def slabObservablePairedSupportRecouplingTargetPreimagesAttached
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabObservablePairedSupportRecouplingTargetPreimage
      D rootFaceId targetFaceId htarget target) :=
  (slabObservablePairedSupportRecouplingTargetPreimages
    D rootFaceId targetFaceId htarget target).attach

theorem SlabObservablePairedSupportRecouplingTargetPreimage.target_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {target : SlabObservableTwoReplicaPair D rootFaceId}
    (item : SlabObservablePairedSupportRecouplingTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    target = slabObservablePairedSupportRecouplingSourceChoiceRealize
      D rootFaceId targetFaceId htarget item.1 :=
  (mem_slabObservablePairedSupportRecouplingTargetPreimages_iff
    D rootFaceId targetFaceId htarget target item.1).mp item.2 |>.2

def slabObservablePairedSupportPreimageTargetEqData
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target)
    (item : SlabObservablePairedSupportRecouplingTargetPreimage
      D rootFaceId targetFaceId htarget target) :=
  slabObservablePairedSupportTargetPairEqData
    D rootFaceId targetFaceId htarget
    item.1.1 anchor.1.1 item.1.2 anchor.1.2
    (item.target_eq.symm.trans anchor.2)

def slabObservablePairedSupportPreimageContributor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target)
    (item : SlabObservablePairedSupportRecouplingTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId
      (slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId anchor.1.1.1)
      (slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId anchor.1.1.1) :=
  let data := slabObservablePairedSupportPreimageTargetEqData
    D rootFaceId targetFaceId htarget target anchor item
  slabObservablePairedSupportContributorTransport
    D rootFaceId targetFaceId item.1.1
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId anchor.1.1.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId anchor.1.1.1)
    data.leftPhysical data.rightPhysical

theorem slabObservablePairedSupportPreimageWeight_eqv_commonColumnWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target)
    (item : SlabObservablePairedSupportRecouplingTargetPreimage
      D rootFaceId targetFaceId htarget target) :
    slabObservablePairedSupportRecouplingSourceChoiceWeight
        D rootFaceId targetFaceId htarget item.1 ≈
      slabObservablePairedSupportContributorColumnWeight
        D rootFaceId targetFaceId
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId anchor.1.1.1)
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId anchor.1.1.1)
        htarget anchor.1.2
        (slabObservablePairedSupportPreimageContributor
          D rootFaceId targetFaceId htarget target anchor item) := by
  let data := slabObservablePairedSupportPreimageTargetEqData
    D rootFaceId targetFaceId htarget target anchor item
  exact slabObservablePairedSupportRecouplingWeight_transport
    D rootFaceId targetFaceId htarget
    item.1.1 item.1.2
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId anchor.1.1.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId anchor.1.1.1)
    anchor.1.2 data.leftPhysical data.rightPhysical
    data.transport_choice_eq

/-! ## 4. Duplicate-free contributors and the column bound -/

def slabObservablePairedSupportPreimageContributors
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target) :
    List (SlabObservablePairedSupportContributorAt
      D rootFaceId targetFaceId
      (slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId anchor.1.1.1)
      (slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId anchor.1.1.1)) :=
  (slabObservablePairedSupportRecouplingTargetPreimagesAttached
    D rootFaceId targetFaceId htarget target).map fun item =>
      slabObservablePairedSupportPreimageContributor
        D rootFaceId targetFaceId htarget target anchor item

private theorem nodup_map_of_injective {A B : Type} (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

theorem slabObservablePairedSupportPreimageContributors_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target) :
    (slabObservablePairedSupportPreimageContributors
      D rootFaceId targetFaceId htarget target anchor).Nodup := by
  unfold slabObservablePairedSupportPreimageContributors
  apply nodup_map_of_injective
  · intro left right heq
    apply Subtype.ext
    apply slabObservablePairedSupportRecouplingSourceChoice_eq_of_source_eq
      D rootFaceId targetFaceId htarget
    · apply Subtype.ext
      exact congrArg
        (fun contributor : SlabObservablePairedSupportContributorAt
            D rootFaceId targetFaceId
            (slabObservablePairSupportSwitchedLeftPhysical
              D targetFaceId anchor.1.1.1)
            (slabObservablePairSupportSwitchedRightPhysical
              D targetFaceId anchor.1.1.1) => contributor.pair)
        heq
    · exact left.target_eq.symm.trans right.target_eq
  · exact attach_nodup_of_nodup _
      (slabObservablePairedSupportRecouplingTargetPreimages_nodup
        D rootFaceId targetFaceId htarget target)

theorem slabObservablePairedSupportPreimageSum_eqv_commonColumnSum
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target) :
    listQSum
        (slabObservablePairedSupportRecouplingSourceChoiceWeight
          D rootFaceId targetFaceId htarget)
        (slabObservablePairedSupportRecouplingTargetPreimages
          D rootFaceId targetFaceId htarget target) ≈
      listQSum
        (slabObservablePairedSupportContributorColumnWeight
          D rootFaceId targetFaceId
          (slabObservablePairSupportSwitchedLeftPhysical
            D targetFaceId anchor.1.1.1)
          (slabObservablePairSupportSwitchedRightPhysical
            D targetFaceId anchor.1.1.1)
          htarget anchor.1.2)
        (slabObservablePairedSupportPreimageContributors
          D rootFaceId targetFaceId htarget target anchor) := by
  rw [← listQSum_attach
    (slabObservablePairedSupportRecouplingSourceChoiceWeight
      D rootFaceId targetFaceId htarget)
    (slabObservablePairedSupportRecouplingTargetPreimages
      D rootFaceId targetFaceId htarget target)]
  unfold slabObservablePairedSupportPreimageContributors
  rw [listQSum_map]
  apply listQSum_congr
  intro item
  exact slabObservablePairedSupportPreimageWeight_eqv_commonColumnWeight
    D rootFaceId targetFaceId htarget target anchor item

theorem slabObservablePairedSupportPreimageSum_le_one_of_anchor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (anchor : SlabObservablePairedSupportRecouplingTargetAnchor
      D rootFaceId targetFaceId htarget target) :
    listQSum
        (slabObservablePairedSupportRecouplingSourceChoiceWeight
          D rootFaceId targetFaceId htarget)
        (slabObservablePairedSupportRecouplingTargetPreimages
          D rootFaceId targetFaceId htarget target) ≤ 1 := by
  have hsum :=
    slabObservablePairedSupportPreimageSum_eqv_commonColumnSum
      D rootFaceId targetFaceId htarget target anchor
  have hcolumn :=
    slabObservablePairedSupportContributorColumnWeight_sum_le_one
      D rootFaceId targetFaceId
      (slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId anchor.1.1.1)
      (slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId anchor.1.1.1)
      htarget anchor.1.2
      (slabObservablePairedSupportPreimageContributors
        D rootFaceId targetFaceId htarget target anchor)
      (slabObservablePairedSupportPreimageContributors_nodup
        D rootFaceId targetFaceId htarget target anchor)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) hcolumn

theorem slabObservablePairedSupportPreimageSum_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    listQSum
        (slabObservablePairedSupportRecouplingSourceChoiceWeight
          D rootFaceId targetFaceId htarget)
        (slabObservablePairedSupportRecouplingTargetPreimages
          D rootFaceId targetFaceId htarget target) ≤ 1 := by
  cases hpreimages : slabObservablePairedSupportRecouplingTargetPreimages
      D rootFaceId targetFaceId htarget target with
  | nil =>
      change (0 : Q') ≤ 1
      exact Q'.zero_le_one
  | cons head tail =>
      have hhead : head ∈
          slabObservablePairedSupportRecouplingTargetPreimages
            D rootFaceId targetFaceId htarget target := by
        rw [hpreimages]
        exact List.mem_cons_self
      let anchor : SlabObservablePairedSupportRecouplingTargetAnchor
          D rootFaceId targetFaceId htarget target :=
        ⟨head,
          (mem_slabObservablePairedSupportRecouplingTargetPreimages_iff
            D rootFaceId targetFaceId htarget target head).mp hhead |>.2⟩
      have hbound :
          listQSum
              (slabObservablePairedSupportRecouplingSourceChoiceWeight
                D rootFaceId targetFaceId htarget)
              (slabObservablePairedSupportRecouplingTargetPreimages
                D rootFaceId targetFaceId htarget target) ≤ 1 :=
        slabObservablePairedSupportPreimageSum_le_one_of_anchor
          D rootFaceId targetFaceId htarget target anchor
      rw [hpreimages] at hbound
      exact hbound

/-! ## 5. The global dependent-kernel column-capacity theorem -/

theorem slabObservablePairedSupportDependentColumnCapacity
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
    listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedSupportRecouplingChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingWeight
            D rootFaceId targetFaceId htarget)
          (slabObservablePairedSupportRecoupledTargetPair
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedSupportSeparatedSources
          D rootFaceId targetFaceId) ≤ 1 := by
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabObservablePairedSupportDependentPushforward_eqv_preimage_sum
        D rootFaceId targetFaceId htarget target))
    (slabObservablePairedSupportPreimageSum_le_one
      D rootFaceId targetFaceId htarget target)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity.slabObservablePairedSupportRecouplingWeight_transport
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity.slabObservablePairedSupportRecoupledTargetPair_injective_fixed_source
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity.slabObservablePairedSupportPreimageContributors_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity.slabObservablePairedSupportPreimageSum_le_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalColumnCapacity.slabObservablePairedSupportDependentColumnCapacity

/-
# Original-cutoff local witnesses for a two-replica face switch

A face-constant mate-closed selection splits each accepted SU(2) link network
into selected and unselected accepted subnetworks.  This module crosses the
pieces between two replicas.  The left switched link is the unselected part
of the left source plus the selected part of the right source; the right
switched link uses the complementary combination.

At each face these physical sums choose exactly one original spin.  Hence
they are the literal two-replica face swaps and remain bounded by the original
cutoff.  Same-cutoff support addition then constructs accepted auxiliary
witnesses for both switched links inside the production `6*K` window.

Constructive contract: explicit subnetworks, pointwise Boolean cases, and
finite support addition only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, `noncomputable`, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CanonicalLinkSameCutoffSupportAddition
import YMGap.Continuum.CompactDualSlabSelectionComplement
import YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate

namespace YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkSameCutoffSupportAddition
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.CompactDualSlabSelectionComplement
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Name both accepted halves of one link -/

/-- The auxiliary labelling of the unselected subnetwork. -/
def slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) : SlabLabelling :=
  lowerEdgeLabellingBy auxiliary selection.toMateClosedSelection.drop

/-- The unselected subnetwork is an accepted witness at the original cutoff,
complementing the selected-subnetwork theorem. -/
theorem slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_mem
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary selection ∈
      slabLinkFusionWitnesses cutoff extent
        (lowerSlabPhysicalByFaceStrandSelection selection.selected) link := by
  unfold slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary
  exact selection.lower_auxiliary_mem (by
    rw [selection.toMateClosedSelection_drop]
    exact SlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
      selection)

/-! ## 2. The physical sums are exactly the facewise transposition -/

/-- The first crossed physical link field: keep unselected left strands and
import selected right strands. -/
def slabCrossReplicaLeftPhysical
    {leftPhysical rightPhysical : SlabLabelling}
    (leftSelected : SlabFaceStrandCopy leftPhysical → Bool)
    (rightSelected : SlabFaceStrandCopy rightPhysical → Bool) :
    SlabLabelling :=
  addEdgeLabelling
    (lowerSlabPhysicalByFaceStrandSelection leftSelected)
    (slabFaceStrandSelectionCount rightSelected)

/-- The complementary crossed physical link field. -/
def slabCrossReplicaRightPhysical
    {leftPhysical rightPhysical : SlabLabelling}
    (leftSelected : SlabFaceStrandCopy leftPhysical → Bool)
    (rightSelected : SlabFaceStrandCopy rightPhysical → Bool) :
    SlabLabelling :=
  addEdgeLabelling
    (slabFaceStrandSelectionCount leftSelected)
    (lowerSlabPhysicalByFaceStrandSelection rightSelected)

theorem slabCrossReplicaLeftPhysical_eq_faceSwap
    {leftPhysical rightPhysical : SlabLabelling}
    (mask : Nat → Bool)
    (leftSelected : SlabFaceStrandCopy leftPhysical → Bool)
    (rightSelected : SlabFaceStrandCopy rightPhysical → Bool)
    (hleftConstant : ∀ copy, leftSelected copy = mask copy.faceId)
    (hrightConstant : ∀ copy, rightSelected copy = mask copy.faceId) :
    slabCrossReplicaLeftPhysical leftSelected rightSelected =
      twoReplicaFaceSwapLeft mask leftPhysical rightPhysical := by
  have hleft := lowerSlabPhysicalByFaceStrandSelection_eq_unselectedByMask
    leftSelected mask hleftConstant
  have hright := slabFaceStrandSelectionCount_eq_selectedByMask
    rightSelected mask hrightConstant
  funext faceId
  unfold slabCrossReplicaLeftPhysical
  unfold addEdgeLabelling
  rw [congrFun hleft faceId, congrFun hright faceId]
  unfold slabPhysicalUnselectedByMask slabPhysicalSelectedByMask
    twoReplicaFaceSwapLeft
  cases mask faceId <;> simp

theorem slabCrossReplicaRightPhysical_eq_faceSwap
    {leftPhysical rightPhysical : SlabLabelling}
    (mask : Nat → Bool)
    (leftSelected : SlabFaceStrandCopy leftPhysical → Bool)
    (rightSelected : SlabFaceStrandCopy rightPhysical → Bool)
    (hleftConstant : ∀ copy, leftSelected copy = mask copy.faceId)
    (hrightConstant : ∀ copy, rightSelected copy = mask copy.faceId) :
    slabCrossReplicaRightPhysical leftSelected rightSelected =
      twoReplicaFaceSwapRight mask leftPhysical rightPhysical := by
  have hleft := slabFaceStrandSelectionCount_eq_selectedByMask
    leftSelected mask hleftConstant
  have hright := lowerSlabPhysicalByFaceStrandSelection_eq_unselectedByMask
    rightSelected mask hrightConstant
  funext faceId
  unfold slabCrossReplicaRightPhysical
  unfold addEdgeLabelling
  rw [congrFun hleft faceId, congrFun hright faceId]
  unfold slabPhysicalUnselectedByMask slabPhysicalSelectedByMask
    twoReplicaFaceSwapRight
  cases mask faceId <;> simp

/-- A facewise transposition of two `K`-bounded physical fields is still
`K`-bounded. -/
theorem twoReplicaFaceSwapLeft_bounded
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    (mask : Nat → Bool)
    (hleft : SlabFaceLabellingBounded K extent leftPhysical)
    (hright : SlabFaceLabellingBounded K extent rightPhysical) :
    SlabFaceLabellingBounded K extent
      (twoReplicaFaceSwapLeft mask leftPhysical rightPhysical) := by
  intro faceId hface
  cases hmask : mask faceId with
  | false => simpa [twoReplicaFaceSwapLeft, hmask] using hleft faceId hface
  | true => simpa [twoReplicaFaceSwapLeft, hmask] using hright faceId hface

/-- The complementary facewise output obeys the same cutoff. -/
theorem twoReplicaFaceSwapRight_bounded
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    (mask : Nat → Bool)
    (hleft : SlabFaceLabellingBounded K extent leftPhysical)
    (hright : SlabFaceLabellingBounded K extent rightPhysical) :
    SlabFaceLabellingBounded K extent
      (twoReplicaFaceSwapRight mask leftPhysical rightPhysical) := by
  intro faceId hface
  cases hmask : mask faceId with
  | false => simpa [twoReplicaFaceSwapRight, hmask] using hright faceId hface
  | true => simpa [twoReplicaFaceSwapRight, hmask] using hleft faceId hface

/-! ## 3. Accepted original-cutoff auxiliary witnesses for both outputs -/

/-- Auxiliary field for the first crossed replica. -/
def slabCrossReplicaLeftAuxiliary
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    {hleftMem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link}
    {hrightMem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link}
    (leftSelection : SlabLinkPartnerClosedFaceSelection
      K extent leftPhysical link leftAuxiliary hleftMem)
    (rightSelection : SlabLinkPartnerClosedFaceSelection
      K extent rightPhysical link rightAuxiliary hrightMem) : SlabLabelling :=
  addEdgeLabelling
    (slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary leftSelection)
    (slabLinkPartnerClosedFaceSelectionSelectedAuxiliary rightSelection)

/-- Auxiliary field for the second crossed replica. -/
def slabCrossReplicaRightAuxiliary
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    {hleftMem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link}
    {hrightMem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link}
    (leftSelection : SlabLinkPartnerClosedFaceSelection
      K extent leftPhysical link leftAuxiliary hleftMem)
    (rightSelection : SlabLinkPartnerClosedFaceSelection
      K extent rightPhysical link rightAuxiliary hrightMem) : SlabLabelling :=
  addEdgeLabelling
    (slabLinkPartnerClosedFaceSelectionSelectedAuxiliary leftSelection)
    (slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary rightSelection)

/-- **First local switch compiler.**  The crossed auxiliary field is an
accepted witness over the literal left face-swap output at the original
cutoff. -/
theorem slabCrossReplicaLeftAuxiliary_mem
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    {hleftMem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link}
    {hrightMem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link}
    (mask : Nat → Bool)
    (hleftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (hrightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    (leftSelection : SlabLinkPartnerClosedFaceSelection
      K extent leftPhysical link leftAuxiliary hleftMem)
    (rightSelection : SlabLinkPartnerClosedFaceSelection
      K extent rightPhysical link rightAuxiliary hrightMem)
    (hleftConstant : ∀ copy, leftSelection.selected copy = mask copy.faceId)
    (hrightConstant : ∀ copy, rightSelection.selected copy = mask copy.faceId) :
    slabCrossReplicaLeftAuxiliary leftSelection rightSelection ∈
      slabLinkFusionWitnesses K extent
        (twoReplicaFaceSwapLeft mask leftPhysical rightPhysical) link := by
  have hphysicalEq := slabCrossReplicaLeftPhysical_eq_faceSwap
    mask leftSelection.selected rightSelection.selected
      hleftConstant hrightConstant
  have hsum := slabLinkFusionWitness_add_mem_sameCutoff link
    (leftPhysical :=
      lowerSlabPhysicalByFaceStrandSelection leftSelection.selected)
    (rightPhysical :=
      slabLinkPartnerClosedFaceSelectionSelectedPhysical rightSelection)
    (leftAuxiliary :=
      slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary leftSelection)
    (rightAuxiliary :=
      slabLinkPartnerClosedFaceSelectionSelectedAuxiliary rightSelection)
    (by
      rw [slabLinkPartnerClosedFaceSelectionSelectedPhysical_eq_count]
      change SlabFaceLabellingBounded K extent
        (slabCrossReplicaLeftPhysical
          leftSelection.selected rightSelection.selected)
      rw [hphysicalEq]
      exact twoReplicaFaceSwapLeft_bounded mask
        hleftBounded hrightBounded)
    (slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_mem leftSelection)
    (slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_mem rightSelection)
  rw [slabLinkPartnerClosedFaceSelectionSelectedPhysical_eq_count] at hsum
  change slabCrossReplicaLeftAuxiliary leftSelection rightSelection ∈
    slabLinkFusionWitnesses K extent
      (slabCrossReplicaLeftPhysical
        leftSelection.selected rightSelection.selected) link at hsum
  rw [hphysicalEq] at hsum
  exact hsum

/-- **Second local switch compiler.**  The complementary crossed auxiliary
field is accepted over the literal right face-swap output at the same
production cutoff. -/
theorem slabCrossReplicaRightAuxiliary_mem
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    {hleftMem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link}
    {hrightMem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link}
    (mask : Nat → Bool)
    (hleftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (hrightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    (leftSelection : SlabLinkPartnerClosedFaceSelection
      K extent leftPhysical link leftAuxiliary hleftMem)
    (rightSelection : SlabLinkPartnerClosedFaceSelection
      K extent rightPhysical link rightAuxiliary hrightMem)
    (hleftConstant : ∀ copy, leftSelection.selected copy = mask copy.faceId)
    (hrightConstant : ∀ copy, rightSelection.selected copy = mask copy.faceId) :
    slabCrossReplicaRightAuxiliary leftSelection rightSelection ∈
      slabLinkFusionWitnesses K extent
        (twoReplicaFaceSwapRight mask leftPhysical rightPhysical) link := by
  have hphysicalEq := slabCrossReplicaRightPhysical_eq_faceSwap
    mask leftSelection.selected rightSelection.selected
      hleftConstant hrightConstant
  have hsum := slabLinkFusionWitness_add_mem_sameCutoff link
    (leftPhysical :=
      slabLinkPartnerClosedFaceSelectionSelectedPhysical leftSelection)
    (rightPhysical :=
      lowerSlabPhysicalByFaceStrandSelection rightSelection.selected)
    (leftAuxiliary :=
      slabLinkPartnerClosedFaceSelectionSelectedAuxiliary leftSelection)
    (rightAuxiliary :=
      slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary rightSelection)
    (by
      rw [slabLinkPartnerClosedFaceSelectionSelectedPhysical_eq_count]
      change SlabFaceLabellingBounded K extent
        (slabCrossReplicaRightPhysical
          leftSelection.selected rightSelection.selected)
      rw [hphysicalEq]
      exact twoReplicaFaceSwapRight_bounded mask
        hleftBounded hrightBounded)
    (slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_mem leftSelection)
    (slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_mem rightSelection)
  rw [slabLinkPartnerClosedFaceSelectionSelectedPhysical_eq_count] at hsum
  change slabCrossReplicaRightAuxiliary leftSelection rightSelection ∈
    slabLinkFusionWitnesses K extent
      (slabCrossReplicaRightPhysical
        leftSelection.selected rightSelection.selected) link at hsum
  rw [hphysicalEq] at hsum
  exact hsum

#print axioms slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_mem
#print axioms slabCrossReplicaLeftPhysical_eq_faceSwap
#print axioms slabCrossReplicaRightPhysical_eq_faceSwap
#print axioms slabCrossReplicaLeftAuxiliary_mem
#print axioms slabCrossReplicaRightAuxiliary_mem

end YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch

/-
# Complementary mate-closed selections split an accepted SU(2) network

The two-replica face switch should not rebuild trivalent pairings by hand.
A mate-closed Boolean strand selection and its Boolean complement are both
mate-closed.  Removing the complement leaves exactly the selected strand
counts, so the existing removal compiler proves that the selected subnetwork
is itself admissible.  Removing the original selection similarly proves
admissibility of the complementary subnetwork.

This module establishes that decomposition first for arbitrary resolved
trivalent networks and then for one accepted corrected-slab link.  The slab
specialization constructs an actual selected physical labelling and an
accepted selected auxiliary witness at the original cutoff.  These are the
two summands needed by the later cross-replica splice.

Honest scope: this module does not add subnetworks from different replicas,
prove the sum lies in the original auxiliary cutoff window, assemble a global
switched assignment, or construct the decoder.

Constructive contract: Boolean complementation, primitive natural interval
counts, and the existing mate-closed removal compiler only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop

namespace YMGap.Continuum.CompactDualSlabSelectionComplement

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Exact Boolean interval complementation -/

/-- A Boolean indicator and the indicator of its complement sum to one. -/
theorem boolIndicator_add_not (value : Bool) :
    boolIndicator value + boolIndicator (!value) = 1 := by
  cases value <;> rfl

/-- A finite Boolean interval and its pointwise complement partition every
slot exactly once. -/
theorem boolCountFrom_add_not
    (selected : Nat → Bool) (start : Nat) : ∀ length : Nat,
    boolCountFrom selected start length +
        boolCountFrom (fun slot => !(selected slot)) start length =
      length
  | 0 => rfl
  | length + 1 => by
      rw [boolCountFrom, boolCountFrom]
      have htail := boolCountFrom_add_not selected (start + 1) length
      have hhead := boolIndicator_add_not (selected start)
      omega

/-- Counting the constantly false predicate gives zero. -/
theorem boolCountFrom_false (start : Nat) : ∀ length : Nat,
    boolCountFrom (fun _ => false) start length = 0
  | 0 => rfl
  | length + 1 => by
      rw [boolCountFrom]
      simp [boolIndicator, boolCountFrom_false (start + 1) length]

/-- Counting the constantly true predicate gives the interval length. -/
theorem boolCountFrom_true (start : Nat) : ∀ length : Nat,
    boolCountFrom (fun _ => true) start length = length
  | 0 => rfl
  | length + 1 => by
      rw [boolCountFrom, boolCountFrom_true (start + 1) length]
      simp [boolIndicator, Nat.add_comm]

/-! ## 2. Complement an arbitrary mate-closed network selection -/

/-- Boolean complementation preserves every local mate equation. -/
def resolvedNetworkMateClosedSelectionComplement
    {label : EdgeLabelling}
    {resolved : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection resolved) :
    ResolvedNetworkMateClosedSelection resolved where
  selected := fun edge slot => !(selection.selected edge slot)
  mate_closed := by
    intro vertex hvertex port
    rw [selection.mate_closed vertex hvertex port]

/-- The selected and complementary edge drops partition the complete source
edge label exactly. -/
theorem resolvedNetworkMateClosedSelectionDrop_add_complementDrop
    {label : EdgeLabelling}
    {resolved : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection resolved)
    (edge : Nat) :
    selection.drop edge +
        (resolvedNetworkMateClosedSelectionComplement selection).drop edge =
      label edge := by
  unfold ResolvedNetworkMateClosedSelection.drop
    resolvedNetworkMateClosedSelectionComplement
  exact boolCountFrom_add_not
    (selection.selected edge) 0 (label edge)

/-- Removing the complementary strands leaves exactly the selected strand
count on every graph edge. -/
theorem resolvedNetworkMateClosedSelectionLower_by_complement_eq_drop
    {label : EdgeLabelling}
    {resolved : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection resolved) :
    lowerEdgeLabellingBy label
        (resolvedNetworkMateClosedSelectionComplement selection).drop =
      selection.drop := by
  funext edge
  unfold lowerEdgeLabellingBy
  have hpartition :=
    resolvedNetworkMateClosedSelectionDrop_add_complementDrop selection edge
  omega

/-- **Selected-subnetwork admissibility.**  The selected edge-count
labelling of any mate-closed selection on a resolved admissible network is
itself admissible on the same ordered trivalent graph. -/
theorem resolvedNetworkMateClosedSelectionDrop_vertices_admissible
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (selection : ResolvedNetworkMateClosedSelection network.resolved) :
    verticesAdmissibleB vertices selection.drop = true := by
  have hadmissible :=
    ((resolvedNetworkMateClosedSelectionComplement selection).toCoherentRemoval
      network).vertices_admissible
  unfold CoherentResolvedTrivalentRemoval.target at hadmissible
  change verticesAdmissibleB vertices
    (lowerEdgeLabellingBy label
      (resolvedNetworkMateClosedSelectionComplement selection).drop) = true
    at hadmissible
  rw [resolvedNetworkMateClosedSelectionLower_by_complement_eq_drop
    selection] at hadmissible
  exact hadmissible

/-! ## 3. Complement a literal physical face-copy selection -/

/-- Pointwise Boolean complementation of a linkwise partner-closed physical
face-copy selection is again partner-closed. -/
def slabLinkPartnerClosedFaceSelectionComplement
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem where
  selected := fun copy => !(selection.selected copy)
  partner_closed := by
    intro terminal
    rw [selection.partner_closed terminal]

/-- On every actual face slot, totalizing the complemented selection agrees
with pointwise complementation of the original totalized selection. -/
theorem slabLinkPartnerClosedFaceSelectionAt_complement
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (faceId slot : Nat) (hslot : slot < physical faceId) :
    slabFaceStrandSelectionAt
        (slabLinkPartnerClosedFaceSelectionComplement selection).selected
        faceId slot =
      !(slabFaceStrandSelectionAt selection.selected faceId slot) := by
  simp [slabFaceStrandSelectionAt, hslot,
    slabLinkPartnerClosedFaceSelectionComplement]

/-- The selected and complementary face-copy counts partition the complete
physical spin at every face. -/
theorem slabLinkPartnerClosedFaceSelectionCount_add_complement
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (faceId : Nat) :
    slabFaceStrandSelectionCount selection.selected faceId +
        slabFaceStrandSelectionCount
          (slabLinkPartnerClosedFaceSelectionComplement selection).selected
          faceId =
      physical faceId := by
  unfold slabFaceStrandSelectionCount
  have hcomplement :
      boolCountFrom
          (slabFaceStrandSelectionAt
            (slabLinkPartnerClosedFaceSelectionComplement selection).selected
            faceId)
          0 (physical faceId) =
        boolCountFrom
          (fun slot =>
            !(slabFaceStrandSelectionAt selection.selected faceId slot))
          0 (physical faceId) := by
    apply boolCountFrom_congr
    intro offset hoffset
    simp only [Nat.zero_add]
    exact slabLinkPartnerClosedFaceSelectionAt_complement
      selection faceId offset hoffset
  rw [hcomplement]
  exact boolCountFrom_add_not
    (slabFaceStrandSelectionAt selection.selected faceId)
    0 (physical faceId)

/-! ## 4. Face-constant selections are literal all-or-nothing masks -/

/-- Keep a physical face label exactly when its Boolean mask bit is true. -/
def slabPhysicalSelectedByMask
    (mask : Nat → Bool) (physical : SlabLabelling) : SlabLabelling :=
  fun faceId => if mask faceId then physical faceId else 0

/-- Keep the complementary physical face labels. -/
def slabPhysicalUnselectedByMask
    (mask : Nat → Bool) (physical : SlabLabelling) : SlabLabelling :=
  fun faceId => if mask faceId then 0 else physical faceId

/-- If every strand copy of a face reads the same face bit, its selected-copy
count is the all-or-nothing masked physical label. -/
theorem slabFaceStrandSelectionCount_eq_selectedByMask
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical → Bool)
    (mask : Nat → Bool)
    (hconstant : ∀ copy, selected copy = mask copy.faceId) :
    slabFaceStrandSelectionCount selected =
      slabPhysicalSelectedByMask mask physical := by
  funext faceId
  unfold slabFaceStrandSelectionCount slabPhysicalSelectedByMask
  cases hmask : mask faceId with
  | false =>
      have hcount :
          boolCountFrom (slabFaceStrandSelectionAt selected faceId)
              0 (physical faceId) =
            boolCountFrom (fun _ => false) 0 (physical faceId) := by
        apply boolCountFrom_congr
        intro offset hoffset
        simp only [Nat.zero_add]
        simp [slabFaceStrandSelectionAt, hoffset,
          hconstant, hmask]
      rw [hcount, boolCountFrom_false]
      rfl
  | true =>
      have hcount :
          boolCountFrom (slabFaceStrandSelectionAt selected faceId)
              0 (physical faceId) =
            boolCountFrom (fun _ => true) 0 (physical faceId) := by
        apply boolCountFrom_congr
        intro offset hoffset
        simp only [Nat.zero_add]
        simp [slabFaceStrandSelectionAt, hoffset,
          hconstant, hmask]
      rw [hcount, boolCountFrom_true]
      rfl

/-- Lowering by a face-constant selection retains exactly the unselected
physical faces. -/
theorem lowerSlabPhysicalByFaceStrandSelection_eq_unselectedByMask
    {physical : SlabLabelling}
    (selected : SlabFaceStrandCopy physical → Bool)
    (mask : Nat → Bool)
    (hconstant : ∀ copy, selected copy = mask copy.faceId) :
    lowerSlabPhysicalByFaceStrandSelection selected =
      slabPhysicalUnselectedByMask mask physical := by
  funext faceId
  unfold lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
    slabPhysicalUnselectedByMask
  rw [congrFun
    (slabFaceStrandSelectionCount_eq_selectedByMask
      selected mask hconstant) faceId]
  unfold slabPhysicalSelectedByMask
  cases mask faceId <;> simp

/-! ## 5. Literal selected physical and auxiliary subnetworks -/

/-- The physical edge labelling carried only by selected copies. -/
def slabLinkPartnerClosedFaceSelectionSelectedPhysical
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) : SlabLabelling :=
  lowerSlabPhysicalByFaceStrandSelection
    (slabLinkPartnerClosedFaceSelectionComplement selection).selected

/-- Lowering by the complementary face selection leaves exactly the selected
physical face-count labelling. -/
theorem slabLinkPartnerClosedFaceSelectionLowerPhysical_complement_eq_selected
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    lowerSlabPhysicalByFaceStrandSelection
        (slabLinkPartnerClosedFaceSelectionComplement selection).selected =
      slabLinkPartnerClosedFaceSelectionSelectedPhysical selection := rfl

/-- The removal presentation of the selected physical subnetwork is exactly
the direct count of selected copies at every face. -/
theorem slabLinkPartnerClosedFaceSelectionSelectedPhysical_eq_count
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
  slabLinkPartnerClosedFaceSelectionSelectedPhysical selection =
      slabFaceStrandSelectionCount selection.selected := by
  funext faceId
  unfold slabLinkPartnerClosedFaceSelectionSelectedPhysical
  unfold lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  have hpartition :=
    slabLinkPartnerClosedFaceSelectionCount_add_complement selection faceId
  omega

/-! ## 6. The selected half is an accepted link witness -/

/-- The auxiliary edge labelling carried only by the selected strand
subnetwork: remove every complementary strand from the accepted source. -/
def slabLinkPartnerClosedFaceSelectionSelectedAuxiliary
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) : SlabLabelling :=
  lowerEdgeLabellingBy auxiliary
    (slabLinkPartnerClosedFaceSelectionComplement selection).toMateClosedSelection.drop

/-- **Literal accepted selected subnetwork.**  Complementary mate-closed
removal constructs an actual member of the original-cutoff link fiber over
the selected physical face-count labelling. -/
theorem slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_mem
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    slabLinkPartnerClosedFaceSelectionSelectedAuxiliary selection ∈
      slabLinkFusionWitnesses cutoff extent
        (slabLinkPartnerClosedFaceSelectionSelectedPhysical selection)
        link := by
  let complement := slabLinkPartnerClosedFaceSelectionComplement selection
  change
    lowerEdgeLabellingBy auxiliary
        complement.toMateClosedSelection.drop ∈
      slabLinkFusionWitnesses cutoff extent
        (lowerSlabPhysicalByFaceStrandSelection
          complement.selected)
        link
  have hexternalSlab :=
    @SlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
      cutoff extent physical link auxiliary hmem complement
  have hexternal :
      slabLinkExternalSpins extent
          (lowerSlabPhysicalByFaceStrandSelection complement.selected) link =
        lowerEdgeLabellingBy
          (slabLinkExternalSpins extent physical link)
          complement.toMateClosedSelection.drop := by
    rw [complement.toMateClosedSelection_drop]
    exact hexternalSlab
  exact @SlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem
    cutoff extent physical
    (lowerSlabPhysicalByFaceStrandSelection complement.selected)
    link auxiliary hmem complement hexternal

/-! ## Dependency gates -/

#print axioms boolCountFrom_add_not
#print axioms resolvedNetworkMateClosedSelectionDrop_add_complementDrop
#print axioms resolvedNetworkMateClosedSelectionDrop_vertices_admissible
#print axioms slabLinkPartnerClosedFaceSelectionCount_add_complement
#print axioms slabFaceStrandSelectionCount_eq_selectedByMask
#print axioms lowerSlabPhysicalByFaceStrandSelection_eq_unselectedByMask
#print axioms slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_mem

end YMGap.Continuum.CompactDualSlabSelectionComplement

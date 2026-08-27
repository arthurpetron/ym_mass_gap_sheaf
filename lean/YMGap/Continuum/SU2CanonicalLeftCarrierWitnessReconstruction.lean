/-
# Reconstruct production witnesses from complete SU(2) left carriers

The complete associator matrices use proof-carrying left-tree carriers as
their source bases.  The production slab uses zero-padded auxiliary edge
labellings.  This module gives the converse to the earlier extraction bridge
at the only nontrivial four-dimensional valences: four, five, and six.

Each left carrier writes its successive intermediate twice-spins into the
canonical production coordinates.  Its fusion proofs establish the Boolean
resolver, while bounded physical external spins place every intermediate in
the production `6*K` auxiliary window.  Therefore the reconstructed
labelling is a literal member of the production witness list.

This does not identify a right-tree vector with a left-tree vector.  It is
intended to be composed with a separate finite carrier reindexing.

Constructive contract: explicit functions, finite membership, and natural
arithmetic only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
import YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock

namespace YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

/-! ## 1. Literal zero-padded auxiliary labellings -/

def valenceFourLeftAuxiliary {a b c d : Nat}
    (source : FixedLeftCGChannel a b c d) : EdgeLabelling :=
  fun edge => if edge = 5 then source.intermediate else 0

def valenceFiveLeftAuxiliary {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e) : EdgeLabelling :=
  fun edge =>
    if edge = 6 then source.firstLeft.intermediate
    else if edge = 7 then source.y
    else 0

def valenceSixLeftAuxiliary {a b c d e f : Nat}
    (source : ValenceSixLeftCarrier a b c d e f) : EdgeLabelling :=
  fun edge =>
    if edge = 7 then source.value.firstLeft.intermediate
    else if edge = 8 then source.value.y
    else if edge = 9 then source.index.val
    else 0

/-! ## 2. Exact resolver acceptance -/

theorem valenceFourLeftAuxiliary_allowed
    (external : EdgeLabelling)
    (source : FixedLeftCGChannel
      (external 0) (external 1) (external 2) (external 3)) :
    canonicalLinkConditionalAllowedB 4
        external
        (valenceFourLeftAuxiliary source) = true := by
  rw [canonicalLinkConditionalAllowedB_four]
  simp only [valenceFourLeftAuxiliary, if_pos, Bool.and_eq_true]
  exact ⟨fixedLeft_inner_fusionOK source,
    fixedLeft_outer_fusionOK source⟩

theorem valenceFiveLeftAuxiliary_allowed
    (external : EdgeLabelling)
    (source : ValenceFiveLeftCarrier
      (external 0) (external 1) (external 2) (external 3) (external 4)) :
    canonicalLinkConditionalAllowedB 5
        external
        (valenceFiveLeftAuxiliary source) = true := by
  rw [canonicalLinkConditionalAllowedB_five]
  simp only [valenceFiveLeftAuxiliary, if_pos, Bool.and_eq_true]
  exact ⟨fixedLeft_inner_fusionOK source.firstLeft,
    fixedLeft_outer_fusionOK source.firstLeft,
    source.suffix.fusionOK⟩

theorem valenceSixLeftAuxiliary_allowed
    (external : EdgeLabelling)
    (source : ValenceSixLeftCarrier
      (external 0) (external 1) (external 2) (external 3)
      (external 4) (external 5)) :
    canonicalLinkConditionalAllowedB 6
        external
        (valenceSixLeftAuxiliary source) = true := by
  rw [canonicalLinkConditionalAllowedB_six]
  simp only [externalSpinsOfList, List.getD_cons_zero,
    List.getD_cons_succ, valenceSixLeftAuxiliary, if_pos,
    Bool.and_eq_true]
  have hsuffix := (List.mem_filter.mp source.index.property).2
  exact ⟨fixedLeft_inner_fusionOK source.value.firstLeft,
    fixedLeft_outer_fusionOK source.value.firstLeft,
    source.value.suffix.fusionOK, hsuffix⟩

/-! ## 3. The production cutoff contains every reconstructed label -/

private theorem valenceFourLeftAuxiliary_mem_bounded
    {K a b c d : Nat} (ha : a ≤ K) (hb : b ≤ K)
    (source : FixedLeftCGChannel a b c d) :
    valenceFourLeftAuxiliary source ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates 4) := by
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    rw [show canonicalUsedAuxiliaryCoordinates 4 = [5] by rfl] at hedge
    have hedgeEq : edge = 5 := by simpa using hedge
    subst edge
    have hintermediate := fusionOK_output_le_add
      (fixedLeft_inner_fusionOK source)
    simp only [valenceFourLeftAuxiliary, if_pos]
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  · intro edge hedge
    have hne : edge ≠ 5 := by
      intro heq
      subst edge
      apply hedge
      rw [show canonicalUsedAuxiliaryCoordinates 4 = [5] by rfl]
      simp
    simp [valenceFourLeftAuxiliary, hne]

private theorem valenceFiveLeftAuxiliary_mem_bounded
    {K a b c d e : Nat} (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K)
    (source : ValenceFiveLeftCarrier a b c d e) :
    valenceFiveLeftAuxiliary source ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates 5) := by
  have hx := fusionOK_output_le_add
    (fixedLeft_inner_fusionOK source.firstLeft)
  have hy := fusionOK_output_le_add
    (fixedLeft_outer_fusionOK source.firstLeft)
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    rw [show canonicalUsedAuxiliaryCoordinates 5 = [6, 7] by rfl] at hedge
    simp at hedge
    rcases hedge with heq | heq
    · subst edge
      simp [valenceFiveLeftAuxiliary]
      unfold linkAuxiliaryCutoff linkIncidenceBound
      omega
    · subst edge
      simp [valenceFiveLeftAuxiliary]
      unfold linkAuxiliaryCutoff linkIncidenceBound
      omega
  · intro edge hedge
    have hne6 : edge ≠ 6 := by
      intro heq
      subst edge
      apply hedge
      rw [show canonicalUsedAuxiliaryCoordinates 5 = [6, 7] by rfl]
      simp
    have hne7 : edge ≠ 7 := by
      intro heq
      subst edge
      apply hedge
      rw [show canonicalUsedAuxiliaryCoordinates 5 = [6, 7] by rfl]
      simp
    simp [valenceFiveLeftAuxiliary, hne6, hne7]

private theorem valenceSixLeftAuxiliary_mem_bounded
    {K a b c d e f : Nat}
    (ha : a ≤ K) (hb : b ≤ K) (hc : c ≤ K) (hd : d ≤ K)
    (source : ValenceSixLeftCarrier a b c d e f) :
    valenceSixLeftAuxiliary source ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates 6) := by
  have hx := fusionOK_output_le_add
    (fixedLeft_inner_fusionOK source.value.firstLeft)
  have hy := fusionOK_output_le_add
    (fixedLeft_outer_fusionOK source.value.firstLeft)
  have hz := fusionOK_output_le_add source.value.suffix.fusionOK
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    rw [show canonicalUsedAuxiliaryCoordinates 6 = [7, 8, 9] by rfl] at hedge
    simp at hedge
    rcases hedge with heq | heq | heq
    · subst edge
      simp [valenceSixLeftAuxiliary]
      unfold linkAuxiliaryCutoff linkIncidenceBound
      omega
    · subst edge
      simp [valenceSixLeftAuxiliary]
      unfold linkAuxiliaryCutoff linkIncidenceBound
      omega
    · subst edge
      simp [valenceSixLeftAuxiliary]
      unfold linkAuxiliaryCutoff linkIncidenceBound
      omega
  · intro edge hedge
    have hne7 : edge ≠ 7 := by
      intro heq
      subst edge
      apply hedge
      rw [show canonicalUsedAuxiliaryCoordinates 6 = [7, 8, 9] by rfl]
      simp
    have hne8 : edge ≠ 8 := by
      intro heq
      subst edge
      apply hedge
      rw [show canonicalUsedAuxiliaryCoordinates 6 = [7, 8, 9] by rfl]
      simp
    have hne9 : edge ≠ 9 := by
      intro heq
      subst edge
      apply hedge
      rw [show canonicalUsedAuxiliaryCoordinates 6 = [7, 8, 9] by rfl]
      simp
    simp [valenceSixLeftAuxiliary, hne7, hne8, hne9]

/-! ## 4. Literal canonical witness-list membership -/

theorem valenceFourLeftAuxiliary_mem_canonical
    {K : Nat} (external : EdgeLabelling)
    (ha : external 0 ≤ K) (hb : external 1 ≤ K)
    (source : FixedLeftCGChannel
      (external 0) (external 1) (external 2) (external 3)) :
    valenceFourLeftAuxiliary source ∈
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates 4)).filter
          (canonicalLinkConditionalAllowedB 4 external) := by
  exact List.mem_filter.mpr
    ⟨valenceFourLeftAuxiliary_mem_bounded ha hb source,
      valenceFourLeftAuxiliary_allowed external source⟩

theorem valenceFiveLeftAuxiliary_mem_canonical
    {K : Nat} (external : EdgeLabelling)
    (ha : external 0 ≤ K) (hb : external 1 ≤ K)
    (hc : external 2 ≤ K)
    (source : ValenceFiveLeftCarrier
      (external 0) (external 1) (external 2) (external 3) (external 4)) :
    valenceFiveLeftAuxiliary source ∈
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates 5)).filter
          (canonicalLinkConditionalAllowedB 5 external) := by
  exact List.mem_filter.mpr
    ⟨valenceFiveLeftAuxiliary_mem_bounded ha hb hc source,
      valenceFiveLeftAuxiliary_allowed external source⟩

theorem valenceSixLeftAuxiliary_mem_canonical
    {K : Nat} (external : EdgeLabelling)
    (ha : external 0 ≤ K) (hb : external 1 ≤ K)
    (hc : external 2 ≤ K) (hd : external 3 ≤ K)
    (source : ValenceSixLeftCarrier
      (external 0) (external 1) (external 2) (external 3)
      (external 4) (external 5)) :
    valenceSixLeftAuxiliary source ∈
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates 6)).filter
          (canonicalLinkConditionalAllowedB 6 external) := by
  exact List.mem_filter.mpr
    ⟨valenceSixLeftAuxiliary_mem_bounded ha hb hc hd source,
      valenceSixLeftAuxiliary_allowed external source⟩

/-! ## 5. External-spin bounds at an actual slab link -/

theorem slabLinkExternalSpin_le
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (hbounded : SlabFaceLabellingBounded K extent physical)
    (position : Nat)
    (hposition : position < (slabIncidentPlaqIds extent link).length) :
    slabLinkExternalSpins extent physical link position ≤ K := by
  unfold slabLinkExternalSpins
  rw [externalSpinsOfList_map_get
    (slabIncidentPlaqIds extent link) physical ⟨position, hposition⟩]
  exact hbounded _
    (slabIncidentPlaqId_physical
      (List.get_mem _ ⟨position, hposition⟩))

/-! ## 6. Reconstructed witnesses at actual slab links -/

theorem valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (hbounded : SlabFaceLabellingBounded K extent physical)
    (hdegree : (slabIncidentPlaqIds extent link).length = 4)
    (source : FixedLeftCGChannel
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)) :
    valenceFourLeftAuxiliary source ∈
      slabLinkFusionWitnesses K extent physical link := by
  have h0 := slabLinkExternalSpin_le (link := link) hbounded 0 (by omega)
  have h1 := slabLinkExternalSpin_le (link := link) hbounded 1 (by omega)
  unfold slabLinkFusionWitnesses
  rw [hdegree]
  exact valenceFourLeftAuxiliary_mem_canonical
    (slabLinkExternalSpins extent physical link) h0 h1 source

theorem valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (hbounded : SlabFaceLabellingBounded K extent physical)
    (hdegree : (slabIncidentPlaqIds extent link).length = 5)
    (source : ValenceFiveLeftCarrier
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)
      ((slabLinkExternalSpins extent physical link) 4)) :
    valenceFiveLeftAuxiliary source ∈
      slabLinkFusionWitnesses K extent physical link := by
  have h0 := slabLinkExternalSpin_le (link := link) hbounded 0 (by omega)
  have h1 := slabLinkExternalSpin_le (link := link) hbounded 1 (by omega)
  have h2 := slabLinkExternalSpin_le (link := link) hbounded 2 (by omega)
  unfold slabLinkFusionWitnesses
  rw [hdegree]
  exact valenceFiveLeftAuxiliary_mem_canonical
    (slabLinkExternalSpins extent physical link) h0 h1 h2 source

theorem valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (hbounded : SlabFaceLabellingBounded K extent physical)
    (hdegree : (slabIncidentPlaqIds extent link).length = 6)
    (source : ValenceSixLeftCarrier
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)
      ((slabLinkExternalSpins extent physical link) 4)
      ((slabLinkExternalSpins extent physical link) 5)) :
    valenceSixLeftAuxiliary source ∈
      slabLinkFusionWitnesses K extent physical link := by
  have h0 := slabLinkExternalSpin_le (link := link) hbounded 0 (by omega)
  have h1 := slabLinkExternalSpin_le (link := link) hbounded 1 (by omega)
  have h2 := slabLinkExternalSpin_le (link := link) hbounded 2 (by omega)
  have h3 := slabLinkExternalSpin_le (link := link) hbounded 3 (by omega)
  unfold slabLinkFusionWitnesses
  rw [hdegree]
  exact valenceSixLeftAuxiliary_mem_canonical
    (slabLinkExternalSpins extent physical link) h0 h1 h2 h3 source

#print axioms valenceFourLeftAuxiliary_allowed
#print axioms valenceFiveLeftAuxiliary_allowed
#print axioms valenceSixLeftAuxiliary_allowed
#print axioms valenceFourLeftAuxiliary_mem_canonical
#print axioms valenceFiveLeftAuxiliary_mem_canonical
#print axioms valenceSixLeftAuxiliary_mem_canonical
#print axioms slabLinkExternalSpin_le
#print axioms valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
#print axioms valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
#print axioms valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses

end YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction

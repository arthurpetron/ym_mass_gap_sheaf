/-
# Symbolic fixed-incidence channel carrier for adjacent-even gluing

The remaining trajectory-gluing theorem needs one finite carrier containing
all channel fields on the literal fixed-face/link incidences.  The carrier is
defined by the existing bounded-labelling recursion, but is used only
symbolically: no list length or Cartesian family is evaluated in this file.

The generic completeness theorem below complements
`boundedLabellingsOn_sound`.  A bounded labelling supported on a noduplicated
key list occurs in the recursively generated carrier.  This lets later proofs
introduce canonical incoming, outgoing, and glue fields without choosing a
global decidable equality on function spaces.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge

/-! ## 1. Constructive completeness of finite bounded labellings -/

/-- A labelling bounded on a noduplicated key list and zero off that list is
present in `boundedLabellingsOn`.  The proof follows the defining recursion
and never searches a function-valued list. -/
theorem boundedLabellingsOn_complete_supported
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (label : A → Nat),
      keys.Nodup →
      (∀ key, key ∈ keys → label key ≤ cutoff) →
      (∀ key, key ∉ keys → label key = 0) →
      label ∈ boundedLabellingsOn cutoff keys
  | [], label, _, _, hsupport => by
      have heq : label = zeroLabellingOn := by
        funext key
        exact hsupport key (by simp)
      simpa [boundedLabellingsOn] using heq
  | head :: rest, label, hnodup, hbounded, hsupport => by
      have hparts := List.nodup_cons.mp hnodup
      let tailLabel : A → Nat := setLabelOn label head 0
      have htailBounded : ∀ key, key ∈ rest →
          tailLabel key ≤ cutoff := by
        intro key hkey
        have hne : key ≠ head := by
          intro heq
          exact hparts.1 (heq ▸ hkey)
        rw [show tailLabel key = label key by
          simp [tailLabel, setLabelOn, hne]]
        exact hbounded key (List.mem_cons_of_mem head hkey)
      have htailSupported : ∀ key, key ∉ rest →
          tailLabel key = 0 := by
        intro key hkey
        by_cases heq : key = head
        · subst key
          simp [tailLabel, setLabelOn]
        · rw [show tailLabel key = label key by
            simp [tailLabel, setLabelOn, heq]]
          exact hsupport key (by simp [heq, hkey])
      have htailMember : tailLabel ∈
          boundedLabellingsOn cutoff rest :=
        boundedLabellingsOn_complete_supported cutoff rest tailLabel
          hparts.2 htailBounded htailSupported
      apply List.mem_flatMap.mpr
      refine ⟨label head, List.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_iff.mpr
          (hbounded head List.mem_cons_self)
      · apply List.mem_map.mpr
        refine ⟨tailLabel, htailMember, ?_⟩
        funext key
        by_cases heq : key = head
        · subst key
          simp [tailLabel, setLabelOn]
        · simp [tailLabel, setLabelOn, heq]

private theorem list_getD_mem_or_eq_fallback
    {A : Type} (fallback : A) : ∀ (items : List A) (index : Nat),
    items.getD index fallback ∈ items ∨
      items.getD index fallback = fallback
  | [], _ => Or.inr rfl
  | head :: tail, 0 => Or.inl List.mem_cons_self
  | head :: tail, index + 1 => by
      simp only [List.getD_cons_succ]
      rcases list_getD_mem_or_eq_fallback fallback tail index with
        hmem | heq
      · exact Or.inl (List.mem_cons_of_mem head hmem)
      · exact Or.inr heq

/-- Membership in a finite list supplies a bounded `getD` index without any
decidable equality or search on the element type. -/
theorem exists_getD_eq_of_mem
    {A : Type} (fallback target : A) : ∀ (items : List A),
    target ∈ items →
      ∃ index, index < items.length ∧
        items.getD index fallback = target
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · refine ⟨0, by simp, ?_⟩
        simp [heq]
      · obtain ⟨index, hindex, hgetD⟩ :=
          exists_getD_eq_of_mem fallback target tail htail
        refine ⟨index + 1, by simp; omega, ?_⟩
        simpa only [List.getD_cons_succ] using hgetD

/-! ## 2. Canonical symbolic fixed-incidence carrier -/

/-- All channel assignments on the literal face/link incidence list, bounded
by the production auxiliary cutoff.  This definition must remain symbolic. -/
def adjacentEvenFixedIncidenceChannelAssignments
    (K radius : Nat) : List (FixedFaceLinkIncidence → Nat) :=
  boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)

/-- Symbolic cardinality of the fixed-incidence carrier.  No theorem in this
file evaluates this length. -/
def adjacentEvenFixedIncidenceMiddleCount
    (K radius : Nat) : Nat :=
  (adjacentEvenFixedIncidenceChannelAssignments K radius).length

/-- Zero-padded lookup in the symbolic incidence carrier. -/
def adjacentEvenFixedIncidenceChannelAssignmentAt
    (K radius index : Nat) : FixedFaceLinkIncidence → Nat :=
  (adjacentEvenFixedIncidenceChannelAssignments K radius).getD index
    (zeroLabellingOn : FixedFaceLinkIncidence → Nat)

/-- Extend an incidence assignment to a face-dependent channel field, setting
all nonphysical face/link pairs to zero. -/
def adjacentEvenFixedIncidenceAssignmentField
    (radius : Nat) (assignment : FixedFaceLinkIncidence → Nat) :
    FixedFaceChannelField :=
  fun id link =>
    if (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius then
      assignment (id, link)
    else 0

/-- The channel field carried by a symbolic middle index. -/
def adjacentEvenFixedIncidenceMiddleField
    (K radius index : Nat) : FixedFaceChannelField :=
  adjacentEvenFixedIncidenceAssignmentField radius
    (adjacentEvenFixedIncidenceChannelAssignmentAt K radius index)

theorem adjacentEvenFixedIncidenceAssignmentField_of_mem
    (radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    {id : Nat} {link : Z4Link}
    (hincidence : (id, link) ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenFixedIncidenceAssignmentField radius assignment id link =
      assignment (id, link) := by
  simp [adjacentEvenFixedIncidenceAssignmentField, hincidence]

theorem adjacentEvenFixedIncidenceAssignmentField_of_not_mem
    (radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    {id : Nat} {link : Z4Link}
    (hincidence : (id, link) ∉
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenFixedIncidenceAssignmentField radius assignment id link = 0 := by
  simp [adjacentEvenFixedIncidenceAssignmentField, hincidence]

/-- Every symbolic middle field lies in the production channel window,
including zero-padded indices and nonphysical incidence pairs. -/
theorem adjacentEvenFixedIncidenceMiddleField_le
    (K radius index id : Nat) (link : Z4Link) :
    adjacentEvenFixedIncidenceMiddleField K radius index id link ≤
      linkAuxiliaryCutoff K := by
  let assignments := adjacentEvenFixedIncidenceChannelAssignments K radius
  let assignment := adjacentEvenFixedIncidenceChannelAssignmentAt K radius index
  have hlookup : assignment ∈ assignments ∨
      assignment = (zeroLabellingOn : FixedFaceLinkIncidence → Nat) := by
    exact list_getD_mem_or_eq_fallback
      (zeroLabellingOn : FixedFaceLinkIncidence → Nat)
      assignments index
  unfold adjacentEvenFixedIncidenceMiddleField
    adjacentEvenFixedIncidenceAssignmentField
  by_cases hincidence : (id, link) ∈
      adjacentEvenFixedFaceMajorIncidences radius
  · rw [if_pos hincidence]
    change assignment (id, link) ≤ linkAuxiliaryCutoff K
    rcases hlookup with hmember | hzero
    · exact boundedLabellingsOn_sound
        (linkAuxiliaryCutoff K)
        (adjacentEvenFixedFaceMajorIncidences radius)
        assignment hmember (id, link) hincidence
    · rw [hzero]
      exact Nat.zero_le _
  · rw [if_neg hincidence]
    exact Nat.zero_le _

/-- Any bounded zero-supported incidence assignment belongs to the canonical
symbolic middle carrier. -/
theorem adjacentEvenFixedIncidenceChannelAssignment_mem
    (K radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    (hbounded : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence ≤ linkAuxiliaryCutoff K)
    (hsupported : ∀ incidence,
      incidence ∉ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence = 0) :
    assignment ∈ adjacentEvenFixedIncidenceChannelAssignments K radius := by
  exact boundedLabellingsOn_complete_supported
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)
    assignment
    (adjacentEvenFixedFaceMajorIncidences_nodup radius)
    hbounded hsupported

/-- A bounded supported assignment is realized by an actual natural-number
middle index.  This is proof-local existence, not a global search function on
the function-valued carrier. -/
theorem adjacentEvenFixedIncidenceChannelAssignment_realized
    (K radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    (hbounded : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence ≤ linkAuxiliaryCutoff K)
    (hsupported : ∀ incidence,
      incidence ∉ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence = 0) :
    ∃ middle,
      middle < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      adjacentEvenFixedIncidenceChannelAssignmentAt K radius middle =
        assignment := by
  have hmember := adjacentEvenFixedIncidenceChannelAssignment_mem
    K radius assignment hbounded hsupported
  obtain ⟨middle, hmiddle, hlookup⟩ := exists_getD_eq_of_mem
    (zeroLabellingOn : FixedFaceLinkIncidence → Nat)
    assignment
    (adjacentEvenFixedIncidenceChannelAssignments K radius)
    hmember
  exact ⟨middle, hmiddle, hlookup⟩

/-- Field-valued form of `adjacentEvenFixedIncidenceChannelAssignment_realized`:
the realized middle field agrees with the assignment on every literal fixed
incidence. -/
theorem adjacentEvenFixedIncidenceAssignmentField_realized
    (K radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    (hbounded : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence ≤ linkAuxiliaryCutoff K)
    (hsupported : ∀ incidence,
      incidence ∉ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence = 0) :
    ∃ middle,
      middle < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      ∀ id link,
        (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
        adjacentEvenFixedIncidenceMiddleField K radius middle id link =
          assignment (id, link) := by
  obtain ⟨middle, hmiddle, hlookup⟩ :=
    adjacentEvenFixedIncidenceChannelAssignment_realized
      K radius assignment hbounded hsupported
  refine ⟨middle, hmiddle, ?_⟩
  intro id link hincidence
  unfold adjacentEvenFixedIncidenceMiddleField
  rw [hlookup]
  exact adjacentEvenFixedIncidenceAssignmentField_of_mem
    radius assignment hincidence

/-! ## 3. Canonical incoming and outgoing trajectory fields -/

/-- Every predecessor selected by a finite trajectory word is either the
initial channel or one of the word channels. -/
theorem fixedIdIncomingChannel_le
    (cutoff : Nat) (channel : Nat → Nat) :
    ∀ (start query : Nat) (ids : List Nat),
      start ≤ cutoff →
      (∀ id, id ∈ ids → channel id ≤ cutoff) →
      fixedIdIncomingChannel channel start query ids ≤ cutoff
  | start, _, [], hstart, _ => hstart
  | start, query, head :: rest, hstart, hchannel => by
      by_cases heq : query = head
      · subst query
        simpa using hstart
      · change (if query = head then start else
          fixedIdIncomingChannel channel (channel head) query rest) ≤ cutoff
        rw [if_neg heq]
        exact fixedIdIncomingChannel_le cutoff channel
          (channel head) query rest
          (hchannel head List.mem_cons_self)
          (fun id hid => hchannel id (List.mem_cons_of_mem head hid))

/-- The outgoing trajectory channel, zero-extended away from the physical
fixed-incidence list. -/
def adjacentEvenTrajectoryOutgoingIncidenceAssignment
    (radius : Nat) (trajectory : FixedIncidenceTrajectoryState) :
    FixedFaceLinkIncidence → Nat :=
  fun incidence =>
    if incidence ∈ adjacentEvenFixedFaceMajorIncidences radius then
      trajectory incidence.2 incidence.1
    else 0

/-- The incoming predecessor channel, zero-extended away from the physical
fixed-incidence list. -/
def adjacentEvenTrajectoryIncomingIncidenceAssignment
    (radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    FixedFaceLinkIncidence → Nat :=
  fun incidence =>
    if incidence ∈ adjacentEvenFixedFaceMajorIncidences radius then
      adjacentEvenIncidenceIncomingChannel radius source trajectory incidence
    else 0

theorem adjacentEvenTrajectoryOutgoingIncidenceAssignment_le
    {K radius : Nat} {trajectory : FixedIncidenceTrajectoryState}
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius)
    (incidence : FixedFaceLinkIncidence)
    (hincidence : incidence ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenTrajectoryOutgoingIncidenceAssignment
        radius trajectory incidence ≤ linkAuxiliaryCutoff K := by
  unfold adjacentEvenTrajectoryOutgoingIncidenceAssignment
  rw [if_pos hincidence]
  have hlinkMajor : incidence ∈
      adjacentEvenFixedLinkMajorIncidences radius :=
    adjacentEvenFixedIncidence_mem_iff.mp hincidence
  have hparts :=
    mem_adjacentEvenFixedLinkMajorIncidences.mp hlinkMajor
  have hchoice : trajectory incidence.2 ∈
      adjacentEvenFixedLinkTrajectoryOptions K radius incidence.2 :=
    heterogeneousChoices_sound
      (zeroLabellingOn : Nat → Nat)
      (adjacentEvenFixedLinkTrajectoryOptions K radius)
      (adjacentEvenFixedLinks radius) trajectory
      (adjacentEvenFixedLinks_nodup radius)
      htrajectory incidence.2 hparts.1
  unfold adjacentEvenFixedLinkTrajectoryOptions at hchoice
  exact boundedLabellingsOn_sound
    (linkAuxiliaryCutoff K)
    (adjacentEvenIncidentFixedFaceIds radius incidence.2)
    (trajectory incidence.2) hchoice incidence.1 hparts.2

theorem adjacentEvenTrajectoryIncomingIncidenceAssignment_le
    {K radius : Nat} {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius)
    (incidence : FixedFaceLinkIncidence)
    (hincidence : incidence ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenTrajectoryIncomingIncidenceAssignment
        radius source trajectory incidence ≤ linkAuxiliaryCutoff K := by
  unfold adjacentEvenTrajectoryIncomingIncidenceAssignment
  rw [if_pos hincidence]
  have hlinkMajor : incidence ∈
      adjacentEvenFixedLinkMajorIncidences radius :=
    adjacentEvenFixedIncidence_mem_iff.mp hincidence
  have hparts :=
    mem_adjacentEvenFixedLinkMajorIncidences.mp hlinkMajor
  have hchoice : trajectory incidence.2 ∈
      adjacentEvenFixedLinkTrajectoryOptions K radius incidence.2 :=
    heterogeneousChoices_sound
      (zeroLabellingOn : Nat → Nat)
      (adjacentEvenFixedLinkTrajectoryOptions K radius)
      (adjacentEvenFixedLinks radius) trajectory
      (adjacentEvenFixedLinks_nodup radius)
      htrajectory incidence.2 hparts.1
  unfold adjacentEvenIncidenceIncomingChannel
  apply fixedIdIncomingChannel_le
  · exact hsource incidence.2 hparts.1
  · intro id hid
    unfold adjacentEvenFixedLinkTrajectoryOptions at hchoice
    exact boundedLabellingsOn_sound
      (linkAuxiliaryCutoff K)
      (adjacentEvenIncidentFixedFaceIds radius incidence.2)
      (trajectory incidence.2) hchoice id hid

theorem adjacentEvenTrajectoryOutgoingIncidenceAssignment_mem
    {K radius : Nat} {trajectory : FixedIncidenceTrajectoryState}
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory ∈
      adjacentEvenFixedIncidenceChannelAssignments K radius := by
  apply adjacentEvenFixedIncidenceChannelAssignment_mem
  · exact adjacentEvenTrajectoryOutgoingIncidenceAssignment_le htrajectory
  · intro incidence hincidence
    simp [adjacentEvenTrajectoryOutgoingIncidenceAssignment, hincidence]

theorem adjacentEvenTrajectoryIncomingIncidenceAssignment_mem
    {K radius : Nat} {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    adjacentEvenTrajectoryIncomingIncidenceAssignment
        radius source trajectory ∈
      adjacentEvenFixedIncidenceChannelAssignments K radius := by
  apply adjacentEvenFixedIncidenceChannelAssignment_mem
  · exact adjacentEvenTrajectoryIncomingIncidenceAssignment_le
      hsource htrajectory
  · intro incidence hincidence
    simp [adjacentEvenTrajectoryIncomingIncidenceAssignment, hincidence]

/-- Every bounded outgoing trajectory field is represented by an actual
middle index, with exact agreement on the physical fixed incidences. -/
theorem adjacentEvenTrajectoryOutgoingMiddleField_realized
    {K radius : Nat} {trajectory : FixedIncidenceTrajectoryState}
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    ∃ middle,
      middle < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      ∀ id link,
        (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
        adjacentEvenFixedIncidenceMiddleField K radius middle id link =
          adjacentEvenTrajectoryOutgoingField trajectory id link := by
  obtain ⟨middle, hmiddle, hfield⟩ :=
    adjacentEvenFixedIncidenceAssignmentField_realized
      K radius
      (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)
      (adjacentEvenTrajectoryOutgoingIncidenceAssignment_le htrajectory)
      (fun incidence hincidence => by
        simp [adjacentEvenTrajectoryOutgoingIncidenceAssignment, hincidence])
  refine ⟨middle, hmiddle, ?_⟩
  intro id link hincidence
  rw [hfield id link hincidence]
  simp [adjacentEvenTrajectoryOutgoingIncidenceAssignment,
    adjacentEvenTrajectoryOutgoingField, hincidence]

/-- Every bounded incoming predecessor field is represented by an actual
middle index, with exact agreement on the physical fixed incidences. -/
theorem adjacentEvenTrajectoryIncomingMiddleField_realized
    {K radius : Nat} {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    ∃ middle,
      middle < adjacentEvenFixedIncidenceMiddleCount K radius ∧
      ∀ id link,
        (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
        adjacentEvenFixedIncidenceMiddleField K radius middle id link =
          adjacentEvenTrajectoryIncomingField
            radius source trajectory id link := by
  obtain ⟨middle, hmiddle, hfield⟩ :=
    adjacentEvenFixedIncidenceAssignmentField_realized
      K radius
      (adjacentEvenTrajectoryIncomingIncidenceAssignment
        radius source trajectory)
      (adjacentEvenTrajectoryIncomingIncidenceAssignment_le
        hsource htrajectory)
      (fun incidence hincidence => by
        simp [adjacentEvenTrajectoryIncomingIncidenceAssignment, hincidence])
  refine ⟨middle, hmiddle, ?_⟩
  intro id link hincidence
  rw [hfield id link hincidence]
  simp [adjacentEvenTrajectoryIncomingIncidenceAssignment,
    adjacentEvenTrajectoryIncomingField, hincidence]

/-- On every literal fixed incidence, the canonical outgoing assignment field
is exactly the outgoing field used by the mixed trajectory kernel. -/
theorem adjacentEvenTrajectoryOutgoingAssignmentField_eq
    (radius : Nat) (trajectory : FixedIncidenceTrajectoryState)
    {id : Nat} {link : Z4Link}
    (hincidence : (id, link) ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenFixedIncidenceAssignmentField radius
        (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)
        id link =
      adjacentEvenTrajectoryOutgoingField trajectory id link := by
  simp [adjacentEvenFixedIncidenceAssignmentField,
    adjacentEvenTrajectoryOutgoingIncidenceAssignment,
    adjacentEvenTrajectoryOutgoingField, hincidence]

/-- On every literal fixed incidence, the canonical incoming assignment field
is exactly the incoming field used by the mixed trajectory kernel. -/
theorem adjacentEvenTrajectoryIncomingAssignmentField_eq
    (radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState)
    {id : Nat} {link : Z4Link}
    (hincidence : (id, link) ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenFixedIncidenceAssignmentField radius
        (adjacentEvenTrajectoryIncomingIncidenceAssignment
          radius source trajectory)
        id link =
      adjacentEvenTrajectoryIncomingField radius source trajectory id link := by
  simp [adjacentEvenFixedIncidenceAssignmentField,
    adjacentEvenTrajectoryIncomingIncidenceAssignment,
    adjacentEvenTrajectoryIncomingField, hincidence]

#print axioms boundedLabellingsOn_complete_supported
#print axioms adjacentEvenFixedIncidenceMiddleField_le
#print axioms adjacentEvenFixedIncidenceChannelAssignment_mem
#print axioms adjacentEvenFixedIncidenceChannelAssignment_realized
#print axioms adjacentEvenFixedIncidenceAssignmentField_realized
#print axioms fixedIdIncomingChannel_le
#print axioms adjacentEvenTrajectoryOutgoingIncidenceAssignment_mem
#print axioms adjacentEvenTrajectoryIncomingIncidenceAssignment_mem
#print axioms adjacentEvenTrajectoryOutgoingMiddleField_realized
#print axioms adjacentEvenTrajectoryIncomingMiddleField_realized
#print axioms adjacentEvenTrajectoryOutgoingAssignmentField_eq
#print axioms adjacentEvenTrajectoryIncomingAssignmentField_eq

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier

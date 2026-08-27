/-
# A deterministic accepted paired-component peel step

Fix a list of physical faces, in its existing order.  This module scans that
list from left to right, chooses the first face still positive in either
accepted replica, and chooses the left replica whenever both are positive.
Thus neither the root face nor the replica contributes a branching factor.

The selected canonical component peel stays in the accepted paired carrier,
removes its exact positive peel size from total pair mass, and strictly
decreases that mass.  Failure to select a step is equivalent to both replicas
being zero on every face of the fixed list.

Constructive contract: structural list recursion, decidable natural-number
positivity, and exact accepted peel identities only; no choice, `Classical`,
`sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedPeel

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. One accepted left-or-right peel -/

/-- A rooted accepted peel of exactly one replica.  The right constructor
also records that the left replica is zero at the selected face; this makes
the left-first convention explicit data rather than prose. -/
inductive SlabAcceptedPairedPeelChoice
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) : Type
  | left
      (faceId : Nat)
      (face_mem_physical : faceId ∈ slabPhysicalFaceEdges D.extent)
      (positive : 0 < state.1.1.1 faceId)
  | right
      (faceId : Nat)
      (face_mem_physical : faceId ∈ slabPhysicalFaceEdges D.extent)
      (left_zero : state.1.1.1 faceId = 0)
      (positive : 0 < state.2.1.1 faceId)

def SlabAcceptedPairedPeelChoice.faceId
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) : Nat :=
  match choice with
  | .left faceId _ _ => faceId
  | .right faceId _ _ _ => faceId

/-- Apply the selected accepted component peel to exactly one replica. -/
def SlabAcceptedPairedPeelChoice.lowerState
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    SlabAcceptedTwoReplicaState D :=
  match choice with
  | .left faceId hface hpositive =>
      slabAcceptedTwoReplicaStateLowerLeftAt
        state faceId hface hpositive
  | .right faceId hface _ hpositive =>
      slabAcceptedTwoReplicaStateLowerRightAt
        state faceId hface hpositive

/-- Physical multiplicity removed by the selected one-replica peel. -/
def SlabAcceptedPairedPeelChoice.peelSize
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) : Nat :=
  match choice with
  | .left faceId hface hpositive =>
      acceptedExpandedSourcePeelSizeAt
        D faceId hface state.1 hpositive
  | .right faceId hface _ hpositive =>
      acceptedExpandedSourcePeelSizeAt
        D faceId hface state.2 hpositive

/-- Exact pair-mass conservation for either selected side. -/
theorem SlabAcceptedPairedPeelChoice.lowerState_mass_add_peelSize
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    slabAcceptedTwoReplicaStateMass choice.lowerState + choice.peelSize =
      slabAcceptedTwoReplicaStateMass state := by
  cases choice with
  | left faceId hface hpositive =>
      exact slabAcceptedTwoReplicaStateLowerLeftAt_mass_add_peelSize
        state faceId hface hpositive
  | right faceId hface _ hpositive =>
      exact slabAcceptedTwoReplicaStateLowerRightAt_mass_add_peelSize
        state faceId hface hpositive

/-- Every selected canonical peel removes positive mass. -/
theorem SlabAcceptedPairedPeelChoice.peelSize_pos
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    0 < choice.peelSize := by
  cases choice with
  | left faceId hface hpositive =>
      exact SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos
        (acceptedExpandedSourceRootSeed
          D faceId hface state.1 hpositive)
  | right faceId hface _ hpositive =>
      exact SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos
        (acceptedExpandedSourceRootSeed
          D faceId hface state.2 hpositive)

/-- Consequently every selected step strictly decreases total pair mass. -/
theorem SlabAcceptedPairedPeelChoice.lowerState_mass_lt
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    slabAcceptedTwoReplicaStateMass choice.lowerState <
      slabAcceptedTwoReplicaStateMass state := by
  have hmass := choice.lowerState_mass_add_peelSize
  have hpositive := choice.peelSize_pos
  omega

/-! ## 2. First remaining face, with a left-first side convention -/

/-- Scan a fixed physical-face list in order.  Select the first face positive
in either replica, and select the left replica first when both are positive. -/
def slabAcceptedPairCanonicalChoice?
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    (faces : List Nat) →
      (∀ faceId, faceId ∈ faces →
        faceId ∈ slabPhysicalFaceEdges D.extent) →
      Option (SlabAcceptedPairedPeelChoice D state)
  | [], _ => none
  | faceId :: rest, hphysical =>
      if hleft : 0 < state.1.1.1 faceId then
        some (.left faceId
          (hphysical faceId List.mem_cons_self) hleft)
      else if hright : 0 < state.2.1.1 faceId then
        some (.right faceId
          (hphysical faceId List.mem_cons_self)
          (by omega) hright)
      else
        slabAcceptedPairCanonicalChoice? D state rest
          (fun next hnext =>
            hphysical next (List.mem_cons_of_mem faceId hnext))

/-- Every returned root is literally a member of the scanned face list. -/
theorem slabAcceptedPairCanonicalChoice?_some_face_mem
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    ∀ (faces : List Nat)
      (hphysical : ∀ faceId, faceId ∈ faces →
        faceId ∈ slabPhysicalFaceEdges D.extent)
      (choice : SlabAcceptedPairedPeelChoice D state),
      slabAcceptedPairCanonicalChoice? D state faces hphysical =
          some choice →
        choice.faceId ∈ faces
  | [], _, _, hchoice => by cases hchoice
  | head :: tail, hphysical, choice, hchoice => by
      by_cases hleft : 0 < state.1.1.1 head
      · have heq : choice = .left head
            (hphysical head List.mem_cons_self) hleft := by
          have hsome :
              some (.left head
                (hphysical head List.mem_cons_self) hleft) =
                some choice := by
            simpa [slabAcceptedPairCanonicalChoice?, hleft] using hchoice
          exact (Option.some.inj hsome).symm
        subst choice
        exact List.mem_cons_self
      · by_cases hright : 0 < state.2.1.1 head
        · have heq : choice = .right head
              (hphysical head List.mem_cons_self) (by omega) hright := by
            have hsome :
                some (.right head
                  (hphysical head List.mem_cons_self)
                    (by omega) hright) = some choice := by
              simpa [slabAcceptedPairCanonicalChoice?, hleft, hright]
                using hchoice
            exact (Option.some.inj hsome).symm
          subst choice
          exact List.mem_cons_self
        · apply List.mem_cons_of_mem head
          apply slabAcceptedPairCanonicalChoice?_some_face_mem
            D state tail
              (fun next hnext =>
                hphysical next (List.mem_cons_of_mem head hnext))
              choice
          simpa [slabAcceptedPairCanonicalChoice?, hleft, hright]
            using hchoice

/-- If the deterministic scan returns no peel, both accepted replicas are
zero at every face in the fixed list. -/
theorem slabAcceptedPairCanonicalChoice?_eq_none_zero
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    ∀ (faces : List Nat)
      (hphysical : ∀ faceId, faceId ∈ faces →
        faceId ∈ slabPhysicalFaceEdges D.extent),
      slabAcceptedPairCanonicalChoice? D state faces hphysical = none →
        ∀ faceId, faceId ∈ faces →
          state.1.1.1 faceId = 0 ∧ state.2.1.1 faceId = 0
  | [], _, _, _, hmem => by cases hmem
  | head :: tail, hphysical, hnone, faceId, hmem => by
      by_cases hleft : 0 < state.1.1.1 head
      · simp [slabAcceptedPairCanonicalChoice?, hleft] at hnone
      · by_cases hright : 0 < state.2.1.1 head
        · simp [slabAcceptedPairCanonicalChoice?, hleft, hright] at hnone
        · have hheadLeft : state.1.1.1 head = 0 := by omega
          have hheadRight : state.2.1.1 head = 0 := by omega
          rcases List.mem_cons.mp hmem with heq | htail
          · subst faceId
            exact ⟨hheadLeft, hheadRight⟩
          · have htailNone :
                slabAcceptedPairCanonicalChoice? D state tail
                    (fun next hnext =>
                      hphysical next
                        (List.mem_cons_of_mem head hnext)) = none := by
              simpa [slabAcceptedPairCanonicalChoice?, hleft, hright]
                using hnone
            exact slabAcceptedPairCanonicalChoice?_eq_none_zero
              D state tail
                (fun next hnext =>
                  hphysical next (List.mem_cons_of_mem head hnext))
              htailNone faceId htail

/-- Conversely, a facewise-zero fixed list produces no canonical step. -/
theorem slabAcceptedPairCanonicalChoice?_eq_none_of_zero
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    ∀ (faces : List Nat)
      (hphysical : ∀ faceId, faceId ∈ faces →
        faceId ∈ slabPhysicalFaceEdges D.extent),
      (∀ faceId, faceId ∈ faces →
        state.1.1.1 faceId = 0 ∧ state.2.1.1 faceId = 0) →
      slabAcceptedPairCanonicalChoice? D state faces hphysical = none
  | [], _, _ => rfl
  | head :: tail, hphysical, hzero => by
      have hhead := hzero head List.mem_cons_self
      have hleft : ¬ 0 < state.1.1.1 head := by omega
      have hright : ¬ 0 < state.2.1.1 head := by omega
      simp only [slabAcceptedPairCanonicalChoice?, hleft, hright,
        ↓reduceDIte]
      exact slabAcceptedPairCanonicalChoice?_eq_none_of_zero
        D state tail
          (fun next hnext =>
            hphysical next (List.mem_cons_of_mem head hnext))
          (fun next hnext =>
            hzero next (List.mem_cons_of_mem head hnext))

/-- Exact terminal characterization of the deterministic face scan. -/
theorem slabAcceptedPairCanonicalChoice?_eq_none_iff
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent) :
    slabAcceptedPairCanonicalChoice? D state faces hphysical = none ↔
      ∀ faceId, faceId ∈ faces →
        state.1.1.1 faceId = 0 ∧ state.2.1.1 faceId = 0 :=
  ⟨slabAcceptedPairCanonicalChoice?_eq_none_zero
      D state faces hphysical,
    slabAcceptedPairCanonicalChoice?_eq_none_of_zero
      D state faces hphysical⟩

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep.SlabAcceptedPairedPeelChoice.lowerState
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep.SlabAcceptedPairedPeelChoice.lowerState_mass_add_peelSize
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep.SlabAcceptedPairedPeelChoice.lowerState_mass_lt
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep.slabAcceptedPairCanonicalChoice?
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep.slabAcceptedPairCanonicalChoice?_some_face_mem
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep.slabAcceptedPairCanonicalChoice?_eq_none_iff

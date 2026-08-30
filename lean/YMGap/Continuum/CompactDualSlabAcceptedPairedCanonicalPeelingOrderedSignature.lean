/-
# The canonical paired-peeling signature follows the scan order

The deterministic paired peeler scans physical faces from left to right and
uses the left replica before the right replica at each face.  Component
lowering is pointwise monotone, so a later peel cannot create positivity at a
key which was zero earlier.  Consequently every record in the complete trace
was already positive in the initial state, and the recorded root/replica ranks
are nondecreasing.

This turns the remaining root/replica data from an arbitrary word into an
ordered block word over the fixed scan alphabet.  It is the structural input
needed to sum the fixed-signature `16/25` estimate by one geometric block per
guard face and replica.

Constructive contract: structural recursion and natural-number order only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Root/replica keys and pointwise monotonicity -/

/-- Physical multiplicity at a root/replica key.  `true` is the left
replica, matching the stored peel record. -/
def slabAcceptedPairKeyValue
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (key : Nat × Bool) : Nat :=
  if key.2 then state.1.1.1 key.1 else state.2.1.1 key.1

/-- Root/replica key selected by one dependent canonical choice. -/
def slabAcceptedPairedPeelChoiceKey
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) : Nat × Bool :=
  match choice with
  | .left faceId _ _ => (faceId, true)
  | .right faceId _ _ _ => (faceId, false)

@[simp] theorem slabAcceptedPairedPeelChoiceKey_fst
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    (slabAcceptedPairedPeelChoiceKey choice).1 = choice.faceId := by
  cases choice <;> rfl

/-- The stored record retains the selected key exactly. -/
@[simp] theorem slabAcceptedPairedPeelChoiceRecord_key
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    ((slabAcceptedPairedPeelChoiceRecord choice).rootFaceId,
        (slabAcceptedPairedPeelChoiceRecord choice).left) =
      slabAcceptedPairedPeelChoiceKey choice := by
  cases choice <;> rfl

/-- A selected choice is positive at its own root/replica key. -/
theorem slabAcceptedPairedPeelChoiceKeyValue_pos
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    0 < slabAcceptedPairKeyValue state
      (slabAcceptedPairedPeelChoiceKey choice) := by
  cases choice with
  | left faceId hface hpositive => exact hpositive
  | right faceId hface hleftZero hpositive => exact hpositive

/-- One component peel cannot increase any root/replica multiplicity. -/
theorem slabAcceptedPairedPeelChoiceLowerState_keyValue_le
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state)
    (key : Nat × Bool) :
    slabAcceptedPairKeyValue choice.lowerState key ≤
      slabAcceptedPairKeyValue state key := by
  have hphysical :=
    YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass.SlabAcceptedPairedPeelChoice.lowerState_physical_le
      choice key.1
  unfold slabAcceptedPairKeyValue
  cases hside : key.2 with
  | false => simpa only [hside, if_false] using hphysical.2
  | true => simpa only [hside, if_true] using hphysical.1

/-! ## 2. Every later trace key was positive initially -/

/-- Every record in the complete canonical trace was already positive at its
root/replica key in the initial state.  Peeling can delete occupancy but never
create it. -/
theorem slabAcceptedPairCanonicalPeeling_trace_keyValue_pos
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    forall record,
      record ∈ (slabAcceptedPairCanonicalPeeling
        D faces hphysical state).2 ->
      0 < slabAcceptedPairKeyValue state
        (record.rootFaceId, record.left) := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro record hrecord
    cases hrecord
  · rename_i choice hchoice
    intro record hrecord
    rcases List.mem_cons.mp hrecord with heq | htail
    · subst record
      simpa only [slabAcceptedPairedPeelChoiceRecord_key] using
        slabAcceptedPairedPeelChoiceKeyValue_pos choice
    · have hpositive :=
        slabAcceptedPairCanonicalPeeling_trace_keyValue_pos
          D faces hphysical choice.lowerState record htail
      have hle := slabAcceptedPairedPeelChoiceLowerState_keyValue_le choice
        (record.rootFaceId, record.left)
      exact Nat.lt_of_lt_of_le hpositive hle
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 3. The exact left-to-right scan rank -/

/-- First-occurrence rank of a face in the scanned list. -/
def slabAcceptedPairFaceRank (faceId : Nat) : List Nat -> Nat
  | [] => 0
  | head :: tail =>
      if faceId = head then 0 else slabAcceptedPairFaceRank faceId tail + 1

/-- Rank a root/replica key by face order, with left immediately before right. -/
def slabAcceptedPairScanRank (faces : List Nat) (key : Nat × Bool) : Nat :=
  2 * slabAcceptedPairFaceRank key.1 faces + if key.2 then 0 else 1

/-- Every member has rank strictly below the face-list length. -/
theorem slabAcceptedPairFaceRank_lt_length_of_mem
    (faceId : Nat) : forall faces : List Nat,
    faceId ∈ faces -> slabAcceptedPairFaceRank faceId faces < faces.length
  | [], hmem => by cases hmem
  | head :: tail, hmem => by
      by_cases heq : faceId = head
      · simp only [slabAcceptedPairFaceRank, heq, if_true,
          List.length_cons]
        omega
      · have htail : faceId ∈ tail := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead)
          · exact htail
        have ih := slabAcceptedPairFaceRank_lt_length_of_mem
          faceId tail htail
        simp only [slabAcceptedPairFaceRank, heq, if_false,
          List.length_cons]
        omega

/-! ## 4. The chosen key is the least positive scan key -/

/-- The dependent canonical choice returned by the scan has no larger rank
than any positive queried key in the duplicate-free face list. -/
theorem slabAcceptedPairCanonicalChoice?_rank_le_of_positive
    (D : SlabPhysicalData) (state : SlabAcceptedTwoReplicaState D) :
    forall (faces : List Nat)
      (hnodup : faces.Nodup)
      (hphysical : forall faceId, faceId ∈ faces ->
        faceId ∈ slabPhysicalFaceEdges D.extent)
      (choice : SlabAcceptedPairedPeelChoice D state),
      slabAcceptedPairCanonicalChoice? D state faces hphysical =
          some choice ->
      forall key : Nat × Bool,
        key.1 ∈ faces ->
        0 < slabAcceptedPairKeyValue state key ->
        slabAcceptedPairScanRank faces
            (slabAcceptedPairedPeelChoiceKey choice) ≤
          slabAcceptedPairScanRank faces key
  | [], _, _, choice, hchoice, _, _, _ => by cases hchoice
  | head :: tail, hnodup, hphysical, choice, hchoice, key,
      hkeyMem, hkeyPositive => by
      have htailNodup := (List.nodup_cons.mp hnodup).2
      have hheadNotTail := (List.nodup_cons.mp hnodup).1
      by_cases hleft : 0 < state.1.1.1 head
      · have hchoiceEq : choice = .left head
            (hphysical head List.mem_cons_self) hleft := by
          have hsome :
              some (.left head
                (hphysical head List.mem_cons_self) hleft) = some choice := by
            simpa [slabAcceptedPairCanonicalChoice?, hleft] using hchoice
          exact (Option.some.inj hsome).symm
        subst choice
        unfold slabAcceptedPairedPeelChoiceKey slabAcceptedPairScanRank
        simp only [slabAcceptedPairFaceRank, if_true, Nat.mul_zero,
          Nat.zero_add]
        exact Nat.zero_le _
      · by_cases hright : 0 < state.2.1.1 head
        · have hchoiceEq : choice = .right head
              (hphysical head List.mem_cons_self) (by omega) hright := by
            have hsome :
                some (.right head
                  (hphysical head List.mem_cons_self)
                    (by omega) hright) = some choice := by
              simpa [slabAcceptedPairCanonicalChoice?, hleft, hright]
                using hchoice
            exact (Option.some.inj hsome).symm
          subst choice
          rcases List.mem_cons.mp hkeyMem with hkeyHead | hkeyTail
          · have hface : key.1 = head := hkeyHead
            cases hside : key.2 with
            | false =>
                unfold slabAcceptedPairedPeelChoiceKey
                  slabAcceptedPairScanRank
                simp only [hface, slabAcceptedPairFaceRank, if_true,
                  hside, if_false, Nat.mul_zero, Nat.zero_add]
                exact Nat.le_refl _
            | true =>
                unfold slabAcceptedPairKeyValue at hkeyPositive
                simp only [hface, hside, if_true] at hkeyPositive
                exact False.elim (hleft hkeyPositive)
          · have hkeyNe : key.1 ≠ head := by
              intro heq
              apply hheadNotTail
              simpa only [heq] using hkeyTail
            unfold slabAcceptedPairedPeelChoiceKey
              slabAcceptedPairScanRank
            simp only [slabAcceptedPairFaceRank, if_true, hkeyNe,
              if_false, Nat.mul_zero, Nat.zero_add]
            cases key.2 <;> simp <;> omega
        · have htailChoice :
              slabAcceptedPairCanonicalChoice? D state tail
                (fun faceId hface =>
                  hphysical faceId (List.mem_cons_of_mem head hface)) =
                some choice := by
            simpa [slabAcceptedPairCanonicalChoice?, hleft, hright]
              using hchoice
          have hkeyTail : key.1 ∈ tail := by
            rcases List.mem_cons.mp hkeyMem with hkeyHead | htail
            · cases hside : key.2 with
              | false =>
                  unfold slabAcceptedPairKeyValue at hkeyPositive
                  simp only [hkeyHead, hside, if_false] at hkeyPositive
                  exact False.elim (hright hkeyPositive)
              | true =>
                  unfold slabAcceptedPairKeyValue at hkeyPositive
                  simp only [hkeyHead, hside, if_true] at hkeyPositive
                  exact False.elim (hleft hkeyPositive)
            · exact htail
          have hchoiceFaceMem :=
            slabAcceptedPairCanonicalChoice?_some_face_mem
              D state tail
              (fun faceId hface =>
                hphysical faceId (List.mem_cons_of_mem head hface))
              choice htailChoice
          have hchoiceNe :
              (slabAcceptedPairedPeelChoiceKey choice).1 ≠ head := by
            intro heq
            apply hheadNotTail
            have hkeyMemTail :
                (slabAcceptedPairedPeelChoiceKey choice).1 ∈ tail := by
              simpa only [slabAcceptedPairedPeelChoiceKey_fst] using
                hchoiceFaceMem
            exact heq ▸ hkeyMemTail
          have hkeyNe : key.1 ≠ head := by
            intro heq
            apply hheadNotTail
            exact heq ▸ hkeyTail
          have ih := slabAcceptedPairCanonicalChoice?_rank_le_of_positive
            D state tail htailNodup
            (fun faceId hface =>
              hphysical faceId (List.mem_cons_of_mem head hface))
            choice htailChoice key hkeyTail hkeyPositive
          unfold slabAcceptedPairScanRank at ih ⊢
          simp only [slabAcceptedPairFaceRank, hchoiceNe, hkeyNe,
            if_false]
          omega

/-! ## 5. Complete traces are rank-monotone -/

/-- Numeric scan ranks of one stored trace. -/
def slabAcceptedPairedPeelTraceScanRanks
    (faces : List Nat) (trace : List SlabAcceptedPairedPeelRecord) : List Nat :=
  trace.map fun record =>
    slabAcceptedPairScanRank faces (record.rootFaceId, record.left)

/-- **Ordered-signature theorem.**  For a duplicate-free scan list, complete
canonical peeling records nondecreasing face/replica ranks. -/
theorem slabAcceptedPairCanonicalPeeling_traceScanRanks_pairwise
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hnodup : faces.Nodup)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    (slabAcceptedPairedPeelTraceScanRanks faces
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical state).2).Pairwise (fun left right => left ≤ right) := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · exact List.Pairwise.nil
  · rename_i choice hchoice
    simp only [slabAcceptedPairedPeelTraceScanRanks, List.map_cons,
      slabAcceptedPairedPeelChoiceRecord_key]
    apply List.pairwise_cons.mpr
    refine ⟨?_,
      slabAcceptedPairCanonicalPeeling_traceScanRanks_pairwise
        D faces hnodup hphysical choice.lowerState⟩
    intro laterRank hlaterRank
    obtain ⟨record, hrecord, hrank⟩ := List.mem_map.mp hlaterRank
    subst laterRank
    have hrecordPositiveLower :=
      slabAcceptedPairCanonicalPeeling_trace_keyValue_pos
        D faces hphysical choice.lowerState record hrecord
    have hrecordLe := slabAcceptedPairedPeelChoiceLowerState_keyValue_le choice
      (record.rootFaceId, record.left)
    have hrecordPositive :
        0 < slabAcceptedPairKeyValue state
          (record.rootFaceId, record.left) :=
      Nat.lt_of_lt_of_le hrecordPositiveLower hrecordLe
    have hrecordRoot := slabAcceptedPairCanonicalPeeling_trace_root_mem
      D faces hphysical choice.lowerState record hrecord
    exact slabAcceptedPairCanonicalChoice?_rank_le_of_positive
      D state faces hnodup hphysical choice hchoice
      (record.rootFaceId, record.left) hrecordRoot hrecordPositive
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature.slabAcceptedPairCanonicalPeeling_trace_keyValue_pos
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature.slabAcceptedPairCanonicalChoice?_rank_le_of_positive
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingOrderedSignature.slabAcceptedPairCanonicalPeeling_traceScanRanks_pairwise

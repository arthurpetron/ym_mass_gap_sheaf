/-
# Whole-link switching along the paired physical-support component

The paired-support component is constant on every positive face incident on
one actual slab link.  Consequently the two replicas can be switched at that
link by transposing their complete auxiliary witnesses, with no strandwise
split or support-addition reconstruction.

This module makes that whole-block statement literal.  A link bit is the
Boolean `any` of the canonical face mask over its incident face list.  On
every supported incident face it equals the face bit.  The canonical physical
face swap therefore restricts at each link to either the original first
replica or the original second replica.  Locality of the production fusion
fiber transports the corresponding accepted auxiliary witness, and a
structural fold assembles two accepted global assignments.

The switch is independent of the fusion-tree presentation.  Recoupling and
the global target-column argument remain separate later steps.

Constructive contract: Boolean case analysis, literal incidence lists, and
structural Cartesian assembly only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. One canonical Boolean bit per actual link -/

/-- A slab link is selected when any of its incident face identifiers lies in
the target-rooted union-support component. -/
def slabTwoReplicaSupportLinkSwapB
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId : Nat) (link : SlabLink) : Bool :=
  (slabIncidentPlaqIds extent link).any
    (slabTwoReplicaSupportSwapMask extent left right targetFaceId)

/-- Face swapping preserves every link bit because it preserves the complete
canonical face mask. -/
theorem slabTwoReplicaSupportLinkSwapB_faceSwap
    (extent targetFaceId : Nat) (selected : Nat → Bool)
    (left right : SlabLabelling) (link : SlabLink) :
    slabTwoReplicaSupportLinkSwapB extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right)
        targetFaceId link =
      slabTwoReplicaSupportLinkSwapB
        extent left right targetFaceId link := by
  unfold slabTwoReplicaSupportLinkSwapB
  rw [slabTwoReplicaSupportSwapMask_faceSwap]

/-- On a supported incident face, the link bit is exactly the canonical face
bit.  The reverse direction uses component closure and the fact that every
selected face belongs to the written support carrier. -/
theorem slabTwoReplicaSupportLinkSwapB_eq_face
    {extent targetFaceId faceId : Nat}
    {left right : SlabLabelling} {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hfaceIncident : faceId ∈ slabIncidentPlaqIds extent link)
    (hfaceSupport : 0 < left faceId ∨ 0 < right faceId) :
    slabTwoReplicaSupportLinkSwapB
        extent left right targetFaceId link =
      slabTwoReplicaSupportSwapMask
        extent left right targetFaceId faceId := by
  let mask := slabTwoReplicaSupportSwapMask
    extent left right targetFaceId
  change (slabIncidentPlaqIds extent link).any mask = mask faceId
  cases hfaceMask : mask faceId with
  | true =>
      exact List.any_eq_true.mpr
        ⟨faceId, hfaceIncident, hfaceMask⟩
  | false =>
      cases hlinkMask : (slabIncidentPlaqIds extent link).any mask with
      | false => rfl
      | true =>
          obtain ⟨found, hfoundIncident, hfoundMask⟩ :=
            List.any_eq_true.mp hlinkMask
          have hseed : targetFaceId ∈
              slabTwoReplicaSupportFaceVertices extent left right :=
            mem_slabTwoReplicaSupportFaceVertices
              htarget htargetSupport
          have hfoundComponent : found ∈
              slabTwoReplicaTargetSupportComponent
                extent left right targetFaceId := by
            exact of_decide_eq_true hfoundMask
          have hfoundVertex : found ∈
              slabTwoReplicaSupportFaceVertices extent left right :=
            rootComponent_subset
              (slabSupportFaceAdjacentB extent)
              hseed hfoundComponent
          have hfoundSupport : 0 < left found ∨ 0 < right found := by
            exact of_decide_eq_true (List.mem_filter.mp hfoundVertex).2
          have heq := slabTwoReplicaSupportSwapMask_eq_of_link
            htarget htargetSupport hlink hfaceIncident hfoundIncident
            hfaceSupport hfoundSupport
          change mask found = mask faceId at heq
          rw [hfoundMask, hfaceMask] at heq
          exact False.elim (Bool.noConfusion heq)

/-! ## 2. The global face swap is a whole-link choice locally -/

/-- On every incident face, the left physical output is selected by the one
link bit: take the second replica if true and the first replica if false. -/
theorem twoReplicaSupportSwapLeft_at_incident
    {extent targetFaceId faceId : Nat}
    {left right : SlabLabelling} {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hfaceIncident : faceId ∈ slabIncidentPlaqIds extent link) :
    twoReplicaFaceSwapLeft
        (slabTwoReplicaSupportSwapMask
          extent left right targetFaceId)
        left right faceId =
      if slabTwoReplicaSupportLinkSwapB
          extent left right targetFaceId link then
        right faceId
      else left faceId := by
  by_cases hsupport : 0 < left faceId ∨ 0 < right faceId
  · have heq := slabTwoReplicaSupportLinkSwapB_eq_face
      htarget htargetSupport hlink hfaceIncident hsupport
    rw [heq]
    cases hmask : slabTwoReplicaSupportSwapMask
        extent left right targetFaceId faceId <;>
      simp [twoReplicaFaceSwapLeft, hmask]
  · have hleftZero : left faceId = 0 := by omega
    have hrightZero : right faceId = 0 := by omega
    simp [twoReplicaFaceSwapLeft, hleftZero, hrightZero]

/-- The right physical output makes the complementary whole-link choice. -/
theorem twoReplicaSupportSwapRight_at_incident
    {extent targetFaceId faceId : Nat}
    {left right : SlabLabelling} {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hfaceIncident : faceId ∈ slabIncidentPlaqIds extent link) :
    twoReplicaFaceSwapRight
        (slabTwoReplicaSupportSwapMask
          extent left right targetFaceId)
        left right faceId =
      if slabTwoReplicaSupportLinkSwapB
          extent left right targetFaceId link then
        left faceId
      else right faceId := by
  by_cases hsupport : 0 < left faceId ∨ 0 < right faceId
  · have heq := slabTwoReplicaSupportLinkSwapB_eq_face
      htarget htargetSupport hlink hfaceIncident hsupport
    rw [heq]
    cases hmask : slabTwoReplicaSupportSwapMask
        extent left right targetFaceId faceId <;>
      simp [twoReplicaFaceSwapRight, hmask]
  · have hleftZero : left faceId = 0 := by omega
    have hrightZero : right faceId = 0 := by omega
    simp [twoReplicaFaceSwapRight, hleftZero, hrightZero]

/-! ## 3. Locality of the production fusion-witness fiber -/

theorem slabLinkExternalSpins_eq_of_eq_on_incident
    {extent : Nat} {left right : SlabLabelling} {link : SlabLink}
    (heq : ∀ faceId, faceId ∈ slabIncidentPlaqIds extent link →
      left faceId = right faceId) :
    slabLinkExternalSpins extent left link =
      slabLinkExternalSpins extent right link := by
  unfold slabLinkExternalSpins
  congr 1
  apply List.map_congr_left
  intro faceId hface
  exact heq faceId hface

/-- The accepted local auxiliary list sees a physical labelling only through
the spins on the literal incident-face list. -/
theorem slabLinkFusionWitnesses_eq_of_eq_on_incident
    (K : Nat) {extent : Nat} {left right : SlabLabelling} {link : SlabLink}
    (heq : ∀ faceId, faceId ∈ slabIncidentPlaqIds extent link →
      left faceId = right faceId) :
    slabLinkFusionWitnesses K extent left link =
      slabLinkFusionWitnesses K extent right link := by
  unfold slabLinkFusionWitnesses
  rw [slabLinkExternalSpins_eq_of_eq_on_incident heq]

/-! ## 4. Generic whole-link transposition and its exact decoder -/

def slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId : Nat)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (link : SlabLink) : SlabLabelling :=
  if slabTwoReplicaSupportLinkSwapB
      extent left right targetFaceId link then
    slabFusionWitnessAssignmentAt link rightAssignment
  else
    slabFusionWitnessAssignmentAt link leftAssignment

def slabTwoReplicaSupportSwitchedRightAuxiliaryAt
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId : Nat)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (link : SlabLink) : SlabLabelling :=
  if slabTwoReplicaSupportLinkSwapB
      extent left right targetFaceId link then
    slabFusionWitnessAssignmentAt link leftAssignment
  else
    slabFusionWitnessAssignmentAt link rightAssignment

def slabTwoReplicaSupportSwitchedLeftAssignment
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId : Nat)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment) :
    SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom
    (boundaryCompleteSlabLinks extent)
    (slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
      extent left right targetFaceId leftAssignment rightAssignment)

def slabTwoReplicaSupportSwitchedRightAssignment
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId : Nat)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment) :
    SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom
    (boundaryCompleteSlabLinks extent)
    (slabTwoReplicaSupportSwitchedRightAuxiliaryAt
      extent left right targetFaceId leftAssignment rightAssignment)

theorem slabTwoReplicaSupportSwitchedLeftAssignment_involutive
    (K extent targetFaceId : Nat) (left right : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent left
        (boundaryCompleteSlabLinks extent))
    (_hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent right
        (boundaryCompleteSlabLinks extent)) :
    let selected := slabTwoReplicaSupportSwapMask
      extent left right targetFaceId
    let switchedLeft := slabTwoReplicaSupportSwitchedLeftAssignment
      extent left right targetFaceId leftAssignment rightAssignment
    let switchedRight := slabTwoReplicaSupportSwitchedRightAssignment
      extent left right targetFaceId leftAssignment rightAssignment
    slabTwoReplicaSupportSwitchedLeftAssignment extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right)
        targetFaceId switchedLeft switchedRight = leftAssignment := by
  dsimp only
  let links := boundaryCompleteSlabLinks extent
  let selected := slabTwoReplicaSupportSwapMask
    extent left right targetFaceId
  let switchedLeft := slabTwoReplicaSupportSwitchedLeftAssignment
    extent left right targetFaceId leftAssignment rightAssignment
  let switchedRight := slabTwoReplicaSupportSwitchedRightAssignment
    extent left right targetFaceId leftAssignment rightAssignment
  calc
    slabTwoReplicaSupportSwitchedLeftAssignment extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right)
        targetFaceId switchedLeft switchedRight =
      slabFusionWitnessAssignmentFrom links
        (fun link => slabFusionWitnessAssignmentAt link leftAssignment) := by
          unfold slabTwoReplicaSupportSwitchedLeftAssignment
            slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
          apply List.map_congr_left
          intro link hlink
          congr 1
          have hbit := slabTwoReplicaSupportLinkSwapB_faceSwap
            extent targetFaceId selected left right link
          have hleftLookup := slabFusionWitnessAssignmentAt_from
            (slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
              extent left right targetFaceId
                leftAssignment rightAssignment)
            links link hlink
          have hrightLookup := slabFusionWitnessAssignmentAt_from
            (slabTwoReplicaSupportSwitchedRightAuxiliaryAt
              extent left right targetFaceId
                leftAssignment rightAssignment)
            links link hlink
          change slabTwoReplicaSupportLinkSwapB extent
              (twoReplicaFaceSwapLeft selected left right)
              (twoReplicaFaceSwapRight selected left right)
              targetFaceId link =
            slabTwoReplicaSupportLinkSwapB extent
              left right targetFaceId link at hbit
          change slabFusionWitnessAssignmentAt link switchedLeft =
              slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
                extent left right targetFaceId
                  leftAssignment rightAssignment link at hleftLookup
          change slabFusionWitnessAssignmentAt link switchedRight =
              slabTwoReplicaSupportSwitchedRightAuxiliaryAt
                extent left right targetFaceId
                  leftAssignment rightAssignment link at hrightLookup
          change (if slabTwoReplicaSupportLinkSwapB extent
              (twoReplicaFaceSwapLeft selected left right)
              (twoReplicaFaceSwapRight selected left right)
              targetFaceId link then
                slabFusionWitnessAssignmentAt link switchedRight
              else slabFusionWitnessAssignmentAt link switchedLeft) =
            slabFusionWitnessAssignmentAt link leftAssignment
          rw [hbit, hleftLookup, hrightLookup]
          cases hsourceBit : slabTwoReplicaSupportLinkSwapB
              extent left right targetFaceId link <;>
            simp [slabTwoReplicaSupportSwitchedLeftAuxiliaryAt,
              slabTwoReplicaSupportSwitchedRightAuxiliaryAt,
              hsourceBit]
    _ = leftAssignment :=
      slabFusionWitnessAssignmentFrom_at_eq
        K extent left links leftAssignment
        (boundaryCompleteSlabLinks_nodup extent) hleftAssignment

theorem slabTwoReplicaSupportSwitchedRightAssignment_involutive
    (K extent targetFaceId : Nat) (left right : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (_hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent left
        (boundaryCompleteSlabLinks extent))
    (hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent right
        (boundaryCompleteSlabLinks extent)) :
    let selected := slabTwoReplicaSupportSwapMask
      extent left right targetFaceId
    let switchedLeft := slabTwoReplicaSupportSwitchedLeftAssignment
      extent left right targetFaceId leftAssignment rightAssignment
    let switchedRight := slabTwoReplicaSupportSwitchedRightAssignment
      extent left right targetFaceId leftAssignment rightAssignment
    slabTwoReplicaSupportSwitchedRightAssignment extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right)
        targetFaceId switchedLeft switchedRight = rightAssignment := by
  dsimp only
  let links := boundaryCompleteSlabLinks extent
  let selected := slabTwoReplicaSupportSwapMask
    extent left right targetFaceId
  let switchedLeft := slabTwoReplicaSupportSwitchedLeftAssignment
    extent left right targetFaceId leftAssignment rightAssignment
  let switchedRight := slabTwoReplicaSupportSwitchedRightAssignment
    extent left right targetFaceId leftAssignment rightAssignment
  calc
    slabTwoReplicaSupportSwitchedRightAssignment extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right)
        targetFaceId switchedLeft switchedRight =
      slabFusionWitnessAssignmentFrom links
        (fun link => slabFusionWitnessAssignmentAt link rightAssignment) := by
          unfold slabTwoReplicaSupportSwitchedRightAssignment
            slabTwoReplicaSupportSwitchedRightAuxiliaryAt
          apply List.map_congr_left
          intro link hlink
          congr 1
          have hbit := slabTwoReplicaSupportLinkSwapB_faceSwap
            extent targetFaceId selected left right link
          have hleftLookup := slabFusionWitnessAssignmentAt_from
            (slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
              extent left right targetFaceId
                leftAssignment rightAssignment)
            links link hlink
          have hrightLookup := slabFusionWitnessAssignmentAt_from
            (slabTwoReplicaSupportSwitchedRightAuxiliaryAt
              extent left right targetFaceId
                leftAssignment rightAssignment)
            links link hlink
          change slabTwoReplicaSupportLinkSwapB extent
              (twoReplicaFaceSwapLeft selected left right)
              (twoReplicaFaceSwapRight selected left right)
              targetFaceId link =
            slabTwoReplicaSupportLinkSwapB extent
              left right targetFaceId link at hbit
          change slabFusionWitnessAssignmentAt link switchedLeft =
              slabTwoReplicaSupportSwitchedLeftAuxiliaryAt
                extent left right targetFaceId
                  leftAssignment rightAssignment link at hleftLookup
          change slabFusionWitnessAssignmentAt link switchedRight =
              slabTwoReplicaSupportSwitchedRightAuxiliaryAt
                extent left right targetFaceId
                  leftAssignment rightAssignment link at hrightLookup
          change (if slabTwoReplicaSupportLinkSwapB extent
              (twoReplicaFaceSwapLeft selected left right)
              (twoReplicaFaceSwapRight selected left right)
              targetFaceId link then
                slabFusionWitnessAssignmentAt link switchedLeft
              else slabFusionWitnessAssignmentAt link switchedRight) =
            slabFusionWitnessAssignmentAt link rightAssignment
          rw [hbit, hleftLookup, hrightLookup]
          cases hsourceBit : slabTwoReplicaSupportLinkSwapB
              extent left right targetFaceId link <;>
            simp [slabTwoReplicaSupportSwitchedLeftAuxiliaryAt,
              slabTwoReplicaSupportSwitchedRightAuxiliaryAt,
              hsourceBit]
    _ = rightAssignment :=
      slabFusionWitnessAssignmentFrom_at_eq
        K extent right links rightAssignment
        (boundaryCompleteSlabLinks_nodup extent) hrightAssignment

/-! ## 5. Literal observable whole-link auxiliary transposition -/

def slabObservablePairSupportLinkSwapB
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) (link : SlabLink) : Bool :=
  slabTwoReplicaSupportLinkSwapB D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId link

def slabObservablePairSupportSwitchedLeftAuxiliaryAt
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (link : SlabLink) : SlabLabelling :=
  slabTwoReplicaSupportSwitchedLeftAuxiliaryAt D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId
      pair.1.1.2 pair.2.1.2 link

def slabObservablePairSupportSwitchedRightAuxiliaryAt
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (link : SlabLink) : SlabLabelling :=
  slabTwoReplicaSupportSwitchedRightAuxiliaryAt D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId
      pair.1.1.2 pair.2.1.2 link

theorem slabObservablePairSupportSwitchedLeftAuxiliaryAt_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink) (hlink : link ∈ boundaryCompleteSlabLinks D.extent) :
    slabObservablePairSupportSwitchedLeftAuxiliaryAt
        D rootFaceId targetFaceId pair link ∈
      slabLinkFusionWitnesses D.cutoff D.extent
        (twoReplicaFaceSwapLeft
          (slabObservableTwoReplicaPairPairedSupportSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) link := by
  have htargetSupport :
      0 < pair.1.1.1 targetFaceId ∨ 0 < pair.2.1.1 targetFaceId :=
    Or.inl (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
      D rootFaceId targetFaceId pair hpair)
  cases hswap : slabObservablePairSupportLinkSwapB
      D pair targetFaceId link with
  | false =>
      have hphysical :
          slabLinkFusionWitnesses D.cutoff D.extent
              (twoReplicaFaceSwapLeft
                (slabObservableTwoReplicaPairPairedSupportSwapMask
                  D pair targetFaceId)
                pair.1.1.1 pair.2.1.1) link =
            slabLinkFusionWitnesses D.cutoff D.extent
              pair.1.1.1 link := by
        apply slabLinkFusionWitnesses_eq_of_eq_on_incident
        intro faceId hface
        have hat := twoReplicaSupportSwapLeft_at_incident
          htarget htargetSupport hlink hface
        change slabTwoReplicaSupportLinkSwapB D.extent
          pair.1.1.1 pair.2.1.1 targetFaceId link = false at hswap
        rw [hswap] at hat
        change twoReplicaFaceSwapLeft
          (slabTwoReplicaSupportSwapMask D.extent
            pair.1.1.1 pair.2.1.1 targetFaceId)
          pair.1.1.1 pair.2.1.1 faceId = pair.1.1.1 faceId
        exact hat
      rw [hphysical]
      change slabTwoReplicaSupportLinkSwapB D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId link = false at hswap
      simp [slabObservablePairSupportSwitchedLeftAuxiliaryAt,
        slabTwoReplicaSupportSwitchedLeftAuxiliaryAt,
        hswap]
      exact slabFusionWitnessAssignmentAt_mem_local
        D.cutoff D.extent pair.1.1.1
        (boundaryCompleteSlabLinks D.extent) pair.1.1.2
        pair.1.assignment_mem link hlink
  | true =>
      have hphysical :
          slabLinkFusionWitnesses D.cutoff D.extent
              (twoReplicaFaceSwapLeft
                (slabObservableTwoReplicaPairPairedSupportSwapMask
                  D pair targetFaceId)
                pair.1.1.1 pair.2.1.1) link =
            slabLinkFusionWitnesses D.cutoff D.extent
              pair.2.1.1 link := by
        apply slabLinkFusionWitnesses_eq_of_eq_on_incident
        intro faceId hface
        have hat := twoReplicaSupportSwapLeft_at_incident
          htarget htargetSupport hlink hface
        change slabTwoReplicaSupportLinkSwapB D.extent
          pair.1.1.1 pair.2.1.1 targetFaceId link = true at hswap
        rw [hswap] at hat
        change twoReplicaFaceSwapLeft
          (slabTwoReplicaSupportSwapMask D.extent
            pair.1.1.1 pair.2.1.1 targetFaceId)
          pair.1.1.1 pair.2.1.1 faceId = pair.2.1.1 faceId
        exact hat
      rw [hphysical]
      change slabTwoReplicaSupportLinkSwapB D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId link = true at hswap
      simp [slabObservablePairSupportSwitchedLeftAuxiliaryAt,
        slabTwoReplicaSupportSwitchedLeftAuxiliaryAt,
        hswap]
      exact slabFusionWitnessAssignmentAt_mem_local
        D.cutoff D.extent pair.2.1.1
        (boundaryCompleteSlabLinks D.extent) pair.2.1.2
        (slabExpandedFineSourceEntryAssignment_mem pair.2)
        link hlink

theorem slabObservablePairSupportSwitchedRightAuxiliaryAt_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink) (hlink : link ∈ boundaryCompleteSlabLinks D.extent) :
    slabObservablePairSupportSwitchedRightAuxiliaryAt
        D rootFaceId targetFaceId pair link ∈
      slabLinkFusionWitnesses D.cutoff D.extent
        (twoReplicaFaceSwapRight
          (slabObservableTwoReplicaPairPairedSupportSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) link := by
  have htargetSupport :
      0 < pair.1.1.1 targetFaceId ∨ 0 < pair.2.1.1 targetFaceId :=
    Or.inl (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
      D rootFaceId targetFaceId pair hpair)
  cases hswap : slabObservablePairSupportLinkSwapB
      D pair targetFaceId link with
  | false =>
      have hphysical :
          slabLinkFusionWitnesses D.cutoff D.extent
              (twoReplicaFaceSwapRight
                (slabObservableTwoReplicaPairPairedSupportSwapMask
                  D pair targetFaceId)
                pair.1.1.1 pair.2.1.1) link =
            slabLinkFusionWitnesses D.cutoff D.extent
              pair.2.1.1 link := by
        apply slabLinkFusionWitnesses_eq_of_eq_on_incident
        intro faceId hface
        have hat := twoReplicaSupportSwapRight_at_incident
          htarget htargetSupport hlink hface
        change slabTwoReplicaSupportLinkSwapB D.extent
          pair.1.1.1 pair.2.1.1 targetFaceId link = false at hswap
        rw [hswap] at hat
        change twoReplicaFaceSwapRight
          (slabTwoReplicaSupportSwapMask D.extent
            pair.1.1.1 pair.2.1.1 targetFaceId)
          pair.1.1.1 pair.2.1.1 faceId = pair.2.1.1 faceId
        exact hat
      rw [hphysical]
      change slabTwoReplicaSupportLinkSwapB D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId link = false at hswap
      simp [slabObservablePairSupportSwitchedRightAuxiliaryAt,
        slabTwoReplicaSupportSwitchedRightAuxiliaryAt,
        hswap]
      exact slabFusionWitnessAssignmentAt_mem_local
        D.cutoff D.extent pair.2.1.1
        (boundaryCompleteSlabLinks D.extent) pair.2.1.2
        (slabExpandedFineSourceEntryAssignment_mem pair.2)
        link hlink
  | true =>
      have hphysical :
          slabLinkFusionWitnesses D.cutoff D.extent
              (twoReplicaFaceSwapRight
                (slabObservableTwoReplicaPairPairedSupportSwapMask
                  D pair targetFaceId)
                pair.1.1.1 pair.2.1.1) link =
            slabLinkFusionWitnesses D.cutoff D.extent
              pair.1.1.1 link := by
        apply slabLinkFusionWitnesses_eq_of_eq_on_incident
        intro faceId hface
        have hat := twoReplicaSupportSwapRight_at_incident
          htarget htargetSupport hlink hface
        change slabTwoReplicaSupportLinkSwapB D.extent
          pair.1.1.1 pair.2.1.1 targetFaceId link = true at hswap
        rw [hswap] at hat
        change twoReplicaFaceSwapRight
          (slabTwoReplicaSupportSwapMask D.extent
            pair.1.1.1 pair.2.1.1 targetFaceId)
          pair.1.1.1 pair.2.1.1 faceId = pair.1.1.1 faceId
        exact hat
      rw [hphysical]
      change slabTwoReplicaSupportLinkSwapB D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId link = true at hswap
      simp [slabObservablePairSupportSwitchedRightAuxiliaryAt,
        slabTwoReplicaSupportSwitchedRightAuxiliaryAt,
        hswap]
      exact slabFusionWitnessAssignmentAt_mem_local
        D.cutoff D.extent pair.1.1.1
        (boundaryCompleteSlabLinks D.extent) pair.1.1.2
        pair.1.assignment_mem link hlink

/-! ## 6. Accepted global whole-link switches -/

def slabObservablePairSupportSwitchedLeftAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabFusionWitnessAssignment :=
  slabTwoReplicaSupportSwitchedLeftAssignment D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId pair.1.1.2 pair.2.1.2

def slabObservablePairSupportSwitchedRightAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabFusionWitnessAssignment :=
  slabTwoReplicaSupportSwitchedRightAssignment D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId pair.1.1.2 pair.2.1.2

theorem slabObservablePairSupportSwitchedLeftAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservablePairSupportSwitchedLeftAssignment
        D rootFaceId targetFaceId pair ∈
      slabFineFusionWitnesses D
        (twoReplicaFaceSwapLeft
          (slabObservableTwoReplicaPairPairedSupportSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) := by
  unfold slabObservablePairSupportSwitchedLeftAssignment
    slabFineFusionWitnesses
  apply slabFusionWitnessAssignmentFrom_mem
  intro link hlink
  exact slabObservablePairSupportSwitchedLeftAuxiliaryAt_mem
    D rootFaceId targetFaceId htarget pair hpair link hlink

theorem slabObservablePairSupportSwitchedRightAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservablePairSupportSwitchedRightAssignment
        D rootFaceId targetFaceId pair ∈
      slabFineFusionWitnesses D
        (twoReplicaFaceSwapRight
          (slabObservableTwoReplicaPairPairedSupportSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) := by
  unfold slabObservablePairSupportSwitchedRightAssignment
    slabFineFusionWitnesses
  apply slabFusionWitnessAssignmentFrom_mem
  intro link hlink
  exact slabObservablePairSupportSwitchedRightAuxiliaryAt_mem
    D rootFaceId targetFaceId htarget pair hpair link hlink

end YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabTwoReplicaSupportLinkSwapB_eq_face
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabTwoReplicaSupportLinkSwapB_faceSwap
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.twoReplicaSupportSwapLeft_at_incident
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.twoReplicaSupportSwapRight_at_incident
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabLinkFusionWitnesses_eq_of_eq_on_incident
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabTwoReplicaSupportSwitchedLeftAssignment_involutive
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabTwoReplicaSupportSwitchedRightAssignment_involutive
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabObservablePairSupportSwitchedLeftAuxiliaryAt_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabObservablePairSupportSwitchedRightAuxiliaryAt_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabObservablePairSupportSwitchedLeftAssignment_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch.slabObservablePairSupportSwitchedRightAssignment_mem

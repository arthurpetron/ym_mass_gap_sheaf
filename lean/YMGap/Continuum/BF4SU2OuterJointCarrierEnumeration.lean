/-
# Finite global carrier for the SU(2) outer positive-row obstruction

The independently stretched face choice is not compatible with every shared
coarse link.  This module replaces that false local choice by one literal
finite global search.  A search code carries simultaneously

* one bounded coarse face labelling;
* one pair-channel state at every coarse face; and
* one complete assignment of canonical coarse-link fusion witnesses.

The face field is retained only when every selected channel has the requested
coarse final label and strictly positive raw face weight.  The link assignment
is drawn from the exact Cartesian fiber whose cardinality is the complete
coarse-link multiplicity product.  Consequently every retained code constructs
a `WholeSlabJointChannelSelection`, and hence a strictly positive raw
recoupling row.

Conversely every semantic `WholeSlabJointChannelSelection` occurs in this
finite search after zero-normalizing its face field away from the physical
face list and choosing the first element of the nonempty global link-witness
fiber.  Thus the remaining obstruction is neither an unspecified choice
principle nor a facewise compatibility slogan: it is exactly the constructive
finite statement that `wholeSlabJointCarrierCodes` has positive length for
every positive fine row.

## Axiom gate

Finite list recursion and exact `Q'` comparisons only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
import YMGap.Continuum.CompactDualSlabFineIntertwinerWitness

namespace YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Finite face-channel fields -/

def zeroFaceChannelField : Nat → PairChannelState :=
  fun _ => ((0, 0), 0)

def setFaceChannel
    (field : Nat → PairChannelState)
    (faceId : Nat) (channel : PairChannelState) :
    Nat → PairChannelState :=
  fun query => if query = faceId then channel else field query

/-- Cartesian enumeration of one pair-channel state at every listed face. -/
def faceChannelFields (cutoff : Nat) :
    List Nat → List (Nat → PairChannelState)
  | [] => [zeroFaceChannelField]
  | faceId :: rest =>
      (pairChannelStateSpace cutoff).flatMap
        (fun channel =>
          (faceChannelFields cutoff rest).map
            (fun tail => setFaceChannel tail faceId channel))

/-- Every enumerated field takes an enumerated value on every listed face. -/
theorem faceChannelFields_sound (cutoff : Nat) :
    ∀ (faces : List Nat) (field : Nat → PairChannelState),
      field ∈ faceChannelFields cutoff faces →
      ∀ faceId, faceId ∈ faces →
        field faceId ∈ pairChannelStateSpace cutoff
  | [], _, _, faceId, hface =>
      False.elim (List.not_mem_nil hface)
  | head :: rest, field, hfield, faceId, hface => by
      obtain ⟨channel, hchannel, hblock⟩ :=
        List.mem_flatMap.mp hfield
      obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hblock
      rw [← heq]
      by_cases hsame : faceId = head
      · subst faceId
        simpa [setFaceChannel] using hchannel
      · have hrest : faceId ∈ rest := by
          rcases List.mem_cons.mp hface with hhead | htailMem
          · exact False.elim (hsame hhead)
          · exact htailMem
        simpa [setFaceChannel, hsame] using
          faceChannelFields_sound cutoff rest tail htail faceId hrest

/-- Zero-normalize a field away from a finite face list. -/
def restrictFaceChannelField :
    List Nat → (Nat → PairChannelState) → Nat → PairChannelState
  | [], _ => zeroFaceChannelField
  | faceId :: rest, field =>
      setFaceChannel
        (restrictFaceChannelField rest field) faceId (field faceId)

/-- The normalized field agrees with the original field on a `Nodup` list. -/
theorem restrictFaceChannelField_apply :
    ∀ (faces : List Nat), faces.Nodup →
      ∀ (field : Nat → PairChannelState) (faceId : Nat),
        faceId ∈ faces →
        restrictFaceChannelField faces field faceId = field faceId
  | [], _, _, faceId, hface =>
      False.elim (List.not_mem_nil hface)
  | head :: rest, hnodup, field, faceId, hface => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hface with hhead | htail
      · subst faceId
        simp [restrictFaceChannelField, setFaceChannel]
      · have hne : faceId ≠ head := by
          intro heq
          exact hparts.1 (heq ▸ htail)
        simp only [restrictFaceChannelField, setFaceChannel, hne, if_false]
        exact restrictFaceChannelField_apply rest hparts.2
          field faceId htail

/-- A pointwise admissible field has a canonical representative in the finite
Cartesian enumeration. -/
theorem restrictFaceChannelField_mem
    (cutoff : Nat) :
    ∀ (faces : List Nat) (field : Nat → PairChannelState),
      (∀ faceId, faceId ∈ faces →
        field faceId ∈ pairChannelStateSpace cutoff) →
      restrictFaceChannelField faces field ∈
        faceChannelFields cutoff faces
  | [], _, _ => List.mem_singleton.mpr rfl
  | head :: rest, field, hfield => by
      apply List.mem_flatMap.mpr
      refine ⟨field head, hfield head List.mem_cons_self, ?_⟩
      apply List.mem_map.mpr
      refine
        ⟨restrictFaceChannelField rest field,
          restrictFaceChannelField_mem cutoff rest field
            (fun faceId hface =>
              hfield faceId (List.mem_cons_of_mem head hface)),
          rfl⟩

private theorem rangeNodup :
    ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨rangeNodup n,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = n := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact (Nat.lt_irrefl n) (List.mem_range.mp hleft)

theorem slabFaceEdges_nodup (D : SlabPhysicalData) :
    D.faceEdges.Nodup := by
  unfold SlabPhysicalData.faceEdges slabPhysicalFaceEdges
  exact rangeNodup _

/-! ## 2. Soundness of a global coarse-link fusion assignment -/

/-- Membership in the Cartesian link-assignment list propositionally exposes
an accepted local auxiliary witness at every listed link.  The witness is used
only to prove the natural-number multiplicity positive; the full assignment
itself remains retained as `Type`-level data in the carrier code below. -/
theorem slabFusionWitnessAssignmentsOn_has_local
    (K extent : Nat) (physical : EdgeLabelling) :
    ∀ (links : List SlabLink)
      (assignment : SlabFusionWitnessAssignment),
      assignment ∈
          slabFusionWitnessAssignmentsOn K extent physical links →
      ∀ link, link ∈ links →
        ∃ auxiliary,
          auxiliary ∈
            slabLinkFusionWitnesses K extent physical link
  | [], _, _, link, hlink =>
      False.elim (List.not_mem_nil hlink)
  | head :: rest, assignment, hassignment, link, hlink => by
      obtain ⟨selected, hselected, hblock⟩ :=
        List.mem_flatMap.mp hassignment
      obtain ⟨tail, htail, heq⟩ := List.mem_map.mp hblock
      rcases List.mem_cons.mp hlink with hhead | hrest
      · subst link
        exact ⟨selected, hselected⟩
      · exact slabFusionWitnessAssignmentsOn_has_local
          K extent physical rest tail htail link hrest

theorem slabLinkMultiplicity_pos_of_globalAssignment
    (K extent : Nat) (physical : EdgeLabelling)
    (links : List SlabLink)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment :
      assignment ∈
        slabFusionWitnessAssignmentsOn K extent physical links)
    (link : SlabLink) (hlink : link ∈ links) :
    0 < slabExplicitLinkMultiplicity K extent physical link := by
  obtain ⟨auxiliary, hauxiliary⟩ :=
    slabFusionWitnessAssignmentsOn_has_local
      K extent physical links assignment hassignment link hlink
  have hlength :
      0 < (slabLinkFusionWitnesses
        K extent physical link).length :=
    List.length_pos_of_mem hauxiliary
  rw [slabLinkFusionWitnesses_length] at hlength
  exact hlength

/-! ## 3. The literal finite global search -/

def faceChannelFieldAcceptedB
    (S : SlabScalePair) (fineState coarseTarget : EdgeLabelling)
    (field : Nat → PairChannelState) : Bool :=
  S.coarse.faceEdges.all (fun faceId =>
    decide
      (field faceId ∈ pairChannelStateSpace S.fine.cutoff) &&
    decide ((field faceId).2 = coarseTarget faceId) &&
    decide
      ((0 : Q') <
        packetPairChannelRawWeight S.coarse.coupling
          (wholeSlabFinePacket S fineState faceId)
          (field faceId)))

/-- One simultaneous coarse target, face-channel field, and shared-link
intertwiner assignment. -/
structure WholeSlabJointCarrierCode
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  coarseTarget : EdgeLabelling
  faceChannel : Nat → PairChannelState
  coarseFusionWitness : SlabFusionWitnessAssignment

/-- The literal global dynamic program.  Its nesting order is
target → whole face field → whole shared-link fusion assignment. -/
def wholeSlabJointCarrierCodes
    (S : SlabScalePair) (fineState : EdgeLabelling) :
    List (WholeSlabJointCarrierCode S fineState) :=
  S.coarse.physicalLabellings.flatMap (fun coarseTarget =>
    ((faceChannelFields S.fine.cutoff S.coarse.faceEdges).filter
      (faceChannelFieldAcceptedB S fineState coarseTarget)).flatMap
      (fun field =>
        (slabFusionWitnessAssignmentsOn
          S.coarse.cutoff S.coarse.extent coarseTarget
          (boundaryCompleteSlabLinks S.coarse.extent)).map
          (fun fusionWitness =>
            { coarseTarget := coarseTarget
              faceChannel := field
              coarseFusionWitness := fusionWitness })))

theorem mem_wholeSlabJointCarrierCodes_components
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {code : WholeSlabJointCarrierCode S fineState}
    (hcode : code ∈ wholeSlabJointCarrierCodes S fineState) :
    code.coarseTarget ∈ S.coarse.physicalLabellings ∧
      code.faceChannel ∈
        (faceChannelFields
          S.fine.cutoff S.coarse.faceEdges).filter
          (faceChannelFieldAcceptedB
            S fineState code.coarseTarget) ∧
      code.coarseFusionWitness ∈
        slabFusionWitnessAssignmentsOn
          S.coarse.cutoff S.coarse.extent code.coarseTarget
          (boundaryCompleteSlabLinks S.coarse.extent) := by
  obtain ⟨coarseTarget, htarget, htargetBlock⟩ :=
    List.mem_flatMap.mp hcode
  obtain ⟨field, hfield, hfieldBlock⟩ :=
    List.mem_flatMap.mp htargetBlock
  obtain ⟨fusionWitness, hwitness, rfl⟩ :=
    List.mem_map.mp hfieldBlock
  exact ⟨htarget, hfield, hwitness⟩

theorem mem_wholeSlabJointCarrierCodes_faceConditions
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {code : WholeSlabJointCarrierCode S fineState}
    (hcode : code ∈ wholeSlabJointCarrierCodes S fineState)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    code.faceChannel faceId ∈
        pairChannelStateSpace S.fine.cutoff ∧
      (code.faceChannel faceId).2 =
        code.coarseTarget faceId ∧
      (0 : Q') <
        packetPairChannelRawWeight S.coarse.coupling
          (wholeSlabFinePacket S fineState faceId)
          (code.faceChannel faceId) := by
  have haccepted :
      faceChannelFieldAcceptedB
        S fineState code.coarseTarget code.faceChannel = true :=
    (List.mem_filter.mp
      (mem_wholeSlabJointCarrierCodes_components hcode).2.1).2
  have hfaceAccepted :=
    List.all_eq_true.mp haccepted faceId hface
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfaceAccepted
  exact
    ⟨hfaceAccepted.1.1, hfaceAccepted.1.2, hfaceAccepted.2⟩

theorem mem_wholeSlabJointCarrierCodes_linkPositive
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {code : WholeSlabJointCarrierCode S fineState}
    (hcode : code ∈ wholeSlabJointCarrierCodes S fineState)
    (link : SlabLink)
    (hlink :
      link ∈ boundaryCompleteSlabLinks S.coarse.extent) :
    0 < slabExplicitLinkMultiplicity
      S.coarse.cutoff S.coarse.extent code.coarseTarget link := by
  exact slabLinkMultiplicity_pos_of_globalAssignment
    S.coarse.cutoff S.coarse.extent code.coarseTarget
    (boundaryCompleteSlabLinks S.coarse.extent)
    code.coarseFusionWitness
    (mem_wholeSlabJointCarrierCodes_components hcode).2.2
    link hlink

/-- A retained finite code together with its kernel-checked membership. -/
structure WholeSlabEnumeratedJointCarrier
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  code : WholeSlabJointCarrierCode S fineState
  code_mem : code ∈ wholeSlabJointCarrierCodes S fineState

namespace WholeSlabEnumeratedJointCarrier

def toSelection
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (carrier : WholeSlabEnumeratedJointCarrier S fineState) :
    WholeSlabJointChannelSelection S fineState where
  coarseTarget := carrier.code.coarseTarget
  coarseTarget_mem :=
    (mem_wholeSlabJointCarrierCodes_components
      carrier.code_mem).1
  faceChannel := carrier.code.faceChannel
  faceChannel_mem := by
    intro faceId hface
    exact
      (mem_wholeSlabJointCarrierCodes_faceConditions
        carrier.code_mem faceId hface).1
  faceChannel_final := by
    intro faceId hface
    exact
      (mem_wholeSlabJointCarrierCodes_faceConditions
        carrier.code_mem faceId hface).2.1
  faceChannel_positive := by
    intro faceId hface
    exact
      (mem_wholeSlabJointCarrierCodes_faceConditions
        carrier.code_mem faceId hface).2.2
  coarseLink_positive := by
    intro link hlink
    exact mem_wholeSlabJointCarrierCodes_linkPositive
      carrier.code_mem link hlink

theorem rawWeight_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (carrier : WholeSlabEnumeratedJointCarrier S fineState) :
    (0 : Q') <
      wholeSlabRecouplingRawWeight S fineState
        carrier.code.coarseTarget :=
  carrier.toSelection.rawWeight_pos

end WholeSlabEnumeratedJointCarrier

/-! ## 4. Completeness: the finite carrier is exactly the semantic carrier -/

def listHeadOfLengthPositive {A : Type} :
    (items : List A) → 0 < items.length → A
  | [], hpositive =>
      False.elim (Nat.not_lt_zero 0 hpositive)
  | head :: _, _ => head

theorem listHeadOfLengthPositive_mem {A : Type}
    (items : List A) (hpositive : 0 < items.length) :
    listHeadOfLengthPositive items hpositive ∈ items := by
  cases items with
  | nil => exact False.elim (Nat.not_lt_zero 0 hpositive)
  | cons head tail => exact List.mem_cons_self

def jointSelectionFirstFusionWitness
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    SlabFusionWitnessAssignment :=
  listHeadOfLengthPositive
    (slabFusionWitnessAssignmentsOn
      S.coarse.cutoff S.coarse.extent selection.coarseTarget
      (boundaryCompleteSlabLinks S.coarse.extent))
    (by
      rw [slabFusionWitnessAssignmentsOn_length]
      exact selection.linkProduct_pos)

theorem jointSelectionFirstFusionWitness_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    jointSelectionFirstFusionWitness selection ∈
      slabFusionWitnessAssignmentsOn
        S.coarse.cutoff S.coarse.extent selection.coarseTarget
        (boundaryCompleteSlabLinks S.coarse.extent) := by
  unfold jointSelectionFirstFusionWitness
  exact listHeadOfLengthPositive_mem _ _

def jointSelectionNormalizedFaceChannel
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    Nat → PairChannelState :=
  restrictFaceChannelField
    S.coarse.faceEdges selection.faceChannel

theorem jointSelectionNormalizedFaceChannel_apply
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    jointSelectionNormalizedFaceChannel selection faceId =
      selection.faceChannel faceId := by
  exact restrictFaceChannelField_apply
    S.coarse.faceEdges (slabFaceEdges_nodup S.coarse)
    selection.faceChannel faceId hface

theorem jointSelectionNormalizedFaceChannel_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    jointSelectionNormalizedFaceChannel selection ∈
      faceChannelFields S.fine.cutoff S.coarse.faceEdges := by
  exact restrictFaceChannelField_mem
    S.fine.cutoff S.coarse.faceEdges selection.faceChannel
    selection.faceChannel_mem

theorem jointSelectionNormalizedFaceChannel_accepted
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    faceChannelFieldAcceptedB S fineState selection.coarseTarget
      (jointSelectionNormalizedFaceChannel selection) = true := by
  apply List.all_eq_true.mpr
  intro faceId hface
  rw [jointSelectionNormalizedFaceChannel_apply
    selection faceId hface]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact
    ⟨⟨selection.faceChannel_mem faceId hface,
        selection.faceChannel_final faceId hface⟩,
      selection.faceChannel_positive faceId hface⟩

def jointSelectionToCarrierCode
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    WholeSlabJointCarrierCode S fineState where
  coarseTarget := selection.coarseTarget
  faceChannel := jointSelectionNormalizedFaceChannel selection
  coarseFusionWitness := jointSelectionFirstFusionWitness selection

def jointSelectionToEnumeratedCarrier
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    WholeSlabEnumeratedJointCarrier S fineState where
  code := jointSelectionToCarrierCode selection
  code_mem := by
    apply List.mem_flatMap.mpr
    refine ⟨selection.coarseTarget, selection.coarseTarget_mem, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨jointSelectionNormalizedFaceChannel selection, ?_, ?_⟩
    · apply List.mem_filter.mpr
      exact
        ⟨jointSelectionNormalizedFaceChannel_mem selection,
          jointSelectionNormalizedFaceChannel_accepted selection⟩
    · apply List.mem_map.mpr
      exact
        ⟨jointSelectionFirstFusionWitness selection,
          jointSelectionFirstFusionWitness_mem selection,
          rfl⟩

/-! ## 5. Minimal finite nonemptiness residual and family reduction -/

/-- The smallest executable residual exposed by the global search: its finite
candidate list has positive length. -/
structure WholeSlabJointCarrierNonempty
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  candidates_positive :
    0 < (wholeSlabJointCarrierCodes S fineState).length

namespace WholeSlabJointCarrierNonempty

def toEnumeratedCarrier
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (nonempty : WholeSlabJointCarrierNonempty S fineState) :
    WholeSlabEnumeratedJointCarrier S fineState where
  code :=
    listHeadOfLengthPositive
      (wholeSlabJointCarrierCodes S fineState)
      nonempty.candidates_positive
  code_mem :=
    listHeadOfLengthPositive_mem
      (wholeSlabJointCarrierCodes S fineState)
      nonempty.candidates_positive

def toSelection
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (nonempty : WholeSlabJointCarrierNonempty S fineState) :
    WholeSlabJointChannelSelection S fineState :=
  nonempty.toEnumeratedCarrier.toSelection

end WholeSlabJointCarrierNonempty

def WholeSlabEnumeratedJointCarrier.toNonempty
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (carrier : WholeSlabEnumeratedJointCarrier S fineState) :
    WholeSlabJointCarrierNonempty S fineState where
  candidates_positive := List.length_pos_of_mem carrier.code_mem

def jointSelectionToCarrierNonempty
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (selection : WholeSlabJointChannelSelection S fineState) :
    WholeSlabJointCarrierNonempty S fineState :=
  (jointSelectionToEnumeratedCarrier selection).toNonempty

/-- The genuine all-row residual, now stated only as positive length of the
explicit finite joint-carrier search. -/
structure SU2OuterJointCarrierNonempty
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  nonempty :
    ∀ K source,
      K ≠ 1 →
      source ∈
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
          (su2OuterScalePair
            G g hg candidate hcandidate K).fine.physicalTerm source →
      WholeSlabJointCarrierNonempty
        (su2OuterScalePair
          G g hg candidate hcandidate K) source

def SU2OuterJointCarrierNonempty.toJointChannelSelection
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (finiteCarrier :
      SU2OuterJointCarrierNonempty
        G g hg candidate hcandidate) :
    SU2OuterJointChannelSelection
      G g hg candidate hcandidate where
  select := by
    intro K source hK hsource hpositive
    exact
      (finiteCarrier.nonempty
        K source hK hsource hpositive).toSelection

def SU2OuterJointCarrierNonempty.toPositiveRowClosure
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (finiteCarrier :
      SU2OuterJointCarrierNonempty
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate :=
  finiteCarrier.toJointChannelSelection.toPositiveRowClosure

def jointChannelSelectionToCarrierNonempty
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (joint :
      SU2OuterJointChannelSelection
        G g hg candidate hcandidate) :
    SU2OuterJointCarrierNonempty
      G g hg candidate hcandidate where
  nonempty := by
    intro K source hK hsource hpositive
    exact
      jointSelectionToCarrierNonempty
        (joint.select K source hK hsource hpositive)

#print axioms faceChannelFields_sound
#print axioms restrictFaceChannelField_apply
#print axioms restrictFaceChannelField_mem
#print axioms slabFaceEdges_nodup
#print axioms slabFusionWitnessAssignmentsOn_has_local
#print axioms slabLinkMultiplicity_pos_of_globalAssignment
#print axioms mem_wholeSlabJointCarrierCodes_components
#print axioms mem_wholeSlabJointCarrierCodes_faceConditions
#print axioms mem_wholeSlabJointCarrierCodes_linkPositive
#print axioms WholeSlabEnumeratedJointCarrier.toSelection
#print axioms WholeSlabEnumeratedJointCarrier.rawWeight_pos
#print axioms jointSelectionToEnumeratedCarrier
#print axioms WholeSlabJointCarrierNonempty.toSelection
#print axioms SU2OuterJointCarrierNonempty.toJointChannelSelection
#print axioms SU2OuterJointCarrierNonempty.toPositiveRowClosure
#print axioms jointChannelSelectionToCarrierNonempty

end YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration

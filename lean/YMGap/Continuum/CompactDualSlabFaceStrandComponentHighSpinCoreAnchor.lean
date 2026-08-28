/-
# Decode a blocked high-spin component to an explicit finite-core anchor

The exterior reserve check fails precisely when some touched physical face
would be lowered below the threshold.  This module turns that finite Boolean
failure into mathematical data.

If a Boolean selection of `n` slots contains more than `n - S` selected
positions, then its prefix of length `S` has positive count.  Splitting the
count at `S` and using the existing positive-count witness computes a selected
slot strictly below `S`.  Applied to a failed component reserve check, this
produces an actual `SlabFaceStrandCopy` in the rooted component whose slot is
below the finite-core threshold.

Consequently every rooted component is now constructively either

* exterior-peelable, with the accepted Casimir-paid path from the preceding
  module; or
* attached to an explicit selected finite-core strand copy.

This is a classification theorem, not yet a summation over core-attached
decorations and not a finite-core spectral estimate.

Constructive contract: structural recursion on finite lists and Boolean
interval counts only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Extract a failed entry from a finite `List.all` scan -/

/-- A false finite universal scan computes an entry on which the Boolean test
is false by structural descent through the list. -/
def listAllFalseWitness {A : Type}
    (test : A -> Bool) : forall items : List A,
    items.all test = false ->
      Σ' item : A, (item ∈ items) ×' (test item = false)
  | [], hfalse => by cases hfalse
  | head :: tail, hfalse => by
      cases hhead : test head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          have htail : tail.all test = false := by
            change (test head && tail.all test) = false at hfalse
            rw [hhead] at hfalse
            exact hfalse
          let witness := listAllFalseWitness test tail htail
          exact ⟨witness.1,
            List.mem_cons_of_mem head witness.2.1,
            witness.2.2⟩

/-! ## 2. Finite pigeonhole witness below a core threshold -/

/-- If a selection of `length` slots overflows the exterior capacity
`length - threshold`, compute a selected slot below `threshold`. -/
def boolCountFromCoreAnchorWitness
    (selected : Nat -> Bool) (length threshold : Nat)
    (hpositive : 0 < boolCountFrom selected 0 length)
    (hoverflow : length <
      boolCountFrom selected 0 length + threshold) :
    {slot : Fin length //
      slot.val < threshold ∧ selected slot.val = true} := by
  by_cases hthreshold : threshold <= length
  · have hlength : threshold + (length - threshold) = length := by
      omega
    have hsplit := boolCountFrom_add selected 0 threshold
      (length - threshold)
    simp only [Nat.zero_add] at hsplit
    rw [hlength] at hsplit
    have htailLe := boolCountFrom_le selected threshold
      (length - threshold)
    have hprefixPositive :
        0 < boolCountFrom selected 0 threshold := by
      omega
    let prefixWitness :=
      YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness.boolCountFromPositiveWitness
        selected 0 threshold hprefixPositive
    exact
      ⟨⟨prefixWitness.1.val,
          Nat.lt_of_lt_of_le prefixWitness.1.isLt hthreshold⟩,
        prefixWitness.1.isLt,
        by simpa using prefixWitness.2⟩
  · have hlengthThreshold : length < threshold := by omega
    let fullWitness :=
      YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness.boolCountFromPositiveWitness
        selected 0 length hpositive
    exact
      ⟨fullWitness.1,
        Nat.lt_trans fullWitness.1.isLt hlengthThreshold,
        by simpa using fullWitness.2⟩

/-! ## 3. An actual selected finite-core copy -/

/-- Data decoded from a blocked rooted component: a physical face and a
literal selected copy below the declared core threshold. -/
structure SlabComponentCoreAnchor
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : Type where
  copy : SlabFaceStrandCopy physical
  face_physical : copy.faceId ∈ slabPhysicalFaceEdges extent
  slot_core : copy.slot.val < threshold
  selected_true : seed.selected copy = true
  reserve_overflow :
    physical copy.faceId <
      slabFaceStrandSelectionCount seed.selected copy.faceId + threshold

/-- Decode the failed finite scan only as far as a physical face with
nonzero selected multiplicity and reserve overflow. -/
def SlabFusionWitnessFaceStrandSeed.reserveFailureFace
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
        false) :
    Σ' faceId : Nat,
      (faceId ∈ slabPhysicalFaceEdges extent) ×'
      (slabFaceStrandSelectionCount seed.selected faceId ≠ 0) ×'
      (physical faceId <
        slabFaceStrandSelectionCount seed.selected faceId + threshold) := by
  unfold SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck at hcheck
  let failedWitness := listAllFalseWitness
    (fun faceId =>
      decide
        (slabFaceStrandSelectionCount seed.selected faceId = 0 ∨
          slabFaceStrandSelectionCount seed.selected faceId + threshold <=
            physical faceId))
    (slabPhysicalFaceEdges extent) hcheck
  let failed : Nat := failedWitness.1
  have hnotPaid :
      ¬(slabFaceStrandSelectionCount seed.selected failed = 0 ∨
        slabFaceStrandSelectionCount seed.selected failed + threshold <=
          physical failed) := by
    exact of_decide_eq_false failedWitness.2.2
  have hcountNe :
      slabFaceStrandSelectionCount seed.selected failed ≠ 0 := by
    intro hzero
    exact hnotPaid (Or.inl hzero)
  have hoverflow :
      physical failed <
        slabFaceStrandSelectionCount seed.selected failed + threshold := by
    have hnotLe :
        ¬slabFaceStrandSelectionCount seed.selected failed + threshold <=
          physical failed := by
      intro hle
      exact hnotPaid (Or.inr hle)
    exact Nat.lt_of_not_ge hnotLe
  exact ⟨failed, failedWitness.2.1, hcountNe, hoverflow⟩

/-- A failed component reserve scan computes an explicit selected core copy.
No choice is used: the failed face comes from recursive `List.all` descent and
the slot comes from the positive prefix count witness. -/
def SlabFusionWitnessFaceStrandSeed.coreAnchorOfReserveFailure
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
        false) :
    SlabComponentCoreAnchor seed threshold := by
  let failure :=
    SlabFusionWitnessFaceStrandSeed.reserveFailureFace
      seed threshold hcheck
  let failed : Nat := failure.1
  have hcountNe :
      slabFaceStrandSelectionCount seed.selected failed ≠ 0 :=
    failure.2.2.1
  have hcountPositive :
      0 < slabFaceStrandSelectionCount seed.selected failed := by
    omega
  have hoverflow :
      physical failed <
        slabFaceStrandSelectionCount seed.selected failed + threshold :=
    failure.2.2.2
  let slotWitness := boolCountFromCoreAnchorWitness
    (slabFaceStrandSelectionAt seed.selected failed)
    (physical failed) threshold
    (by
      unfold slabFaceStrandSelectionCount at hcountPositive
      exact hcountPositive)
    (by
      unfold slabFaceStrandSelectionCount at hoverflow
      exact hoverflow)
  let copy : SlabFaceStrandCopy physical :=
    { faceId := failed
      slot := slotWitness.1 }
  have hselected : seed.selected copy = true := by
    have hslot := slotWitness.2.2
    rw [slabFaceStrandSelectionAt_fin] at hslot
    exact hslot
  exact
    { copy := copy
      face_physical := failure.2.1
      slot_core := slotWitness.2.1
      selected_true := hselected
      reserve_overflow := hoverflow }

/-! ## 4. The complete component dichotomy with decoded core data -/

/-- Every rooted component is either exterior-peelable or carries an explicit
selected finite-core anchor. -/
inductive SlabComponentExteriorOrCoreAnchor
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : Type
  | exterior
      (reserve_paid :
        SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
          true)
  | core
      (anchor : SlabComponentCoreAnchor seed threshold)

/-- Evaluate the reserve check and decode the failed branch immediately to
an actual core anchor copy. -/
def SlabFusionWitnessFaceStrandSeed.exteriorOrCoreAnchor
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) :
    SlabComponentExteriorOrCoreAnchor seed threshold :=
  match hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold with
  | true => .exterior hcheck
  | false => .core
      (SlabFusionWitnessFaceStrandSeed.coreAnchorOfReserveFailure
        seed threshold hcheck)

#print axioms listAllFalseWitness
#print axioms boolCountFromCoreAnchorWitness
#print axioms SlabComponentCoreAnchor
#print axioms SlabFusionWitnessFaceStrandSeed.reserveFailureFace
#print axioms SlabFusionWitnessFaceStrandSeed.coreAnchorOfReserveFailure
#print axioms SlabComponentExteriorOrCoreAnchor
#print axioms SlabFusionWitnessFaceStrandSeed.exteriorOrCoreAnchor

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor

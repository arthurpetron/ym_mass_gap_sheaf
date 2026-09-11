/-
# The active inward-mate debt carrier contains its positive strand root

The positivity-gated remainder is already a finite Cartesian carrier.  This
file strengthens each carrier element from a bare pair to dependent data: its
chosen local assignment is stored together with membership in the fiber
selected by its Boolean word.

A structural theorem follows a word to its first `true` bit through the same
Cartesian recursion and extracts the actual witness chosen from the debt
fiber at that position.  Specializing to the cube proves that both faces at
the computed geometric root are positive.  The next compiler can therefore
construct literal bounded face-strand copies at that root without extracting
data from an existential proposition.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Follow the Cartesian assignment to its first debt choice -/

/-- Every member of a Boolean-selected Cartesian fiber has exactly one stored
entry per input item. -/
theorem choiceFiberAssignment_member_length {A B : Type}
    (target debt : A → List B) :
    ∀ (items : List A) (word : List Bool)
      (assignment : List (A × B)),
      assignment ∈ choiceFiberAssignments target debt items word →
        assignment.length = items.length
  | [], _, assignment, hassignment => by
      simp only [choiceFiberAssignments, List.mem_singleton] at hassignment
      subst assignment
      rfl
  | _ :: _, [], _, hassignment => by
      simp only [choiceFiberAssignments, List.not_mem_nil] at hassignment
  | head :: tail, false :: word, assignment, hassignment => by
      obtain ⟨headWitness, _, htailMap⟩ := List.mem_flatMap.mp hassignment
      obtain ⟨tailAssignment, htailAssignment, hassignmentEq⟩ :=
        List.mem_map.mp htailMap
      rw [← hassignmentEq]
      simp only [List.length_cons]
      rw [choiceFiberAssignment_member_length
        target debt tail word tailAssignment htailAssignment]
  | head :: tail, true :: word, assignment, hassignment => by
      obtain ⟨headWitness, _, htailMap⟩ := List.mem_flatMap.mp hassignment
      obtain ⟨tailAssignment, htailAssignment, hassignmentEq⟩ :=
        List.mem_map.mp htailMap
      rw [← hassignmentEq]
      simp only [List.length_cons]
      rw [choiceFiberAssignment_member_length
        target debt tail word tailAssignment htailAssignment]

/-- At the first true position, the already stored assignment entry belongs
to the debt fiber.  This theorem is propositional: the witness itself is read
from the assignment list and never extracted from membership. -/
theorem choiceFiberAssignment_firstTrue_get_mem_debt {A B : Type}
    (target debt : A → List B) :
    ∀ (items : List A) (word : List Bool)
      (assignment : List (A × B))
      (itemRoot : Fin items.length)
      (assignmentRoot : Fin assignment.length),
      itemRoot.val = firstTrueIndex word →
      assignmentRoot.val = itemRoot.val →
      word.length = items.length →
      true ∈ word →
      assignment ∈ choiceFiberAssignments target debt items word →
      (assignment.get assignmentRoot).1 = items.get itemRoot ∧
        (assignment.get assignmentRoot).2 ∈ debt (items.get itemRoot)
  | [], _, _, itemRoot, _, _, _, _, _, _ => Fin.elim0 itemRoot
  | _ :: _, [], _, _, _, _, _, _, htrue, _ => by simp at htrue
  | head :: tail, false :: word, assignment,
      itemRoot, assignmentRoot, hitemRoot, hrootEq, hwordLength,
      htrue, hassignment => by
      obtain ⟨headWitness, _, htailMap⟩ := List.mem_flatMap.mp hassignment
      obtain ⟨tailAssignment, htailAssignment, hassignmentEq⟩ :=
        List.mem_map.mp htailMap
      subst assignment
      have htrueTail : true ∈ word := by simpa using htrue
      have hwordLengthTail : word.length = tail.length := by
        simp only [List.length_cons] at hwordLength
        omega
      let tailItemRoot : Fin tail.length :=
        ⟨firstTrueIndex word,
          by
            rw [← hwordLengthTail]
            exact firstTrueIndex_lt_of_mem_true word htrueTail⟩
      have htailLength := choiceFiberAssignment_member_length
        target debt tail word tailAssignment htailAssignment
      let tailAssignmentRoot : Fin tailAssignment.length :=
        ⟨firstTrueIndex word, by
          rw [htailLength]
          rw [← hwordLengthTail]
          exact firstTrueIndex_lt_of_mem_true word htrueTail⟩
      have hitemRootValue :
          itemRoot.val = firstTrueIndex word + 1 := by
        simpa [firstTrueIndex] using hitemRoot
      have hitemRootEq : itemRoot = Fin.succ tailItemRoot := by
        apply Fin.ext
        dsimp [tailItemRoot]
        simpa [firstTrueIndex] using hitemRoot
      have hassignmentRootEq :
          assignmentRoot = Fin.succ tailAssignmentRoot := by
        apply Fin.ext
        dsimp [tailAssignmentRoot, tailItemRoot]
        omega
      subst itemRoot
      subst assignmentRoot
      simpa using choiceFiberAssignment_firstTrue_get_mem_debt
        target debt tail word tailAssignment
          tailItemRoot tailAssignmentRoot rfl rfl
          hwordLengthTail htrueTail htailAssignment
  | head :: tail, true :: word, assignment,
      itemRoot, assignmentRoot, hitemRoot, hrootEq, _, _, hassignment => by
      obtain ⟨headWitness, hheadWitness, htailMap⟩ :=
        List.mem_flatMap.mp hassignment
      obtain ⟨tailAssignment, _, hassignmentEq⟩ :=
        List.mem_map.mp htailMap
      subst assignment
      have hitemRootEq : itemRoot = ⟨0, by simp⟩ := by
        apply Fin.ext
        simpa [firstTrueIndex] using hitemRoot
      have hassignmentRootEq : assignmentRoot = ⟨0, by simp⟩ := by
        apply Fin.ext
        omega
      subst itemRoot
      subst assignmentRoot
      exact ⟨rfl, hheadWitness⟩

/-- Transport a position in the item list to the same stored position in a
Cartesian assignment.  The value is independent of the membership proof; the
proof only certifies its bound. -/
def choiceFiberAssignmentPosition {A B : Type}
    (target debt : A → List B)
    (items : List A) (word : List Bool)
    (assignment : List (A × B))
    (hassignment : assignment ∈
      choiceFiberAssignments target debt items word)
    (position : Fin items.length) : Fin assignment.length :=
  ⟨position.val, by
    rw [choiceFiberAssignment_member_length
      target debt items word assignment hassignment]
    exact position.isLt⟩

/-- Reading the transported first-true position returns an element of the
selected debt fiber. -/
theorem choiceFiberAssignmentPosition_get_mem_debt {A B : Type}
    (target debt : A → List B)
    (items : List A) (word : List Bool)
    (assignment : List (A × B))
    (hassignment : assignment ∈
      choiceFiberAssignments target debt items word)
    (position : Fin items.length)
    (hposition : position.val = firstTrueIndex word)
    (hwordLength : word.length = items.length)
    (htrue : true ∈ word) :
    (assignment.get
        (choiceFiberAssignmentPosition target debt items word
          assignment hassignment position)).1 = items.get position ∧
      (assignment.get
        (choiceFiberAssignmentPosition target debt items word
          assignment hassignment position)).2 ∈ debt (items.get position) := by
  exact choiceFiberAssignment_firstTrue_get_mem_debt
    target debt items word assignment position
      (choiceFiberAssignmentPosition target debt items word
        assignment hassignment position)
      hposition rfl hwordLength htrue hassignment

/-- A Cartesian assignment together with the already computed first-debt
position and the certificate read there. -/
structure RootedChoiceFiberAssignment {A B : Type}
    (target debt : A → List B) (items : List A) (word : List Bool)
    (itemRoot : Fin items.length) : Type where
  assignment : List (A × B)
  assignment_mem : assignment ∈
    choiceFiberAssignments target debt items word
  assignmentRoot : Fin assignment.length
  assignmentRoot_val : assignmentRoot.val = itemRoot.val
  root_item : (assignment.get assignmentRoot).1 = items.get itemRoot
  root_mem : (assignment.get assignmentRoot).2 ∈ debt (items.get itemRoot)

/-- Attach the rooted certificate to every assignment in one selected
Cartesian fiber. -/
def rootedChoiceFiberAssignments {A B : Type}
    (target debt : A → List B) (items : List A) (word : List Bool)
    (itemRoot : Fin items.length)
    (hitemRoot : itemRoot.val = firstTrueIndex word)
    (hwordLength : word.length = items.length)
    (htrue : true ∈ word) :
    List (RootedChoiceFiberAssignment target debt items word itemRoot) :=
  (choiceFiberAssignments target debt items word).attach.map fun assignment =>
    let assignmentRoot := choiceFiberAssignmentPosition
      target debt items word assignment.1 assignment.2 itemRoot
    let hroot := choiceFiberAssignmentPosition_get_mem_debt
      target debt items word assignment.1 assignment.2 itemRoot
        hitemRoot hwordLength htrue
    { assignment := assignment.1
      assignment_mem := assignment.2
      assignmentRoot := assignmentRoot
      assignmentRoot_val := rfl
      root_item := hroot.1
      root_mem := hroot.2 }

theorem rootedChoiceFiberAssignments_length {A B : Type}
    (target debt : A → List B) (items : List A) (word : List Bool)
    (itemRoot : Fin items.length)
    (hitemRoot : itemRoot.val = firstTrueIndex word)
    (hwordLength : word.length = items.length)
    (htrue : true ∈ word) :
    (rootedChoiceFiberAssignments target debt items word itemRoot
      hitemRoot hwordLength htrue).length =
      (choiceFiberAssignments target debt items word).length := by
  simp [rootedChoiceFiberAssignments]

/-! ## 2. Intrinsically valid active cube-debt carrier -/

/-- One nonempty word and one assignment with its exact membership retained
as Type-level data. -/
structure CubeRootedActiveDebtFusionCarrier
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Type where
  word : CubeNonemptyDebtWord
  rooted : RootedChoiceFiberAssignment
      (fun linked =>
        CompactDualSlabFineIntertwinerWitness.slabLinkFusionWitnesses
          K 1 (centralLowerCubeEvenInwardMatePhysical physical)
          linked.1.link)
      (cubeInwardMateActiveStretchedFusionWitnesses
        K physical hK hbounded)
      cubeProductionIncidences.attach word.1 (cubeDebtRootPosition word)

/-- Enumerate the dependent carrier directly from attached words and attached
members of their selected Cartesian fibers. -/
def cubeRootedActiveDebtFusionCarriers
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (CubeRootedActiveDebtFusionCarrier K physical hK hbounded) :=
  (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.flatMap
    fun word =>
      (rootedChoiceFiberAssignments
        (fun linked =>
          CompactDualSlabFineIntertwinerWitness.slabLinkFusionWitnesses
            K 1 (centralLowerCubeEvenInwardMatePhysical physical)
            linked.1.link)
        (cubeInwardMateActiveStretchedFusionWitnesses
          K physical hK hbounded)
        cubeProductionIncidences.attach word.1 (cubeDebtRootPosition word) rfl
        (nonemptyDebtChoiceWords_word_length
          cubeProductionIncidences.attach word.1 word.2)
        (true_mem_of_mem_nonemptyDebtChoiceWords
          cubeProductionIncidences.attach word.1 word.2)).map fun rooted =>
            { word := word, rooted := rooted }

private theorem cubeRootedActiveDebtFusionCarriers_length_aux
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    ∀ words : List CubeNonemptyDebtWord,
    (words.flatMap fun word =>
      (rootedChoiceFiberAssignments
        (fun linked =>
          CompactDualSlabFineIntertwinerWitness.slabLinkFusionWitnesses
            K 1 (centralLowerCubeEvenInwardMatePhysical physical)
            linked.1.link)
        (cubeInwardMateActiveStretchedFusionWitnesses
          K physical hK hbounded)
        cubeProductionIncidences.attach word.1 (cubeDebtRootPosition word) rfl
        (nonemptyDebtChoiceWords_word_length
          cubeProductionIncidences.attach word.1 word.2)
        (true_mem_of_mem_nonemptyDebtChoiceWords
          cubeProductionIncidences.attach word.1 word.2)).map fun rooted =>
            ( { word := word, rooted := rooted } :
              CubeRootedActiveDebtFusionCarrier
                K physical hK hbounded)).length =
      natListSum (words.map fun word =>
        (choiceFiberAssignments
          (fun linked =>
            CompactDualSlabFineIntertwinerWitness.slabLinkFusionWitnesses
              K 1 (centralLowerCubeEvenInwardMatePhysical physical)
              linked.1.link)
          (cubeInwardMateActiveStretchedFusionWitnesses
            K physical hK hbounded)
          cubeProductionIncidences.attach word.1).length)
  | [] => rfl
  | word :: words => by
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.map_cons, natListSum]
      rw [rootedChoiceFiberAssignments_length]
      rw [cubeRootedActiveDebtFusionCarriers_length_aux
        K physical hK hbounded words]

/-- The strengthened dependent carrier retains the exact active-remainder
cardinality. -/
theorem cubeRootedActiveDebtFusionCarriers_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeRootedActiveDebtFusionCarriers
      K physical hK hbounded).length =
      cubeInwardMateNonemptyActiveStretchedRemainder
        K physical hK hbounded := by
  unfold cubeRootedActiveDebtFusionCarriers
    cubeInwardMateNonemptyActiveStretchedRemainder nonemptyDebtExpansion
  rw [cubeRootedActiveDebtFusionCarriers_length_aux]
  apply congrArg natListSum
  calc
    (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.map
        (fun word =>
          (choiceFiberAssignments
            (fun linked =>
              CompactDualSlabFineIntertwinerWitness.slabLinkFusionWitnesses
                K 1 (centralLowerCubeEvenInwardMatePhysical physical)
                linked.1.link)
            (cubeInwardMateActiveStretchedFusionWitnesses
              K physical hK hbounded)
            cubeProductionIncidences.attach word.1).length) =
        (nonemptyDebtChoiceWords cubeProductionIncidences.attach).attach.map
          (fun word => debtChoiceProduct
            (cubeInwardMateTargetLinkMultiplicity K physical)
            (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
            cubeProductionIncidences.attach word.1) := by
              apply List.map_congr_left
              intro word _
              change (cubeActiveDebtWordFusionAssignments
                K physical hK hbounded word.1).length = _
              exact cubeActiveDebtWordFusionAssignments_length
                K physical hK hbounded word.1
    _ = ((nonemptyDebtChoiceWords
          cubeProductionIncidences.attach).attach.map Subtype.val).map
        (debtChoiceProduct
          (cubeInwardMateTargetLinkMultiplicity K physical)
          (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
          cubeProductionIncidences.attach) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro word _
            rfl
    _ = (nonemptyDebtChoiceWords cubeProductionIncidences.attach).map
        (debtChoiceProduct
          (cubeInwardMateTargetLinkMultiplicity K physical)
          (cubeInwardMateActiveStretchedDebt K physical hK hbounded)
          cubeProductionIncidences.attach) := by
            rw [List.attach_map_subtype_val]

/-! ## 3. Read the actual root witness and its positive face copies -/

/-- Forget only the rooting certificate and recover the underlying complete
cube assignment. -/
def CubeRootedActiveDebtFusionCarrier.assignment
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : CubeDebtFusionAssignment :=
  carrier.rooted.assignment

/-- Reuse the computed word position as a bounded position in the stored
assignment.  Assignment membership proves the two lists have equal length. -/
def CubeRootedActiveDebtFusionCarrier.rootAssignmentPosition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    Fin carrier.assignment.length :=
  carrier.rooted.assignmentRoot

/-- The actual auxiliary labelling is read directly from the assignment list,
so no proposition is eliminated to manufacture data. -/
def CubeRootedActiveDebtFusionCarrier.rootAuxiliary
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : EdgeLabelling :=
  (carrier.assignment.get carrier.rootAssignmentPosition).2

theorem CubeRootedActiveDebtFusionCarrier.rootAuxiliary_mem
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    carrier.rootAuxiliary ∈ cubeInwardMateActiveStretchedFusionWitnesses
      K physical hK hbounded (cubeDebtRootIncidence carrier.word) := by
  exact carrier.rooted.root_mem

/-- A nonempty active stretched fiber proves that both incident source faces
at its root carry at least one physical strand. -/
theorem CubeRootedActiveDebtFusionCarrier.root_faces_positive
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    0 < physical
        (centralLowerCubeFaceId (cubeDebtRootIncidence carrier.word).1.left) ∧
      0 < physical
        (centralLowerCubeFaceId (cubeDebtRootIncidence carrier.word).1.right) := by
  have hmem := carrier.rootAuxiliary_mem
  unfold cubeInwardMateActiveStretchedFusionWitnesses at hmem
  by_cases hpositive :
      0 < physical
          (centralLowerCubeFaceId (cubeDebtRootIncidence carrier.word).1.left) ∧
        0 < physical
          (centralLowerCubeFaceId (cubeDebtRootIncidence carrier.word).1.right)
  · exact hpositive
  · simp [hpositive] at hmem

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.choiceFiberAssignment_firstTrue_get_mem_debt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.cubeRootedActiveDebtFusionCarriers_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.CubeRootedActiveDebtFusionCarrier.rootAuxiliary_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.CubeRootedActiveDebtFusionCarrier.root_faces_positive
